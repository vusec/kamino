module D = Debug.Make(struct let name = "Function" and default=`Debug end)
open D

module X86 =
struct
  let find_exit_nodes ast_cfg =
    Cfg.AST.G.fold_vertex (fun v acc ->
        match Cfg.AST.G.out_degree ast_cfg v with
        | 0 -> v :: acc
        | _ -> acc) ast_cfg []


  let has_prolog ast_cfg =
    let  (_, entry) =  Cfg_ast.find_entry ast_cfg in
    let stmts = Cfg.AST.get_stmts ast_cfg entry in
    (* We use the x86 assembly available in comments to detect the prolog because the
       IL instructions for saving the callers stackframe can vary depending on transformation applied
       (e.g., memory2array splits the store into byte sized chunks.
       This approach should be more stable and less transformation sensitive.
    *)
    let labels  = List.filter (function
        | Ast.Label (_, attributes) -> List.exists (function
            | Type.Asm _ -> true
            | _ -> false) attributes
        | _ -> false) stmts in
    let prolog = List.map (function
        (* XXX: This doesn't work when more attributes are added! *)
        | Ast.Label (_, [Type.Asm asm]) -> asm
        | _ -> failwith "Expected a label with an asm statement!"
      ) (BatList.take 3 labels) in
    let expected_prolog = [Str.regexp "^push[^%]+%ebp$"; Str.regexp "^mov[^%]+%esp,%ebp$";
                           Str.regexp "^sub[^\\$]+\\$0x[0-9a-fA-F]+,%esp$"] in
    try
      List.fold_left2 (fun acc s s' ->
          (Str.string_match s' s 0) && acc) true prolog expected_prolog
    with Invalid_argument _ ->
      dprintf "Function prologue is too short!";
      false

  let has_epilog ast_cfg =
    let exit_nodes = find_exit_nodes ast_cfg
    in
    match exit_nodes with
    | [n] -> List.exists (function
        (* XXX: This assumes only one attributes! *)
        | Ast.Label (_, [Type.Asm asm]) ->
          (* XXX: This doesn't consider mov %ebp,%esp  pop %ebp  ret sequence!*)
          Str.string_match (Str.regexp "^leave[ ]+$") asm 0
        | _ -> false) (Cfg.AST.get_stmts ast_cfg n)
    | [] -> failwith "Unable to find exit node in CFG!"
    | _ :: _ -> failwith "Multiple exit nodes is not supported!"

  exception Invalid_stack_height
  exception Unknown_stack_height of string
  exception Irreducible_expression

  type requested_addr = ReqAddr of Type.addr | ReqBBEnd
  module Hashable_addr = struct
    type t = Type.addr
    let equal ra1 ra2 = ra1 = ra2
    let hash = Hashtbl.hash
  end
  let raddr_to_str = function
    | ReqBBEnd -> "BBEnd"
    | ReqAddr addr -> Printf.sprintf "%#Lx" addr

  let addr_is_requested raddrs addr =
    List.exists (function
    | ReqAddr raddr when raddr = addr -> true
    | _ -> false) raddrs

  module L =
  struct
    (*
     * This is a remainder of the GraphDataflow approach. Pointless now
     * (should use Option everywhere) but too much of a hassle to remove ATM.
     *)
    type stack_height = Height of int | Unknown
    let to_string = function
      | Height h -> Printf.sprintf "%d" h
      | Unknown -> "unknown"
  end

  let do_stack_height_at_addrs stmts height requested_addrs =
    (*
     * See if a variable has been defined as a constant (i.e. we can handle
     * t = 7; esp = esp + t as well as p = 6; q = p; esp = esp + q). Handling
     * stuff like p = 6; q = p + 7; esp = esp + q would also be simple but
     * hopefully no compiler generates that, so we can ignore it for now.
     * This seriously needs some VSA love anyway (TBD, XXX).
     *)
    let get_constant_def rstmts var =
      let rec inner to_resolve stmts =
        match stmts with
        | [] -> None
        | s :: rest ->
          (match s with
          | Ast.Move (lvar, exp, [])
              when Var.equal to_resolve lvar ->
            (match exp with
            | Ast.Int (bi, _) ->
              Some (Big_int_Z.int_of_big_int bi)
            | Ast.Var nvar ->
                (* track copies *)
              inner nvar rest
            | _ ->
              raise Irreducible_expression)
          | _ -> inner to_resolve rest)
      in
      inner var rstmts
    in
    let solve_binop_for_const const = function
      | Type.PLUS -> const
      | Type.MINUS -> - const
        (* XXX: need a bright idea for esp &= ~0xf *)
      | _ -> raise Irreducible_expression
    in
    let do_plusminus rstmts operator operand =
      match operand with
      | Ast.Int (constant, _) ->
        let constant = Big_int_Z.int_of_big_int constant in
        solve_binop_for_const constant operator
      | Ast.Var var ->
        (match get_constant_def rstmts var with
        | None -> raise Irreducible_expression
        | Some c -> solve_binop_for_const c operator)
      | _ ->
        raise Irreducible_expression
    in
    let response = BatHashtbl.create (List.length requested_addrs) in
    let last_addr, adj, _, response = List.fold_left (fun (curr_addr, adj, rstmts, acc) stmt ->
        (* Walk the statements *)
      dprintf "do_stack_height_at_addrs: folding %s (adj = %s)"
        (BatOption.map_default (Printf.sprintf "%#Lx")  "unavailable" curr_addr)
        (BatOption.map_default (Printf.sprintf "%d") "lost_track" adj);

      let naddr, nadj, nacc = (match stmt with
        | Ast.Label (Type.Addr addr, _) ->
            (*
             * Note: addr can be None (if we're in a rep loop, the BB with
             * the body statements won't have an Ast.Label; hopefully
             * there won't be any interesting instructions there...
             *)
          let nacc = (match curr_addr with
            | None -> acc
            | Some curr_addr ->
              dprintf "Label: %#Lx"  curr_addr;
              (* Return the stack height /after/ the requested address *)
              if addr_is_requested requested_addrs curr_addr then begin
                let res = (match adj with
                | Some adj ->
                  let new_height = height + adj in
                  L.Height new_height
                | None ->
                  (* We've lost track of the stack height *)
                  L.Unknown)
                in
                dprintf "Adding height %s for requested addr %#Lx"
                  (L.to_string res) curr_addr;
                BatHashtbl.add acc (ReqAddr curr_addr) res;
                acc
              end else begin
                acc
              end
          )
          in
          (Some addr, adj, nacc)
        | Ast.Move (lvar, exp, _) when Karch.X86.is_stack_reg lvar ->
          (try
               (* Look at adjustments of esp *)
             (match exp with
             | Ast.BinOp (op, Ast.Var var, other)
             | Ast.BinOp (op, other, Ast.Var var)
                 when Karch.X86.is_stack_reg var ->
                 (*
                  * If we were able to express this adjustment as +/- constant,
                  * add it to the total adjustment effected by these stmts.
                  *)
               let adj_post_stmt = (match adj with
                 | Some adj ->
                   let diff = do_plusminus rstmts op other in
                   Some (adj + diff)
                 | None ->
                   None)
               in
               (curr_addr, adj_post_stmt, acc)
             | Ast.Var other ->
               (* XXX, TBD: temporary. happens for init, __libc_csu_fini (in .init) *)
               raise Irreducible_expression;
             | _ ->
               raise Irreducible_expression)
           with Irreducible_expression as e ->
             dprintf "Irreducible expression %s" (Pp.ast_exp_to_string exp);
             (curr_addr, None, acc))
        | _ -> (curr_addr, adj, acc))
                               in
                              let curr_addr = match naddr with
                                | Some _ -> naddr
                                | None -> curr_addr
                              in
        (*
         * Maintain a reverse list of previous statements; it's used
         * to do trivial resolution of constants (see above).
         *)
                              (curr_addr, nadj, stmt :: rstmts, nacc))
        (None, Some 0, [], response) stmts
      in
      let final_height = match adj with
        | Some adj -> L.Height (height + adj)
        | None -> L.Unknown
      in
      dprintf "Calculated new height %s given %d" (L.to_string final_height)
        height;
      BatHashtbl.add response ReqBBEnd final_height;
      ignore(match last_addr with
      | None ->
        ()
      | Some last_addr ->
        if addr_is_requested requested_addrs last_addr then
          BatHashtbl.add response (ReqAddr last_addr) final_height);
        (* Did we resolve them all? *)
      List.iter (fun raddr ->
        try
          ignore(BatHashtbl.find response raddr)
        with Not_found ->
          dprintf "No stackheight for requested address %s"
            (raddr_to_str raddr)) requested_addrs;
      Misc.bathashtbl_find_option response

  let stack_height_at_addrs stmts h_in requested_addrs =
    match h_in with
    | L.Height height ->
      do_stack_height_at_addrs stmts height requested_addrs
    | L.Unknown ->
      (* All is unknown *)
      let resp = BatHashtbl.create (List.length requested_addrs) in
      let resp = List.fold_left (fun acc raddr ->
        BatHashtbl.add acc raddr L.Unknown;
        acc
      ) resp requested_addrs
      in
      Misc.bathashtbl_find_option resp

  (* Calculate the (+/- constant) adjustment to esp in this BB *)
  let stack_adj_for_bb cfg v =
    let h_in_zero = L.Height 0 in
    (* Get the statements of the BB *)
    let stmts = Cfg.AST.get_stmts cfg v in
    try
      let height_at = stack_height_at_addrs stmts h_in_zero [ReqBBEnd] in
      match height_at ReqBBEnd with
      | None ->
        failwith "ReqBBEnd missing"
      | Some h -> h
    with Irreducible_expression ->
      L.Unknown

  let compute_bb_stack_heights_out ast_cfg =
    let stack_adjustments = BatHashtbl.create (Cfg.AST.G.nb_vertex ast_cfg) in
    let stack_adj_for_bb v =
      match Misc.bathashtbl_find_option stack_adjustments v with
      | Some ret -> ret
      | None ->
        let ret = stack_adj_for_bb ast_cfg v in
        BatHashtbl.add stack_adjustments v ret;
        ret
    in
    (*
     * This needs to be a local module because Analysis.analyze needs
     * access to the cfg.
     *)
    let module Analysis =
    struct
      module C = Cfg.AST
      type vertex = C.G.V.t
      type edge = C.G.E.t
      type g = C.G.t
      type data = L.stack_height
      let direction = Fixpoint.Forward
      let equal = (=)
      let join a b =
        let ret = match a, b with
          | L.Height h1, L.Height h2
            when h1 = h2 ->
            L.Height h1
          (*
           * If two incoming heights differ, the result is indeterminate
           *)
          | L.Height _, L.Height _ ->
            L.Unknown
          | _ ->
            L.Unknown
        in
        dprintf "join %s %s -> %s" (L.to_string a) (L.to_string b)
          (L.to_string ret);
        ret


      (*
       * This function gets as argument an edge and the current
       * OUT of the source vertex. It returns the new OUT of
       * the destination vertex.
       * This implementation is bloody stupid, we should just precalculate
       * the stack adjustments and not walk the statements every time
       * through.
       * XXX: This might very well not terminate if esp is ever adjusted
       * in the body of a loop, haven't tested that case.
       *)
      let analyze e h_in =
        let e2s e =
          let lab = C.G.E.label e in
          let src, dst = (C.G.E.src e, C.G.E.dst e) in
          Printf.sprintf "%s -> %s" (C.v2s src) (C.v2s dst)
        in
        dprintf "analyze %s (h_in: %s)" (e2s e) (L.to_string h_in);
        let v = C.G.E.dst e in
        match h_in with
        | L.Unknown -> L.Unknown
        | L.Height h1 ->
          begin
            match stack_adj_for_bb v with
            | L.Unknown -> L.Unknown
            | L.Height h2 ->
              L.Height (h1 + h2)
          end
    end
    in

    let initial v =
      match Cfg.BB_Entry = Cfg.AST.G.V.label v with
      | true ->
        let stmts = Cfg.AST.get_stmts ast_cfg v in
        let resp = stack_height_at_addrs stmts (L.Height 0) [ReqBBEnd] in
        (match resp ReqBBEnd with
        | Some h -> h
        | None -> L.Unknown)
      | false -> L.Unknown
    in
    let module FP = Fixpoint.Make(Cfg.AST.G)(Analysis) in
    (fun v ->
      match FP.analyze initial ast_cfg v with
      | L.Unknown -> None
      | L.Height h -> Some h)

  let compute_bb_stack_heights_in ast_cfg bb_out v =
    let preds = Cfg.AST.G.pred ast_cfg v in
    match preds with
    | [] ->
      Some 0 (* Entry node *)
    | pred :: rest ->
      let first_h = bb_out pred in
      List.fold_left (fun h p ->
        let h' = bb_out p in
        match h, h' with
        | Some h, Some h' when h = h' -> Some h
        | Some _, Some _ -> None
        | Some _, None
        | None, Some _
        | None, None -> None) first_h rest

  let compute_bb_stack_heights ast_cfg =
    let bbh_out = compute_bb_stack_heights_out ast_cfg in
    let bbh_in = compute_bb_stack_heights_in ast_cfg bbh_out in
    (bbh_in, bbh_out)

  let compute_stack_height ast_cfg =
    let bb_out_stackheight = snd (compute_bb_stack_heights ast_cfg) in
    let exit_nodes = find_exit_nodes ast_cfg in
    let exit_nodes_height = List.map bb_out_stackheight exit_nodes in
    let heights = List.fold_left (fun (acc) -> function
        | Some h ->
          (* If f is well-behaved the data-flow equation for exit nodes is
             IN(B) = OUT(B') - addrsz.
             The substraction of addrsz is ommitted, so we have to check against > addrsz
             instead of > 0 ) *)
          if h > 4 then
            raise Invalid_stack_height
          else
            h :: acc
        | None ->
          raise (Unknown_stack_height "No height at exit node"))
      [] exit_nodes_height
    in
    match heights with
    | [] ->
      (*
       * TBD: this happens at least when there's a call to a noreturn function
       * that we haven't identified (e.g. bsdtar's long_help() which calls out
       * to the noreturn version(). We need to be propagating the no-return
       * attribute to callers, but we can't do that in the general case and
       * the compiler can be smarter than we can ever hope to be. So we
       * have to be able to bail here in any case.
       *)
      wprintf "No exit nodes!";
      raise (Unknown_stack_height "No exit nodes!")
    | h :: rest ->
      List.iter (fun r ->
        if r <> h then begin
          let str = Printf.sprintf "Exit stack heights differ: %d vs %d" r h in
          raise (Unknown_stack_height str)
        end) rest;
      h

  let height_to_str = function
    | None -> "unknown"
    | Some h -> Printf.sprintf "%d" h

  (* XXX: this performs poorly *)
  let bb_filter_addrs stmts addrs =
    let bb_has_addr addr =
      try
        ignore(List.find (fun s ->
          match Bb.stmt_get_addr s with
          | None -> false
          | Some stmt_addr -> stmt_addr = addr) stmts);
        true
      with Not_found -> false
    in
    List.filter bb_has_addr addrs

  let calc_stack_height_at_addrs ast_cfg addrs =
    let bb_in_stackheight = fst (compute_bb_stack_heights ast_cfg) in
    let module AddrHtbl = BatHashtbl.Make(Hashable_addr) in
    let htbl = AddrHtbl.create (List.length addrs) in
    dprintf "calc_stack_height_at_addrs:";
    List.iter (fun addr ->
      dprintf "addr: %#Lx" addr) addrs;
    let htbl = Cfg.AST.G.fold_vertex (fun v acc ->
      let stmts = Cfg.AST.get_stmts ast_cfg v in
      let bbaddrs = bb_filter_addrs stmts addrs in
      let bbraddrs = List.map (fun addr -> ReqAddr addr) bbaddrs in
      if (List.length bbraddrs) > 0 then begin
        let in_h = bb_in_stackheight v in
        dprintf "in_h(%s) = %s" (Cfg.AST.v2s v) (height_to_str in_h);
        let opt2h o = match o with
          | Some h -> L.Height h
          | None -> L.Unknown
        in
        let height_at = stack_height_at_addrs stmts (opt2h in_h) bbraddrs in
        List.fold_left (fun acc addr ->
          match height_at (ReqAddr addr) with
          | None ->
            dprintf "Couldn't get stack height at %#Lx" addr;
            (*
             * Either we couldn't track ESP (in which case we should have raised
             * Irreducible_expression and never have gotten here) or we
             * mixed up the addresses that we were supposed to resolve...
             *)
            failwith "Didn't calculate stack height at requested addr"
          | Some h ->
            (match h with
            | L.Height h ->
              AddrHtbl.add acc addr (Some h);
              acc
            | L.Unknown ->
              AddrHtbl.add acc addr None;
              acc)) acc bbaddrs
      end else begin
        htbl
      end
    ) ast_cfg htbl in
    AddrHtbl.find_option htbl

  let is_well_behaved descr ast_cfg =
    (*
     * Perhaps we can use this as a heuristic ("if the function has a standard
     * prologue and epilogue, assume it treats the stack pointer nicely too")
     * when we can't track stack pointer adjustments, but we want to default
     * to being conservative for now. Besides, the prologue and epilogue often
     * get omitted even at -O1 with gcc, so...
     *)
(*
    let by_prolog_and_epilog = (has_prolog ast_cfg) && (has_epilog ast_cfg) in
*)
    let by_prolog_and_epilog = true in
    try
      (* XXX: For debugging purposes we do not short-circuit the stack height computation. *)
      let stack_height = compute_stack_height ast_cfg in
      (* Well-behaving functions restore the stack height to 0, but the return hacks also
         pops the return address explicitly *)
      let by_stack_height = stack_height = 4 in
      dprintf "Computed the stack height for %s: %d" descr stack_height;
      by_prolog_and_epilog || by_stack_height
    with e -> match e with
      | Unknown_stack_height reason ->
        dprintf "Computed the stack height for %s: bottom (%s)" descr reason;
        false
      | Invalid_stack_height ->
        dprintf "Computed the stack height for %s: invalid!" descr;
        false
      | _ -> raise e

  exception Irreducible_kill_depth
  type kill_descr = {basereg : Var.t option; region : Interval.Address_interval.t}
  type kill_depth = Kill of kill_descr | Infinite

  (*
   * We depend on a separate pass (rewrite-stack-loadstores) to already have
   * assigned arrays to stores, which are named after the base pointer, and
   * to have determined the bounds of such arrays.
   *
   * Note: we need this information in order to be able to properly summarize
   * function calls, so that we can properly convert to SSA form. So this
   * means we're "forking" the pipeline, INCORRECTLY converting to SSA and
   * running the rewrite-stack-loadstores pass, so that we can compute the
   * function summaries. Then, we summarize and do the SSA conversion for real.
   * This is broken for everything other than ESP-based stuff which we assume
   * is stable after a call (this is handled specially by emitting code to
   * adjust the esp value, to account for the fact that the pushing of the
   * ret address is visible in the parent, but the return is not).
   *)
  (*
   * Given this *incorrect* SSA CFG, provide information (if possible) for
   * the loads in the function. This information is only accurate for
   * ESP-based loads and loads from globals, but this is all our caller
   * needs for now.
   *
   * XXX: DANGER DANGER: While we track stuff that's using ESP directly
   * or through a copy, it is very much possible for us to lose track
   * of a pointer derived from ESP. E.g. if it's saved to the stack then
   * reloaded or if it's masked, etc. At the very least we should notice
   * when this happens and declare the function confusing or something.
   * Currently, we're being optimistic in assuming that no compiler would
   * do that :P
   *)
  let compute_load_info ssa_cfg =
    let conv_interval bi =
      let b = Interval.Big_int.begin_ bi in
      let e = Interval.Big_int.end_ bi in
      match (b, e) with
      | None, None ->
        (* Empty *)
        Interval.Address_interval.create (Int64.of_int 1) (Int64.of_int 0)
      | Some b, Some e ->
        Interval.Address_interval.create
          (Big_int_Z.int64_of_big_int b)
          (Big_int_Z.int64_of_big_int e)
      | _ ->
        let str = Printf.sprintf "One-sided bounds!" in
        failwith str
    in
    let load_for_ary arr =
      let var_of_val = function
        | Ssa.Int _
        | Ssa.Lab _ -> failwith "Can't happen (Ssa.Lab)"
        | Ssa.Var var -> var
      in
      let arrv = var_of_val arr in
      let module VcArray = Var_convenience.Array in
      if VcArray.is_array arrv then begin
        let breg = VcArray.base_reg arrv in
        let bounds = VcArray.bounds arrv in
        let bounds = conv_interval bounds in
        if Karch.X86.is_stack_reg breg then begin
          Some {
            basereg = Some breg;
            (*
             * Note: here we depend on the overlap calculations we did to
             * create these arrays. The width of the store could be narrower
             * than the width of the array.
             *)
            region = bounds;
          }
        end else if VcArray.is_global_ary arrv then begin
          Some {
            basereg = None;
            region = bounds;
          }
        end else begin
          (*
           * If it's not a global and it's not a store through ESP,
           * then it's a store through an arbitrary pointer. For
           * all we know it points at any stack or heap location...
           *)
          None
        end
      end else begin
        (*
         * If the arrayfication pass hasn't beeen able to assign an array
         * for this load, it probably means it was a pointer loaded through
         * a pointer or a pointer derived through another pointer via
         * some operation that we can't really track (e.g. p + nonconst or
         * p & mask). Regardless, we simply can't provide any accurate
         * information for this load.
         *)
        None
      end
    in
    let loads = BatHashtbl.create 10 in
    let find_loads_for_bb bb =
      let load_offset = ref 0 in
      let visitor = object
        inherit Ssa_visitor.nop
        method visit_exp = function
        | Ssa.Load(arr, idx, edn, typ) ->
          let bbid = (Cfg.SSA.G.V.label bb) in
          ignore(match load_for_ary arr with
          | Some k ->
            BatHashtbl.add loads (bbid, !load_offset) (Some k);
            load_offset := !load_offset + 1
          | None ->
            BatHashtbl.add loads (bbid, !load_offset) None;
          );
          Type.SkipChildren
        | _ ->
          Type.SkipChildren

        method visit_stmt = function
        | Ssa.Move (var, exp, _) -> Type.DoChildren
        | _ -> Type.SkipChildren
      end
      in
      let stmts =
        try
          Cfg.SSA.get_stmts ssa_cfg bb
        with Not_found -> failwith "Couldn't get stmts for BB"
      in
      ignore(Ssa_visitor.stmts_accept visitor stmts)
    in
    Cfg.SSA.G.iter_vertex find_loads_for_bb ssa_cfg;
    Misc.bathashtbl_find_option loads
end
