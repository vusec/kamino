module D = Debug.Make(struct let name = "Analysis_pass" and default=`Debug end)
open D

open Crappy_vsa
open Ktype.Exceptions
open Misc.Pervasives

module VH = Var.VarHash
module VarMap = Var.VarMap

type pipeline_ctx = {
  arch : Asmir.arch;
  function_information: Function_info.t list;
  info : Ktype.analysis_pass_result list;
  idx : int;
}

type ('a,'b) action =
  | Transform of < transform: pipeline_ctx -> 'a -> 'a; name: string >
  | Analysis of < analyze: pipeline_ctx -> 'a -> pipeline_ctx; name: string >

type 'a configuration =
  | Ast of (Ast.program, 'a) action
  | AstCfg of (Cfg.AST.G.t, 'a) action
  | Ssa of (Ssa.stmt list, 'a) action
  | SsaCfg of (Cfg.SSA.G.t, 'a) action

type 'a pass = Pass of 'a configuration

let default_pipeline_ctx = {
  arch = Asmir.arch_i386;
  function_information = [];
  info = [];
  idx = 0;
}

let get_callinfo ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `Callinfo ci -> Some ci
        | _ -> None) ctx.info
  with Not_found ->
    failwith "No callinfo"

let get_retinfo ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `Retinfo x -> Some x
        | _ -> None) ctx.info
  with Not_found ->
    failwith "No retinfo"

let get_hltinfo ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `Hltinfo x -> Some x
        | _ -> None) ctx.info
  with Not_found ->
    failwith "No hltinfo"

let get_addrmap ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `Addrmap x -> Some x
        | _ -> None) ctx.info
  with Not_found ->
    failwith "Need to have an addrmap"

let get_data_dependencies ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `DataDependencies dd -> Some dd
        | _ -> None) ctx.info
  with Not_found ->
    failwith "Expected data dependencies to be available!"

let get_function_inputs ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `Inputs inputs -> Some inputs
        | _ -> None) ctx.info
  with Not_found ->
    failwith "Expected function inputs to be available!"

let get_mem_accesses ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `MemAccesses acc -> Some acc
        | _ -> None) ctx.info
  with Not_found ->
    failwith "Expected mem accesses to be available!"

let get_collapsible_loads ctx =
  try
    BatList.find_map (fun el ->
        match el with
        | `CollapsibleLoads l -> Some l
        | _ -> None) ctx.info
  with Not_found ->
    failwith "Expected stack accesses to be available!"

let set_callinfo ctx callinfo = {ctx with info = (`Callinfo callinfo) :: ctx.info}
let set_retinfo ctx retinfo = {ctx with info = (`Retinfo retinfo) :: ctx.info}
let set_hltinfo ctx hltinfo = {ctx with info = (`Hltinfo hltinfo) :: ctx.info}
let set_addrmap ctx addrmap = {ctx with info = (`Addrmap addrmap) :: ctx.info}
let set_function_inputs ctx inputs = {ctx with info = (`Inputs inputs) :: ctx.info}
let set_data_dependencies ctx dd = {ctx with info = (`DataDependencies dd) :: ctx.info}
let set_mem_accesses ctx acc = {ctx with info = (`MemAccesses acc) :: ctx.info}
let set_collapsible_loads ctx l = {ctx with info = (`CollapsibleLoads l) :: ctx.info}

let callinfo_of_calls =
  List.fold_left (fun ci ct ->
      Callinfo.add ci ct) Callinfo.empty

let last_call callinfo addrtest =
  let cts = Callinfo.filter_by_site addrtest callinfo in
  let cts = List.sort (fun a b ->
      (* Get the highest addr first *)
      - (Callgraph.cmp_by_call_site a b)) cts
  in
  match cts with
  | [] -> None
  | last :: _ -> Some last

let get_function_info ctx addr =
  try
    assert((List.length ctx.function_information) > 0);
    let info = List.find (fun fi ->
        match Function_info.begin_address fi with
        | Some funcaddr ->
          0 = (Int64.compare funcaddr addr)
        | None ->
          (* Ignore and hope the address is for a function we *do* know about *)
          false
      )
        ctx.function_information
    in
    Some info
  with Not_found -> None

let addrlist_to_str =
  Print.list_to_string ~enclosing:("(", ")") (Printf.sprintf "%#Lx")


module Ast_passes =
struct
  let start =
    object
      method name = "start"
      method transform _ stmts = stmts
    end

  let verify_no_calls =
    object
      method name = "verify-no-calls"
      method analyze ctx stmts =
        List.iter (fun stmt ->
            match Misc.is_call ctx.arch stmt with
            | true -> raise (Confusing_function "has calls")
            | false -> ()) stmts;
        ctx
    end

  let collect_calls =
    object
      method name = "collect-calls"
      method analyze ctx stmts =
        assert((List.length ctx.function_information) = 1);
        let current_func = List.hd (ctx.function_information) in
        let _, ret_addrs, hlt_addrs = List.fold_left (fun (addr, rets, hlts) s ->
            match s with
            | Ast.Label (Type.Addr addr, _) ->
              (Some addr, rets, hlts)
            | Ast.Halt _ ->
              (match addr with
               | Some addr ->
                 dprintf "got halt at %#Lx" addr;
                 (Some addr, rets, addr :: hlts)
               | None ->
                 failwith "No addr for hlt statement")
            | _ ->
              if Misc.is_ret ctx.arch s then
                (match addr with
                 | Some addr ->
                   (Some addr, addr :: rets, hlts)
                 | None ->
                   failwith "No addr for ret statement")
              else if Ast.is_indirectjump s then begin
                let str = Pp.ast_stmt_to_string s in
                dprintf "Indirect jump: %s" str;
                let reason = Printf.sprintf "%s has an indirect jump"
                    (Function_info.symbols_to_str current_func) in
                raise (Confusing_function reason)
              end else
                (addr, rets, hlts)) (None, [], []) stmts
        in
        (* XXX: need to also throw a fit in case of indirect jumps! *)
        let indirect = BatList.Exceptionless.find (fun ct -> match ct with
            | Callgraph.IndirectCall _ -> true
            | Callgraph.DirectCall _ -> false)
        in
        let ci = Callgraph.call_targets stmts in
        ignore(
          try
            (match indirect ci with
             | Some (Callgraph.IndirectCall addr) ->
               let str = Printf.sprintf "has indirect call (%#Lx)" addr in
               raise (Confusing_function str);
             | _ -> ())
          with Match_failure _ -> ()
        );
        let ctx = set_callinfo ctx (callinfo_of_calls ci) in
        let ctx = set_retinfo ctx ret_addrs in
        set_hltinfo ctx hlt_addrs
    end

  let replace_call_stmts =
    object
      method name = "replace-call-stmts"
      method transform ctx stmts =
        List.map (fun stmt ->
            match Misc.is_call ctx.arch stmt with
            | true ->
              let esp = List.find (fun v -> Var.name v = "R_ESP") (Asmir.decls_for_arch ctx.arch) in
              Ast.Move(esp, Ast.BinOp (Type.PLUS, Ast.Var esp,
                                       Ast.Int (Big_int_Z.big_int_of_int 4, Type.Reg 32)),
                       [Type.StrAttr "esp_readjustment"])
            | false -> stmt ) stmts
    end

  (** The pass removes halt statements from AST form, because there are no
      semantics for HALT statements in SSA form. *)
  let remove_halt_stmts =
    object
      method name = "remove-hlt-stmts"
      method transform ctx = List.filter(fun stmt ->
          match stmt with
          | Ast.Halt _ -> false
          | _ -> true)
    end

  let remove_special_stmts =
    object
      method name = "remove-special-stmts"
      method transform ctx = List.filter (fun stmt ->
          match stmt with
          | Ast.Special _ -> false
          | _ -> true)
    end

  let coerce_prog =
    let open BatPervasives in
    object
      method name = "memory-to-array"
      method transform ctx = Memory2array.coerce_prog |- Flatten_mem.flatten_mem_program
    end

end

module Astcfg_passes =
struct
  module C = Cfg.AST
  module G = C.G

  let remove_indirect =
    object
      method name = "remove-indirect"
      method transform _ cfg =
        let cfg = Hacks.ast_remove_indirect cfg in
        try
          let bberr = Cfg.AST.find_vertex cfg Cfg.BB_Error in
          match Cfg.AST.G.in_degree cfg bberr with
          | 0 -> Cfg.AST.remove_vertex cfg bberr
          | _ -> raise (Confusing_function "has BB_Error")
        with Not_found -> cfg
    end

  let do_prune_unreachable _ cfg =
    try
      Prune_unreachable.prune_unreachable_ast cfg
    with Invalid_argument str ->
      let str = Printf.sprintf "prune_unreachable: %s" str in
      raise (Confusing_function str)

  let prune_unreachable1 =
    object
      method name = "prune-unreachable1"
      method transform = do_prune_unreachable
    end

  let prune_unreachable2 =
    object
      method name = "prune-unreachable2"
      method transform = do_prune_unreachable
    end

  let force_single_exit =
    let open BatPervasives in
    let fallthrough_edge_to_bb ~dst cfg src =
      let e = G.E.create src None dst in
      C.add_edge_e cfg e
    in
    let trim_merged_tails cfg bbs n_trimmed =
      List.fold_left (fun cfg bb ->
          let stmts = C.get_stmts cfg bb in
          let len = List.length stmts in
          assert (len >= n_trimmed);
          let stmts = BatList.take (len - n_trimmed) stmts in
          C.set_stmts cfg bb stmts) cfg bbs
    in
    let doit cfg exit_bbs =
      let rev_stmts = List.map (fun bb -> C.get_stmts cfg bb |> List.rev) exit_bbs in
      (* Note: this will declare any two labels to be equal. This is exactly what
       * we want as we need to preserve at least one address label of the return
       * instructions we might merge.
      *)
      let stmts_eq s1 s2 = match Misc.ast_stmts_eq s1 s2 with
        | BatResult.Ok () -> true
        | BatResult.Bad _ -> false
      in
      let common_tail = Misc.longest_common_prefix_n stmts_eq rev_stmts |>
                        List.rev
      in
      let cfg, single_exit = C.create_vertex cfg common_tail in
      let cfg = List.fold_left (fallthrough_edge_to_bb ~dst:single_exit) cfg exit_bbs in
      trim_merged_tails cfg exit_bbs (List.length common_tail)
    in
    object
      method name = "force-single-exit"
      method transform _ cfg =
        match Cfg_convenience.AST.get_exit_bbs cfg with
        | []
        | [_] -> cfg
        | exit_bbs -> doit cfg exit_bbs
    end
  let do_coalesce ctx cfg =
    let callinfo = get_callinfo ctx in
    let module AST' = struct
      include Cfg.AST
      let remove_redundant_jump p =
        match List.rev p with
        | Ast.Jmp (e, _) as s::tl  when Ast.lab_of_exp e <> None ->
          let str = "Removed redundant jump: " ^ (Pp.ast_stmt_to_string s) in
          let rs = Ast.Comment(str, []) in
          List.rev (rs::tl)
        | _ -> p
      let is_safe_to_coalesce p =
        let is_safe_to_coalesce_stmt = function
          | Ast.Comment _
          | Ast.Label _ -> true
          | _ -> false
        in
        match Bb.get_bbbounds_from_ast p with
        | Some (_, last) when Callinfo.call_at_addr callinfo last <> None ->
              (*
               * We want to preserve breaks after call sites, so that we
               * can take calls into account when comparing BBs.
               *)
          dprintf "Refusing to coalesce because of call at %#Lx" last;
          false
        | Some (first, last) ->
          dprintf "CallCoalesceProt: (%#Lx, %#Lx)" first last;
          let p = remove_redundant_jump p in
          List.for_all is_safe_to_coalesce_stmt p
        | _ ->
          let p = remove_redundant_jump p in
          List.for_all is_safe_to_coalesce_stmt p
    end in
    let module Coalesce = Coalesce.MakeCoalesce(AST') in
    Coalesce.coalesce cfg

  let coalesce_ast1 =
    object
      method name = "coalesce-ast1"
      method transform = do_coalesce
    end

  let coalesce_ast2 =
    object
      method name = "coalesce-ast2"
      method transform = do_coalesce
    end

  let coalesce_ast3 =
    object
      method name = "coalesce-ast3"
      method transform = do_coalesce
    end

  let subreg_liveness =
    let module D = Debug.Make(struct
        let name = "Subreg_liveness" and default=`Debug
      end) in
    let open D in

    let open BatPervasives in

    let exp_bits = Track_exp_bits.exp_bits in
    let exp_pad bits e =
      let obits = exp_bits e in
      if  obits >= bits then begin
        let s = Printf.sprintf "Tried to pad to <= type (%d -> %d)"
            obits bits in
        failwith s
      end;
      Ast.Cast (Type.CAST_UNSIGNED, Type.Reg bits, e)
    in
    let exp_cast_low bits e =
      let obits = exp_bits e in
      if  obits <= bits then begin
        let s = Printf.sprintf "Tried to exp_cast_low to >= type (%d -> %d)"
            obits bits in
        failwith s
      end;
      Ast.Cast (Type.CAST_LOW, Type.Reg bits, e)
    in
    let rec push_low bits exp =
      match exp with
      | Ast.Load _
      | Ast.Store _ ->
        exp_cast_low bits exp
      | Ast.BinOp (op, e1, e2)
          when op = Type.AND || op = Type.OR || op = Type.XOR ->
        Ast.BinOp (op, push_low bits e1, push_low bits e2)
      | Ast.BinOp _ ->
        exp_cast_low bits exp
      | Ast.UnOp (op, e) ->
        (* Both unary operators are bitwise *)
        Ast.UnOp (op, push_low bits e)
      | Ast.Var var ->
        exp_cast_low bits exp
      | Ast.Lab _ ->
        failwith "push_low on Ast.Lab"
      | Ast.Unknown _ ->
        failwith "push_low on Ast.Unknown"
      | Ast.Int (bi_, _) ->
        let open Big_int_convenience in
        Ast.Int (bi_ &% ((bi1 <<% bits) -% bi1), Type.Reg bits)
      | Ast.Cast _ ->
        exp_cast_low bits exp
      | Ast.Let _ ->
        failwith "push_low on Ast.Let"
      | Ast.Ite _ ->
        exp_cast_low bits exp
      | Ast.Extract _ ->
        exp_cast_low bits exp
      | Ast.Concat (e1, e2) ->
        let bits_low = exp_bits e2 in
        if bits = bits_low then begin
          e2
        end else if bits < bits_low then begin
            exp_cast_low bits e2
        end else begin
          exp_cast_low bits exp
        end
    in
    let apply_trim stmt bits =
      match stmt with
      | Ast.Move (avar, e, attrs) when bits > 0->
        let e = exp_pad (Var.typ avar |> Typecheck.bits_of_width) (push_low bits e) in
        Ast.Move (avar, e, attrs)
      | Ast.Move (avar, _, attrs) ->
        Ast.Comment (Printf.sprintf "elided unused assignment to %s" (Pp.var_to_string avar),
                     Type.Synthetic :: attrs)
      | _ ->
        failwith "Tried to apply_trim to non-Move"
    in
    let apply_trims stmts trims =
      let stmts = Array.of_list stmts in
      List.iter (fun (stmt_off, bits) ->
          stmts.(stmt_off) <- apply_trim stmts.(stmt_off) bits) trims;
      Array.to_list stmts
    in
    let map_to_s map =
      VarMap.fold (fun v _ acc -> v :: acc) map [] |>
      Print.list_to_string ~enclosing:("", "") ~sep:", " Pp.var_to_string
    in
    let maybe_trim (map: BatISet.t VarMap.t) defs to_be_trimmed avar =
      try
        begin
          let bits = VarMap.find avar map in
          let used_low_bits =
            if BatISet.is_empty bits then 0 else (BatISet.max_elt bits) + 1
          in
          try
            begin
              if used_low_bits < (Var.typ avar |> Typecheck.bits_of_width) then begin
                let stmt_off = VarMap.find avar defs in
                dprintf "Will trim %s at %d" (Pp.var_to_string avar) stmt_off;
                (stmt_off, used_low_bits) :: to_be_trimmed
              end else begin
                dprintf "not trimming: used_low_bits %d/%d" used_low_bits
                  (Var.typ avar |> Typecheck.bits_of_width);
                to_be_trimmed
              end
            end
          with Not_found ->
            dprintf "not trimming: no def";
            to_be_trimmed
        end
      with Not_found ->
        dprintf "not trimming: avar not in map [%s]" (map_to_s map);
        to_be_trimmed
    in
    let do_stmt_uses map stmt =
      let uses = match stmt with
        | Ast.CJmp (exp, _, _, _)
        | Ast.Move (_, exp, _) ->
          Track_exp_bits.exp_uses exp
        | _ ->
          VarMap.empty
      in
      Track_exp_bits.join map uses
    in
    let do_stmt (subreg_map, defs, to_be_trimmed) stmt_off s =
      dprintf "Looking at stmt: %s" (Pp.ast_stmt_to_string s);
      (* Record uses. Note that this only has an effect for definitions
       * we track (see below).
       *)
      let subreg_map = do_stmt_uses subreg_map s in
      match s with
      | Ast.Move (avar, exp, _)
        when Typecheck.is_integer_type (Var.typ avar) ->
        begin
          dprintf "about to maybe_trim (avar = %s)" (Pp.var_to_string avar);
          let to_be_trimmed = maybe_trim subreg_map defs to_be_trimmed avar in
          let defs = VarMap.add avar stmt_off defs in
          let subreg_map = VarMap.add avar BatISet.empty subreg_map in
          (subreg_map, defs, to_be_trimmed)
        end
      | _ -> (subreg_map, defs, to_be_trimmed)
    in
    let do_bb stmts =
      let rec fixed_point trimmed cnt stmts =
        let _, _, trims = BatList.fold_lefti do_stmt
            (VarMap.empty, VarMap.empty, []) stmts
        in
        let trims = List.filter (fun (stmt_off, _) ->
            not (BatISet.mem stmt_off trimmed)) trims in
        match trims with
        | [] ->
          stmts
        | _ ->
          let stmts = apply_trims stmts trims in
          let trimmed =
            List.fold_left (fun trimmed (stmt_off, _) ->
                BatISet.add stmt_off trimmed) trimmed trims
          in
          if cnt > 0 then begin
            fixed_point trimmed (cnt - 1) stmts
          end else begin
            (* There's no way we have more trims than definitions,
             * if we ever get here, we've messed up.
            *)
            failwith "Fixed-point iteration limit exhausted!"
          end
      in
      fixed_point BatISet.empty (List.length stmts) stmts
    in
    object
      method name = "subreg-liveness"
      method transform (_ : pipeline_ctx) cfg =
        Cfg_convenience.AST.rewrite_by_bb_stmts cfg do_bb
    end

  let addrmap =
    object
      method name = "build-addrmap"
      method analyze ctx cfg =
        let addrmap = BatHashtbl.create 100 in
        Cfg.AST.G.iter_vertex (fun v ->
            let stmts = Cfg.AST.get_stmts cfg v in
            List.iter (fun s -> match s with
                | Ast.Label (Type.Addr addr, _) ->
                  BatHashtbl.add addrmap addr (Cfg.AST.G.V.label v)
                | _ -> ()) stmts) cfg;
        set_addrmap ctx addrmap
    end

  let do_break_after_calls ctx orig_cfg =
    let split_stmts_after_calls is_call stmts_with_addr =
      let ret res acc =
        match acc with
        | [] -> res
        | _ -> (List.rev acc) :: res
      in
      let rec split_when_addr_changes addr res acc remaining =
        match remaining with
        | [] ->
          ret res acc
        | (a, s) :: rest ->
          (match a with
           | None ->
             split_when_addr_changes addr res (s :: acc) rest
           | Some a ->
             if Int64.compare a addr <> 0 then
               let nacc = List.rev acc in
               split (nacc :: res) [s] rest
             else
               split_when_addr_changes addr res (s :: acc) rest)
      and split res acc remaining =
        match remaining with
        | [] ->
          ret res acc
        | (a, s) :: rest ->
          (match a with
           | None ->
             split res (s :: acc) rest
           | Some a ->
             if is_call (a, s) then begin
               split_when_addr_changes a res (s :: acc) rest
             end else begin
               split res (s :: acc) rest
             end)
      in
      split [] [] stmts_with_addr
    in
    let module C = Cfg.AST in
    let nr_vs = C.G.nb_vertex orig_cfg in
    let map_src = BatHashtbl.create nr_vs in
    let map_dst = BatHashtbl.create nr_vs in
    let callinfo = get_callinfo ctx in
    dprintf "Call information: %s" (Callinfo.to_string callinfo);
    let is_call (addr, _) = Callinfo.call_at_addr callinfo addr <> None in
    let map_src, map_dst, ng = C.G.fold_vertex (fun v (map_src, map_dst, ng) ->
        let stmts = C.get_stmts orig_cfg v in
        let astmts = Misc.stmts_with_addrs stmts in
        let split = split_stmts_after_calls is_call astmts in
        dprintf "break_after_calls: split %s to %d parts"
          (Cfg.AST.v2s v) (List.length split);
        let split = match split with
          (*
           * Ensure we re-create empty BBs. Not sure if we need
           * preservation of empty BBs, but playing it safe.
           *)
          | [] -> [[]]
          | _ -> split
        in
        (*
         * Notice: split is in reverse order, but b/c of the special
         * treatment of BB_Entry/BB_Exit/etc, we need it to be in
         * proper order.
        *)
        let split = List.rev split in
        let _, nvs, ng = List.fold_left (fun (in_first, vs, acc_g) stmts ->
            if in_first then begin
              let vlab = Cfg.AST.G.V.label v in
              match vlab with
              | Cfg.BB_Entry ->
                let acc_g, entry = Cfg_ast.create_entry acc_g in
                let acc_g = C.set_stmts acc_g entry stmts in
                (false, entry :: vs, acc_g)
              | Cfg.BB_Exit ->
                let acc_g, v = Cfg_ast.find_exit acc_g in
                let acc_g = C.set_stmts acc_g v stmts in
                (false, v :: vs, acc_g)
              | Cfg.BB_Indirect ->
                let acc_g, v = Cfg_ast.find_indirect acc_g in
                let acc_g = C.set_stmts acc_g v stmts in
                (false, v :: vs, acc_g)
              | Cfg.BB_Error ->
                let acc_g, v = Cfg_ast.find_error acc_g in
                let acc_g = C.set_stmts acc_g v stmts in
                (false, v :: vs, acc_g)
              | Cfg.BB _ ->
                let acc_g, nv = Cfg.AST.create_vertex acc_g stmts in
                (false, nv :: vs, acc_g)
            end else begin
              let acc_g, nv = Cfg.AST.create_vertex acc_g stmts in
              (false, nv :: vs, acc_g)
            end)
            (true, [], ng) split
        in
        (*
         * Get the new vertices to be in program order, this is
         * required for the threading below.
         *)
        let nvs = List.rev nvs in
        dprintf "New vertexes for %s:" (Cfg.AST.v2s v);
        List.iter (fun nv ->
            dprintf "nvertex: %s" (Cfg.AST.v2s nv)) nvs;
        (* Thread the new BBs w/ fall-through edges *)
        let _, ng = List.fold_left (fun (prev_v, acc_g) curr_v ->
            let nacc_g = match prev_v with
              | Some prev_v ->
                C.add_edge_e acc_g (C.G.E.create prev_v None curr_v)
              | None ->
                acc_g
            in
            (Some curr_v, nacc_g)) (None, ng) nvs
        in
        ignore(match nvs with
            | [] -> failwith "No created BBs??"
            | _ ->
              let hd = List.hd nvs in
              let last = BatList.last nvs in
          (*
           * All edges that were pointing to v, should now point to the
           * first of the BBs we created here.
           *)
              let v2s = Cfg.AST.v2s in
              dprintf "Add DST mapping: %s -> %s" (v2s v) (v2s hd);
              BatHashtbl.add map_dst v hd;
          (*
           * For all edges that had v as source, now we need to use the last
           * created BB.
           *)
              dprintf "Add SRC mapping: %s -> %s" (v2s v) (v2s last);
              BatHashtbl.add map_src v last);
        (map_src, map_dst, ng))
        orig_cfg
        (map_src, map_dst, (C.empty ()))
    in
      (*
       * Now make another pass, adding the edges that existed in the
       * original graph.
       *)
    C.G.fold_edges_e (fun e ng ->
        let lab = C.G.E.label e in
        let src = C.G.E.src e in
        let dst = C.G.E.dst e in
        let src = match Misc.bathashtbl_find_option map_src src with
          | None -> failwith "couldn't get mapping for src vertex"
          | Some v -> v in
        let dst = match Misc.bathashtbl_find_option map_dst dst with
          | None ->
            let str = Printf.sprintf "couldn't get mapping for dst vertex (%s)"
                (Cfg.AST.v2s dst)
            in
            failwith str
          | Some v -> v in
        C.add_edge_e ng (C.G.E.create src lab dst)) orig_cfg ng

  let break_after_calls1 =
    object
      method name = "break-after-calls1"
      method transform = do_break_after_calls
    end

  let break_after_calls2 =
    object
      method name = "break-after-calls2"
      method transform = do_break_after_calls
    end

end

exception Last_eax_def_bb of (Cfg.SSA.G.V.t * Ssa.stmt list)

type exit_bb_type =
  | ExitBBReturns
  | ExitBBHalts
  | ExitBBCalls of Type.addr
  | ExitBBEmpty
  | ExitBBUnidentified

let vh_find vh var =
  try
    Some (Var.VarHash.find vh var)
  with Not_found -> None


module Ssa_passes =
struct
  module C = Cfg.SSA
  module G = C.G
  module H = Analysis_helpers.SSA
  module CC = Cfg_convenience.SSA

  open Ssa

  let start =
    object
      method name = "ssa-start"
      method transform _ cfg = cfg
    end

  let in_bb_tmpl callinfo addrmap ~ignore_calls bb addr =
    if ignore_calls && (Callinfo.call_at_addr callinfo addr <> None) then
      false
    else
      match Misc.bathashtbl_find_option addrmap addr with
      | Some bbid -> bbid = (G.V.label bb)
      | None -> false

  let in_bb_by_stmts cfg v =
    let stmts = C.get_stmts cfg v in
    let search addr =
      try
        ignore(List.find (fun s ->
            match Bb.ssa_stmt_get_addr s with
            | None -> false
            | Some stmt_addr -> stmt_addr = addr) stmts);
        true
      with Not_found -> false
    in
    BatResult.Ok search

  let patch_cfg cfg to_insert =
    let pcmp (off1, _) (off2, _) = off1 - off2 in
    let sort = List.sort pcmp in
    BatMap.foldi (fun bbid patches cfg ->
        (* let patches = match BatMap.Exceptionless.find bbid to_insert with *)
        (*   | None -> [] *)
        (*   | Some patches -> sort patches *)
        (* in *)
        let patches = sort patches in
        let v =
          try
            Cfg.SSA.find_vertex cfg bbid
          with Not_found ->
            let s = Printf.sprintf "Couldn't find recorded bbid %s"
                (Cfg.bbid_to_string bbid) in
            failwith s
        in
        let stmts = C.get_stmts cfg v in
        let _, _, stmts = List.fold_left (fun (i, patches, acc) stmt ->
            let to_prepend, patches =
              BatList.span (fun (off, _) -> off = i) patches
            in
            let to_prepend = List.map (fun (_, s) -> s) to_prepend in
            (i + 1, patches, stmt :: (to_prepend @ acc)))
            (0, patches, []) stmts
        in
        let stmts = List.rev stmts in
        C.set_stmts cfg v stmts
      ) to_insert cfg

  let remove_noreturn_edges =
    object(self)
      method name = "remove-noreturn-edges"
      (*
       * Remove out-edges from BBs that have a call to a function that
       * doesn't return. Typically, this should be a fallthrough edge
       * b/c the compiler "knows" that a function can't return.
       *
       * XXX: we should probably be propagating the noreturn attribute
       * up the callgraph. The compiler might do that too...
       *)
      method transform ctx cfg =
        let ci = get_callinfo ctx in
        let is_noreturn target =
          match get_function_info ctx target with
          | None ->
            failwith (Printf.sprintf "Couldn't get Function_info for %#Lx in pass %s"
                        target self#name)
          | Some fi ->
            let has = Function_info.has_attr fi in
            (has Func_attr.Abort) || (has Func_attr.Noreturn)
        in
        let has_noreturn v =
          let in_bb = match in_bb_by_stmts cfg v with
            | BatResult.Ok is_in_bb -> is_in_bb
            | BatResult.Bad _ ->
            (*
             * Calls cannot be found in BBs w/o address info, as those
             * are generated by rep prefixes.
             *)
              (fun _ -> false)
          in
          Callinfo.fold (fun call exists ->
              match exists with
              | true -> exists
              | false ->
                begin
                  match call with
                  | Callgraph.IndirectCall _ ->
                    (* Should have bailed out earlier *)
                    failwith "can't get here"
                  | Callgraph.DirectCall (callsite, target) ->
                    (in_bb callsite) && is_noreturn target
                end) ci false
        in
        G.fold_vertex (fun v g ->
            if (not (Bb.SSA.is_nop g v)) &&
               (G.out_degree g v <> 0) &&
               has_noreturn v then begin
              dprintf "Function has noreturn call";
              match G.succ_e g v with
              | [] -> failwith "Can't get here"
              | fallthrough :: [] ->
                assert (None = (G.E.label fallthrough));
                dprintf "Removing fallthrough edge";
                let g' = C.remove_edge_e g fallthrough in
                Prune_unreachable.prune_unreachable_ssa g'
              | edges ->
            (*
             * This would be a very weird compiler that generated this,
             * chances are /we/ messed up somewhere
             *)
                wprintf "Cjmp after noreturn function!";
                let g' = List.fold_left (fun g e ->
                    C.remove_edge_e g e) g edges in
                Prune_unreachable.prune_unreachable_ssa g'
            end else
              g
          ) cfg cfg
    end

  (*
   * Peel off any NOTs at the (successive) root of the expression
   * in a cjmp condition. If the number of NOTs is odd, remove the
   * final NOT and flip the T/F labels in the outgoing edges.
   *)
  let normalize_cjmp_cond =
    object
      method name = "normalize-cjmps"
      method transform ctx cfg =
        let (_, fd, _) = get_data_dependencies ctx in
        let get_def = vh_find fd in
        let flip_edge_label cfg e =
          let src = G.E.src e in
          let dst = G.E.dst e in
          let lab = G.E.label e in
          let lab = match lab with
            | None -> failwith "Fallthrough edge in flip_edge_label"
            | Some x -> Some (not x)
          in
          let cfg = C.remove_edge_e cfg e in
          C.add_edge_e cfg (G.E.create src lab dst)
        in
        let flip_cjmp cfg v =
          let succ_e = G.succ_e cfg v in
          match succ_e with
          | [e1; e2] ->
            let cfg = flip_edge_label cfg e1 in
            flip_edge_label cfg e2
          | _ ->
            failwith "CJmp doesn't have exactly two OUT edges"
        in
        let rec resolve_nots nr_nots value =
          match value with
          | Lab _ ->
            failwith "label in cjmp cond?"
          | Int _ ->
            (nr_nots, value)
          | Var var ->
            begin
              let defsite = get_def var in
              match defsite with
              | None ->
                (nr_nots, value)
              | Some defsite ->
                begin
                  let def_stmt = H.get_stmt_at cfg defsite in
                  match def_stmt with
                  | Move (avar, UnOp (Type.NOT, nvalue), _) ->
                    resolve_nots (nr_nots + 1) nvalue
                  | _ ->
                    (nr_nots, value)
                end
            end
        in
        let do_cjmp_nots collected (cond, t1, t2, attrs) =
          let (nr_nots, value) = resolve_nots 0 cond in
          if (nr_nots mod 2) = 1 then begin
            (* Peel off all NOTs and flip the control flow *)
            (* Note we need to  flip the cjmp targets too! *)
            let ncjmp = CJmp (value, t2, t1, attrs) in
            let nstmts = List.rev (ncjmp :: collected) in
            `FlipCjmp nstmts
          end else begin
            if nr_nots > 0 then begin
              (* #NOTs is even; just peel them all off *)
              let ncjmp = CJmp (value, t1, t2, attrs) in
              let nstmts = List.rev (ncjmp :: collected) in
              `NoFlipCjmp nstmts
            end else begin
              (* No NOTs to begin with, don't rewrite anything *)
              `NoFlipCjmp []
            end
          end
        in
        let do_cjmp_neq collected (cond, t1, t2, attrs) =
          match cond with
          | Lab _ ->
            failwith "label in cjmp cond?"
          | Int _ ->
            `NoFlipCjmp []
          | Var var ->
            begin
              match get_def var with
              | None ->
                `NoFlipCjmp []
              | Some defsite ->
                begin
                  let def_stmt = H.get_stmt_at cfg defsite in
                  match def_stmt with
                  | Move (avar, BinOp (Type.NEQ, op1, op2), attrs) ->
                    (* OK, so we have
                     *   avar = (op1 != op2)
                     *   cjmp (avar, t1, t2)
                     * and we're gonna change that to
                     *   tmp = (op1 == op2)
                     *   avar = (op1 != op2)
                     *   cjmp (tmp, t2, t1)
                     * so as to normalize on the zero value (the non-zero
                     * values could reasonably be different and the code would
                     * still be equivalent). DCE should eliminate avar in almost
                     * all cases.
                    *)
                    let tmp = Var.newvar "T_cjmp_neq" (Var.typ avar) in
                    let nstmt = Move (tmp, BinOp (Type.EQ, op1, op2), attrs) in
                    let ncjmp = CJmp (Var tmp, t2, t1, attrs) in
                    let stmts = List.rev (ncjmp :: collected) in
                    dprintf "do_cjmp_neq: Located statement %s" (Pp.ssa_stmt_to_string def_stmt);
                    `FlipCjmpAndInsert (stmts , (nstmt, defsite))
                  | _ ->
                    `NoFlipCjmp []
                end
            end
        in
        let do_stmts inspector bb_stmts =
          let rec inner collected remaining =
            match remaining with
            | [] ->
              (* We only end up here if there were no stmts *)
              `NoFlipCjmp []
            | [last] ->
              begin
                match last with
                | CJmp (cond, t1, t2, attrs) ->
                  inspector collected (cond, t1, t2, attrs)
                | _ ->
                  `NoFlipCjmp []
              end
            | x :: rest ->
              inner (x :: collected) rest
          in
          inner [] bb_stmts
        in
        let each_bb inspector v (g, to_flip, to_insert) =
          let stmts = C.get_stmts cfg v in
          match do_stmts inspector stmts with
          | `NoFlipCjmp [] ->
            (g, to_flip, to_insert)
          | `NoFlipCjmp nstmts ->
            (C.set_stmts g v nstmts, to_flip, to_insert)
          | `FlipCjmp nstmts ->
            (*
             * Don't rewrite edges while in fold_vertex. Maybe this works,
             * but even then, I'm not sure it'll continue to work on later
             * ocamlgraph versions.
             *)
            let g = C.set_stmts g v nstmts in
            (g, v :: to_flip, to_insert)
          | `FlipCjmpAndInsert (stmts, (nstmt, defsite)) ->
            begin
              let g = C.set_stmts g v stmts in
              (* Possibly different vertex from here on *)
              let (v, off) = defsite in
              let to_insert = BatMap.modify_opt (G.V.label v) (function
                  | None -> Some [(off, nstmt)]
                  | Some others -> Some ((off, nstmt) :: others))
                to_insert
              in
              (g, v :: to_flip, to_insert)
            end
        in
        List.fold_left (fun cfg inspector ->
            let acc = (cfg, [], BatMap.empty) in
            let cfg, to_flip, to_insert =
              G.fold_vertex (each_bb inspector) cfg acc
            in
            let cfg = List.fold_left flip_cjmp cfg to_flip in
            patch_cfg cfg to_insert)
          cfg
          [do_cjmp_nots; do_cjmp_neq]
    end

  let mark_eax_liveout =
    object(self)
      method name = "mark-eax-liveout"
      method transform ctx cfg =
        let ci = get_callinfo ctx in
        let ri = get_retinfo ctx in
        let hi = get_hltinfo ctx in
        let classify_other v =
          ExitBBUnidentified
        in
        let classify_exit v =
        (*
         * Get vertex as an argument, so that in_bb_by_stmts will only
         * be called when the BB is not only composed of nop stmts.
         * XXX: possibly is_nop should be replaced with has_label,
         * has_address or something...
         *)
          let in_bb vertex = match in_bb_by_stmts cfg vertex with
            | BatResult.Ok f -> f
            | BatResult.Bad str ->
              let str = Printf.sprintf "%s: %s" (C.v2s vertex) str in
              failwith str
          in
          let has_such addrlist =
            try
              ignore(List.find (in_bb v) addrlist);
              true
            with Not_found ->
              false
          in
          if Bb.SSA.is_nop cfg v then
            ExitBBEmpty
          else if has_such ri then
            ExitBBReturns
          else if has_such hi then
            ExitBBHalts
          else begin
            match last_call ci (in_bb v) with
            | None -> classify_other v
            | Some Callgraph.DirectCall (_, target) -> ExitBBCalls target
            | _ -> failwith "can't get here"
          end;
        in
        let set_liveout s =
          let add_liveout s =
            match s with
            | Move (var, exp, attrs) -> Move (var, exp, Type.Liveout::attrs)
            | _ -> failwith "Why are we setting Liveout on a non-Move?"
          in
          let attrs = get_attrs s in
          let lo = BatList.Exceptionless.find (fun attr ->
              match attr with
              | Type.Liveout -> true
              | _ -> false) attrs
          in
          dprintf "Marking %s as Liveout" (Pp.ssa_stmt_to_string s);
          match lo with
          | Some _ -> s
          | None -> add_liveout s
        in
        let has_eax_def v () =
          let stmts = C.get_stmts cfg v in
          (* fold_right, as we need to find the last definition of EAX
           * in a BB
          *)
          let (matched, nstmts) = List.fold_right (fun s (found, stmts) ->
              match s with
              | Move (lv, _, attrs) ->
                if (not found) && (String.compare (Var.name lv) "R_EAX") = 0 then
                  (* NOTE: if found is true, we already rewrote the last definition
                     of EAX, but we need to return the full list of statements,
                     so keep going.
                  *)
                  (true, (set_liveout s)::stmts)
                else
                  (found, s::stmts)
              | _ -> (found, s::stmts)) stmts (false, [])
          in
          match matched with
          | false -> ()
          | true ->
            (* Bail early from the graph walk and allow our caller
               to adjust the BB statements *)
            raise (Last_eax_def_bb (v, nstmts))
        in
        let rec mark_from_exit lvl cfg exit_bb =
        (*
         * XXX: Here we need to classify the exit_bb accordingly and detect
         * if eax is used or not; It will not be used e.g. if the function
         * called has the Crash attribute (__stack_chk_fail being one such
         * example). Unfortunately, we need to do that by passing callsite
         * information from the AST form to here, which means extending
         * the pipeline a bit. Deadline rush ATM, can't do that.
         *)
          dprintf "mark_from_exit (%d) %s" lvl
            (Cfg.bbid_to_string (G.V.label exit_bb));
          match classify_exit exit_bb with
          | ExitBBReturns
          | ExitBBHalts  ->
            (try
               let exit_bbid = G.V.label exit_bb in
               Cfg_convenience.SSA.walk_from_bb_inclusive has_eax_def cfg
                 () exit_bbid G.pred;
               (* No definition of EAX in the graph at all *)
               wprintf "no EAX definition in graph";
               cfg
             with Last_eax_def_bb (v, nstmts) ->
               C.set_stmts cfg v nstmts)
          | ExitBBCalls target_addr ->
            (match get_function_info ctx target_addr with
             | None ->
               failwith (Printf.sprintf "Couldn't get Function_info for %#Lx in pass %s"
                           target_addr self#name)
             | Some fi ->
               if (Function_info.has_attr fi Func_attr.Abort) ||
                  (Function_info.has_attr fi Func_attr.Noreturn) then
                 cfg (* nothing to do *)
               else
                 let str = Printf.sprintf
                     "Exit BB has call to unknown function: %s"
                     (Function_info.to_string fi) in
                 raise (Confusing_function str))
          | ExitBBEmpty ->
            (match G.pred cfg exit_bb with
             | [] ->
               dprintf "BB is %s" (Cfg.bbid_to_string (G.V.label exit_bb));
               failwith "No preds for empty exit BB"
             | [p] -> mark_from_exit (lvl + 1) cfg p
             | _ -> failwith "More than one pred for empty exit BB")
          | ExitBBUnidentified ->
            dprintf "retinfo: %s" (addrlist_to_str ri);
            dprintf "callinfo: %s" (Callinfo.to_string ci);
            dprintf "hltinfo: %s" (addrlist_to_str hi);
            (* XXX: should recurse to the predecessors? *)
            raise (Confusing_function "ExitBBUnidentified")
        in
        let exit_bbs = Cfg_convenience.SSA.get_exit_bbs cfg in
        let exit_bbs = List.filter (fun v ->
            G.V.label v <> Cfg.BB_Error) exit_bbs in
        List.fold_left (mark_from_exit 0) cfg exit_bbs
    end

  let phi_propagation =
    object
      method name = "phi-propagation"
      method transform ctx cfg =
        let var_phi_definitions = BatHashtbl.create (G.nb_vertex cfg) in
        (*
         * For each phi, check if the variable it's assigned to is
         * only used in phis. If so, propagate.
         *)
        let pass1 v graph =
          dprintf "phi-prop: propagate_phis1: looking at %s" (C.v2s v);
          let stmts = C.get_stmts graph v in
          let nstmts = BatList.filter_map (fun s ->
              match s with
              | Move (v, Phi vs, attrs) ->
                if debug () then begin
                  let str = Print.list_to_string Pp.var_to_string vs in
                  dprintf "propagate_phis1: adding %s -> %s" (Pp.var_to_string v) str
                end;
                (* There can be only one (definition of a var) *)
                BatHashtbl.add var_phi_definitions v vs;
                if List.mem Type.Liveout attrs then begin
                  Some s
                end else begin
                  None
                end
              | _ -> Some s
            ) stmts in
          C.set_stmts graph v nstmts
        in
        let passN v (pass_mods, graph) =
          dprintf "phi-prop: propagate_phis2: looking at %s" (C.v2s v);
          let stmts = C.get_stmts graph v in
          let mods = ref pass_mods in
          let prepend_stmts = ref [] in
          let phivar_temps = BatHashtbl.create 10 in
          let temp_for_phivar var phi_args =
            match Misc.bathashtbl_find_option phivar_temps var with
            | None ->
              (* If don't already have a temp for this phivar in this BB,
                 create one
              *)
              let new_phi = Phi phi_args in
              let typ = Var.typ var in
              let temp = match typ with
                | Type.Array _ ->
                  let res = List.fold_left (fun acc v ->
                      match acc with
                      | BatResult.Ok "" ->
                        BatResult.Ok (Var.name v)
                      | BatResult.Ok name ->
                        if (Var.name v) = name then
                          BatResult.Ok name
                        else
                          let str = Printf.sprintf
                              "different arrays in phi: %s and %s"
                              (Var.name v) name in
                          BatResult.Bad str
                      | BatResult.Bad _ as bad -> bad) (BatResult.Ok "") phi_args
                  in
                  (match res with
                   | BatResult.Ok "" -> failwith "Can't get here"
                   | BatResult.Ok name -> Var.newvar name typ
                   | BatResult.Bad err-> raise (Confusing_function err))
                | _ ->
                  Var.newvar "T_phi" typ
              in
              let temp_assign = Move (temp, new_phi, [Type.Synthetic]) in
              dprintf "propagate_phis2: prepending %s" (Pp.ssa_stmt_to_string temp_assign);
              prepend_stmts := temp_assign::(!prepend_stmts);
              BatHashtbl.add phivar_temps var temp;
              temp
            | Some temp -> temp
          in
          let expand_rvar rvar =
            (* If this rvar is defined to be a phi, return the phi arguments,
             * else return a list with just this var
            *)
            dprintf "trying to expand %s" (Pp.var_to_string rvar);
            match Misc.bathashtbl_find_option var_phi_definitions rvar with
            | None -> [rvar]
            | Some vars ->
              let recovered = vars in
              dprintf "Expanded %s to %s"
                (Pp.var_to_string rvar)
                (Print.list_to_string Pp.var_to_string recovered);
              recovered
          in
          let add_var_to_phi vars nvar =
            if List.mem nvar vars then
              vars
            else
              nvar :: vars
          in
          let add_vars_to_phi vars nvars = List.fold_left add_var_to_phi vars nvars in
          let rewrite_stmt s =
            let propagate_uses lhs_var phi_args =
              let do_expand_vars vs =
                let maybe_expand (i, vars) var =
                  let do_expand var =
                    match expand_rvar var with
                    | [] -> failwith (Printf.sprintf "variable %s imploded" (Var.name var))
                    | v::[] -> (i, add_var_to_phi vars v)
                    | expansion ->
                      let orig_len = List.length vars in
                      let nvars = add_vars_to_phi vars expansion in
                      let new_len = List.length nvars in
                      (i + (new_len - orig_len) - 1, nvars)
                  in
                  match lhs_var with
                  | Some lvar ->
                    if Var.equal lvar var then
                      (* Do not substitute a phi argument if we're in the
                       * definition of that same argument (e.g. a3 = phi(a3, b0)).
                      *)
                      (i, var::vars)
                    else
                      do_expand var
                  | None -> do_expand var
                in
                List.fold_left maybe_expand (0,[]) vs
              in
              do_expand_vars phi_args
            in
            let visitor = object(self)
              inherit Ssa_visitor.nop
              val lvar = ref None
              method visit_stmt s =
                (* Keep track of the variable assigned to; used by filter_self above *)
                dprintf "propagate_phis2: visit_stmt %s" (Pp.ssa_stmt_to_string s);
                match s with
                | Move (v, _, _) ->
                  lvar := Some v;
                  Type.DoChildren
                | _ ->
                  lvar := None;
                  Type.DoChildren
              method visit_exp expr =
                dprintf "propagate_phis2: visit_exp";
                (*
                 * Convert
                 *   a = phi(c, d)
                 *   b = phi(a, e)
                 * to
                 *   a = phi(c, d)
                 *   b = phi(c, d, e)
                 *)
                match expr with
                | Phi vs ->
                  let (changed, nvs) = propagate_uses !lvar vs in
                  if debug () then begin
                    let before = Print.list_to_string Pp.var_to_string vs in
                    let after = Print.list_to_string Pp.var_to_string nvs in
                    dprintf "propagate_phis2: phi expansion %s -> %s" before after
                  end;
                  if changed > 0 then begin
                    mods := !mods + 1;
                    Type.ChangeTo (Phi nvs)
                  end else
                    Type.DoChildren
                | _ ->
                  Type.DoChildren
              method visit_rvar rvar =
                dprintf "propagate_phis2: visit_rvar %s" (Pp.var_to_string rvar);
                (*
                 * If this is a reference to a variable defined to be a phi,
                 * replace it with said phi
                 *)
                let def_args = expand_rvar rvar in
                match def_args with
                | [] -> failwith "rvar replaced with nothing"
                | _::[] -> Type.DoChildren (* not defined to be a phi *)
                | _ -> Type.ChangeTo (temp_for_phivar rvar def_args)
            end
            in
            Ssa_visitor.stmt_accept visitor s
          in
          let nstmts = List.map rewrite_stmt stmts in
          (!mods, C.set_stmts graph v ((!prepend_stmts) @ nstmts))
        in
        let ng = G.fold_vertex pass1 cfg cfg in
        let iterate count initial_graph =
          let keep_going = ref true in
          let i = ref 1 in
          let g = ref initial_graph in
          while !keep_going do
            let (mods, ng) = G.fold_vertex passN !g (0, !g) in
            g := ng;
            dprintf "propagate_phis pass%d: %d changes" !i mods;
            if 0 = mods then
              keep_going := false;
            if !i > count then begin
              let str = Printf.sprintf "phi prop didn't settle after \
                                        %d iterations" count
              in
              (*
               * XXX: This pass should be rewritten as a fixpoint algorithm!
               *)
              if false then begin
                raise (Confusing_function str)
              end else begin
                keep_going := false
              end
            end;
            i := !i + 1
          done;
          !g
        in
        (* XXX: limit needs to be derived from the number of phis/BBs *)
        iterate 30 ng
    end

  let bap_simplifications _ g =
    Ssa_simp.simp_cfg ~usedc:false ~usesccvn:true ~usemisc:true g

  let bap_simplifications1 =
    object
      method name = "bap-ssa-simplifications1"
      method transform = bap_simplifications
    end

  let bap_simplifications2 =
    object
      method name = "bap-ssa-simplifications2"
      method transform = bap_simplifications
    end

  let bap_simplifications3 =
    object
      method name = "bap-ssa-simplifications3"
      method transform = bap_simplifications
    end

  let do_dce _ g =
    let (ng, _) = Deadcode.do_dce g in
    ng

  let dce1 =
    object
      method name = "dead-code-elimination1"
      method transform = do_dce
    end

  let dce2 =
    object
      method name = "dead-code-elimination2"
      method transform = do_dce
    end

  let coalesce_ssa1 =
    object
      method name = "coalesce-ssa1"
      method transform _ cfg = Coalesce.coalesce_ssa cfg
    end

  let coalesce_ssa2 =
    object
      method name = "coalesce-ssa2"
      method transform _ cfg = Coalesce.coalesce_ssa cfg
    end

  let drop_nop_bbs ctx cfg =
    (* first pass: duplicate BBs that have actual statements *)
    let drop_nop_bbs v cfg =
      dprintf "simplify: drop_nop_bbs1: looking at %s" (C.v2s v);
      let stmts = C.get_stmts cfg v in
      let has_removed_stmts () =
        dprintf "Got %d stmts" (List.length stmts);
        let in_bb = match in_bb_by_stmts cfg v with
          | BatResult.Ok f -> f
          | BatResult.Bad str ->
            let str = Printf.sprintf "%s: %s" (C.v2s v) str in
            failwith str
        in
        let has_such addrlist =
          try
            ignore(List.find in_bb addrlist);
            true
          with Not_found ->
            false
        in
        let ci = get_callinfo ctx in
        let ri = get_retinfo ctx in
        let hi = get_hltinfo ctx in
        (has_such ri) || (has_such hi) ||
        (match last_call ci in_bb with
         | Some _ -> true
         | None -> false)
      in
      let nop () =
        if Bb.SSA.is_nop cfg v then
          try
            not (has_removed_stmts ())
              (*
               * XXX: Hackity hack hack: if the BB really has no statements, we
               * won't be able to get the bounds. This should be made safer
               * by explicitly signaling that this is the case in get_bbbounds.
               *)
          with Invalid_argument _ -> true
        else
          false
      in
          (*
           * XXX: Take special care to only run nop () if the BB is not
           * one of these two, or get_bbbounds will crash and burn.
           *)
      match (G.V.label v) != Cfg.BB_Exit &&
            (G.V.label v) != Cfg.BB_Error &&
            (nop ())
      with
      | true -> begin
          (* a nop BB can't have a jump or a cjmp, it *has* to fall through *)
          assert ((G.out_degree cfg v) = 1);
          dprintf "Dropping nop node %s" (C.v2s v);
          let succ = List.hd (G.succ cfg v) in
          let cfg = List.fold_left (fun cfg pred_e ->
              let label = G.E.label pred_e in
              let src = G.E.src pred_e in
              let cfg = C.remove_edge_e cfg pred_e in
              let new_edge = G.E.create src label succ in
              C.add_edge_e cfg new_edge
            ) cfg (G.pred_e cfg v)  in
          C.remove_vertex cfg v
        end
      | false ->
        cfg
    in
    (* second pass: drop references to nop BBs
           XXX: this has only been tested in functions with a single nop BB
        let drop_nop_bbs2 v ngraph =
          dprintf "simplify: drop_nop_bbs2: looking at %s" (C.v2s v);
          try
            let v' = Hashtbl.find vmap v in
            let ng = ngraph in
            C.G.fold_pred_e (fun e acc ->
                try
                  let src = Hashtbl.find vmap (E.src e) in
                  let ne = E.create src (E.label e) v' in
                  dprintf "simplify: adding predecessor edge";
                  C.add_edge_e acc ne
                with Not_found -> (* predecessor was a nop BB *)
                  dprintf "simplify: skipping nop predecessor";
                  acc
              ) orig_graph v ng
          with Not_found ->     (* nop BB *)
            dprintf "simplify: Node %s is a nop node" (C.v2s v);
            dprintf "simplify: %s" (Print.list_to_string Pp.ssa_stmt_to_string (C.get_stmts orig_graph v));
            let find_no_nop_successor g v =
              let single_successor g v =
                (match C.G.succ orig_graph v with
                 | [] -> None
                 | succ::[] -> Some succ
                 | _ -> failwith "Can't happen")
              in
              let is_no_nop = Hashtbl.mem vmap in
              let rec find g v =
                (match single_successor g v with
                 | Some succ ->
                   if is_no_nop succ then Some succ
                   else (* find g succ *)
                     let str =
                       Printf.sprintf "Successor (%s) of nop (%s) is also a nop!"
                         (Cfg.bbid_to_string (C.G.V.label v))
                         (Cfg.bbid_to_string (C.G.V.label succ)) in
                     failwith str
                 | None -> None)
              in
              find g v
            in
            (match find_no_nop_successor orig_graph v with
             | Some succ ->
               dprintf "simplify: found no nop successor %s for %s"(C.v2s succ) (C.v2s v);
               (* adjust predecessor edges to point to v's single none nop successor *)
               C.G.fold_pred_e (fun edge acc ->
                   let src = E.src edge in
                   dprintf "simplify: adding edge from %s to %s skipping %s" (C.v2s src)
                     (C.v2s succ) (C.v2s v);
                   try
                     let src = Hashtbl.find vmap src in
                     let nedge = E.create src (E.label edge) succ in
                     C.add_edge_e acc nedge
                   with Not_found ->
                     failwith (Printf.sprintf "simplify: predecessor %s of %s is a nop" (C.v2s src) (C.v2s v))
                 ) orig_graph v ngraph
             | None -> ngraph)
        in*)
    G.fold_vertex drop_nop_bbs cfg cfg

  let drop_nop_bbs1 =
    object
      method name = "drop-nop-bbs1"
      method transform = drop_nop_bbs
    end

  let drop_nop_bbs2 =
    object
      method name = "drop-nop-bbs2"
      method transform = drop_nop_bbs
    end

  let compute_dd =
    object
      method name = "compute-data-dependencies"
      method analyze ctx g =
        set_data_dependencies ctx (Depgraphs.DDG_SSA.compute_dd g)
    end

  let compute_function_inputs =
    object
      method name = "compute-function-inputs"
      method analyze ctx g =
        let (vars, fd, _) = get_data_dependencies ctx in
        let inputs =
          Var.VarSet.filter (fun var ->
              match Var.typ(var) with
              | Type.Reg _ ->
                (try
                   ignore(Var.VarHash.find fd var);
                   false
                 with Not_found -> true)
              | _ -> false) vars in
        set_function_inputs ctx inputs
    end


  let rewrite_loadstores =
    object
      method name = "rewrite-stack-loadstores"
      method transform ctx g =
        Load_store_analysis.rewrite_stack_loadstores ctx.arch g
    end


   (*
      Perform basic collapsible load testing.
      That is, check if a load is preceded by a store to the same location with
      the same width.
      A less conservative version could look at other preceding stores, but
      that would require alias information to be useful so we do not bother
      at the moment.
   *)
  let compute_collapsible_loads =
    object
      method name = "compute-collapsible-loads"
      method analyze ctx cfg =
        let (vars, fd, fu) = get_data_dependencies ctx in
        let visitor =
          object
            inherit Ssa_visitor.nop

            val mutable current_location = None
            val collapsible_loads = BatHashtbl.create 8

            method get_collapsible_loads = collapsible_loads

            method visit_stmt = function
              | Move (v, _, _) ->
                current_location <- Some (Var.VarHash.find fd v);
                Type.DoChildren
              | _ ->
                current_location <- None;
                Type.DoChildren

            method visit_exp = function
              | Load (mem, idx, edn, typ) as load ->
                if H.mem_is_ary mem
                then
                  begin
                    try
                      let loc = Var.VarHash.find fd (H.val2var_exn mem) in
                      (match H.get_stmt_at cfg loc with
                       | Move (_, Store(_, idx', value, edn', typ'), _) ->
                         dprintf "Found candidate %s for collapsing"
                           (Pp.ssa_exp_to_string load);
                         if idx = idx' && edn = edn' && typ = typ'
                         then
                           begin
                             dprintf "Candidate %s is collapsible to %s"
                               (Pp.ssa_exp_to_string load) (Pp.value_to_string value);
                             (match current_location with
                              | Some l -> BatHashtbl.add collapsible_loads l value
                              | None ->
                                let str = "Expected a current location for the collapsible load!" in
                                raise (Confusing_function str))
                           end
                         else
                           dprintf "Pruning collapsible candidate %s"
                             (Pp.ssa_exp_to_string load);
                       | _ -> ()
                      );
                      Type.SkipChildren
                    with Not_found ->
                      dprintf "Skipping %s, no definition found."
                        (Pp.ssa_exp_to_string load);
                      Type.SkipChildren
                  end
                else Type.SkipChildren
              | _ -> Type.SkipChildren
          end
        in
        ignore(Ssa_visitor.cfg_accept visitor cfg);
        set_collapsible_loads ctx visitor#get_collapsible_loads
    end

  let collapse_loads =
    object
      method name = "collapse-load"
      method transform ctx cfg =
        let replace_load cfg ((bb, offset), value) =
          let rev_stmts, _ = List.fold_left (fun (stmts, i) stmt ->
              if i = offset
              then begin
                match stmt with
                | Move (v, Load _, attrs) ->
                  let nstmt = Move (v, Val value, attrs) in
                  dprintf "Collapsing %s to %s"
                    (Pp.ssa_stmt_to_string stmt)
                    (Pp.ssa_stmt_to_string nstmt);
                  nstmt :: stmts, i + 1
                | _ -> failwith "Collapsible load is not a load!"
              end
              else (stmt :: stmts, i + 1)
            ) ([], 0) (C.get_stmts cfg bb) in
          C.set_stmts cfg bb (List.rev rev_stmts)
        in
        let collapsible_loads = get_collapsible_loads ctx in
        BatEnum.fold replace_load cfg (BatHashtbl.enum collapsible_loads);
    end
  let mark_stores_liveout =
    object
      method name = "mark-stores-liveout"
      method transform _ cfg =
        let mark_store_liveout =
          let open Var_convenience.Array in
          let open Analysis_helpers.SSA in
          function
          | Move(dst, (Store (mem, _, _, _, _) as store), attrs) when
              not ((mem_is_ary mem) && (Karch.X86.is_stack_reg (base_reg (val2var_exn mem)))) ->
            Move(dst, store, Type.Liveout :: attrs)
          | s -> s
        in
        G.fold_vertex (fun v acc_g ->
            let stmts = C.get_stmts cfg v in
            let stmts = List.map mark_store_liveout stmts in
            C.set_stmts acc_g v stmts) cfg cfg
    end

let prde = object
    method name = "partial-redundant-definition-elimination"
    method transform _ cfg =
      let module HC = Hashtbl_convenience in
      (* 1. Collect BBs with 2 outgoing edges *)
      let candidates = G.fold_vertex (fun v acc ->
        if G.out_degree cfg v = 2 then begin
          dprintf "Considering %s for prde!" (C.v2s v);
          v :: acc
        end else acc
      ) cfg [] in
      let visibility_info = Visibility.initialize cfg in
      (* 2. Collect the definitions *)
      let label = G.V.label in
      let is_used var v =
        try
          Visibility.var_is_used_exn visibility_info var (label v)
        with Not_found -> false in
      let safe_defs_per_bb = List.fold_left (fun acc v ->
        let safe_defs = List.fold_left (fun acc stmt ->
          match stmt with
          (*
            Moving memory operations can change the semantics
            (e.g., access violations), so we do not consider these
            safe candidates.
          *)
          | Move (var, Load _, _)
          | Move (var, Store _, _) -> acc
          | Move (var, _, _) when is_used var v -> acc
          | Move (var, _, _) ->
             dprintf "%s: %s contains a safe def %s" (C.v2s v)
               (Pp.ssa_stmt_to_string stmt) (Pp.var_to_string var);
            var :: acc
          | _ -> acc
        ) [] (C.get_stmts cfg v) in
        BatHashtbl.add acc v (List.rev safe_defs); acc
      ) (BatHashtbl.create (List.length candidates)) candidates in
      (* 3. For each candidate see if its definitions are useful in
       *only* one successor. *)
      let is_useful v var = Visibility.var_useful visibility_info var (G.V.label v) in
      let redundant_defs = BatHashtbl.fold (fun v vars acc ->
        List.fold_left (fun acc var ->
        let useful_succ = List.fold_left (fun acc v ->
          if is_useful v var then v :: acc
          else acc
        ) [] (G.succ cfg v) in
        begin match (List.length useful_succ) with
        | 0 -> dprintf "Variable %s is not useful in any successor!" (Pp.var_to_string var)
        | 1 -> dprintf "Variable %s is redundant!" (Pp.var_to_string var);
          HC.append acc v (var, List.hd useful_succ)
        | 2 -> dprintf "Variable %s is not redundant!"
           (Pp.var_to_string var)
        | _ -> failwith (Printf.sprintf "BB %s has more successors than outgoing edges!" (C.v2s v))
        end;
        acc) acc vars
      ) safe_defs_per_bb (BatHashtbl.create (List.length candidates)) in
      let cfg' = BatHashtbl.fold (fun v rdef_succ_pairs cfg ->
        let rdefs = List.map fst rdef_succ_pairs in
        let rdef2succ var = List.assoc var rdef_succ_pairs in
        let stmts = C.get_stmts cfg v in
        let needed, redundant, running =
          List.fold_left (fun (needed, redundant, running) -> function
          | Comment _ | Label _ as s -> (needed, redundant, s :: running)
          | Move (var, _, _) as s -> if List.mem var rdefs then begin
            (* Append each redundant definition to a list indexed by the
               useful successor.*)
            HC.append redundant (rdef2succ var) (List.rev (s :: running));
            (needed, redundant, [])
          end else begin
            let needed = needed @ (List.rev (s :: running)) in
            (needed, redundant, [])
          end
          | _ as s-> let needed = needed @ (List.rev (s :: running)) in
                     (needed, redundant, [])
          ) ([], BatHashtbl.create 8, []) stmts in
        (* This should only happens if a BB ends with a label or comment! *)
        let needed = needed @ running in
        let cfg = C.set_stmts cfg v needed in
        let cfg = BatHashtbl.fold (fun v' stmts cfg ->
          let stmts = List.flatten stmts in
          let old_edge = G.find_edge cfg v v' in
          let cfg = C.remove_edge_e cfg old_edge in
          (* The new edge requires the same label
             (i.e., true or false) *)
          let cfg, v'' = C.create_vertex cfg stmts in
          dprintf "Created new vertex %s" (C.v2s v'');
          let new_edge = G.E.create v
            (G.E.label old_edge) v'' in
          let cfg = C.add_edge_e cfg new_edge in
          (* Finally add the fall-through edge *)
          C.add_edge cfg v'' v'
        ) redundant cfg in
        cfg
      ) redundant_defs cfg in
      cfg'
  end

let buoyancy =
  let module LH = (* Local helpers *)
  struct
    let pos_to_string (bb, i) =
      Printf.sprintf "(%s, %d)" (Cfg.SSA.v2s bb) i
    let is_candidate = function
      | Move (_,Load _,_) | Move (_,Store _,_) | Move (_,Phi _,_)-> false
      | Move (_,_,attrs) when List.mem Type.Liveout attrs -> false
      | Move _ -> true
      | _ -> false
    let get_avar = function
      | Move (v,_,_) -> Some v
      | _ -> None
    let is_phi = function
      | Phi _ -> true
      | _ -> false
    let is_load = function
      | Load _ -> true
      | _ -> false
    let is_store = function
      | Store _ -> true
      | _ -> false
    let site2pos ?(order=0) (bb, depth)  = (bb, depth, order)
    let get_depth (_,d,_) = d
    let get_def (s,_,_) = s
    let get_order (_,_,o) = o
    let depth_cmp p p' = compare (get_depth p) (get_depth p')
    let cmp_order p p' = compare (get_order p) (get_order p')
    let pair n m = (n, m)
    let list2vh ~key list =
      let add_entry tbl value = match key value with
        | Some var -> VH.add tbl var value; tbl
        | None -> tbl in
      List.fold_left add_entry (VH.create (List.length list)) list
    let prependable i = (get_depth |- (>) i)

  end in
  object
    method name = "buoyancy"
    method transform ctx cfg =
      let optimal_pos_tbl = VH.create 64 in
      let get_definfo = H.def_info cfg in
      let is_dom pos1 pos2 =
        let ret = H.pos_dom cfg pos1 pos2 in
        dprintf "does %s dominate %s?: %b"
          (LH.pos_to_string pos1) (LH.pos_to_string pos2) ret;
        ret
      in
      (* For each definition, find its optimal position, with the
         optimal position being after the operand definition
         dominating this definition or before BB_Entry if none of the
         operands are defined in this function. Definitions
         containing constants are moved to the beginning of
         BB_Entry.*)
      (* XXX: If a topological fold is used, some passes can be
         merged (e.g., get_definfo, collect_candidates, and
         find_optimal_pos). However, for now the following implementation suffices.
      *)
      let collect_candidates bb acc =
        dprintf "Collecting candidate definitions at %s" (C.v2s bb);
        let candidates =
          List.filter LH.is_candidate (C.get_stmts cfg bb) in
        (* Prepend the new candidates, because we are adding them
           in post-fix order! *)
        candidates @ acc
      in
      let candidates =
        H.fold_postfix_component collect_candidates cfg
          (G.V.create Cfg.BB_Entry) [] in
      let avar2def =
        let tbl = LH.list2vh ~key:LH.get_avar candidates in
        Hashtbl_convenience.VH.find_option tbl in
      (* Select the operand definition dominated by all other
         operand definitions. *)
      let select_optimal_pos (bb1, d1, o1) (bb2, d2, o2)=
        let pos1 = (bb1, d1) in
        let pos2 = (bb2, d2) in
        let (bb, d) = if is_dom pos1 pos2 then pos2 else pos1 in
        let o = if o1 > o2 then o1 else o2 in
        (bb, d, o)
      in
      let rec find_optimal_pos v =
        dprintf "Finding optimal position for %s" (Pp.var_to_string v);
        try
          let cached = VH.find optimal_pos_tbl v in
          let (bb, d, _) = cached in
          dprintf "Returning cached %s" (LH.pos_to_string (bb, d));
          cached
        with Not_found ->
          let def,site = get_definfo v in
          match def with
          (* We do not move phi definitions *)
          | Some def when (LH.is_phi def) || (LH.is_load def) || (LH.is_store def) ->
            let pos = LH.site2pos site in
            VH.add optimal_pos_tbl v pos;
            pos
          | Some def ->
            let ops = H.get_varargs_exp def in
            (* No ops, means only constant operands. *)
            if BatList.is_empty ops then begin
              (* Move definitions without data dependencies after
                 inputs & globals *)
              let pos = (G.V.create Cfg.BB_Entry, 0, 0) in
              VH.add optimal_pos_tbl v pos;
              pos
            end else begin
              let cur_bb, cur_d = site in
              let possible_pos = List.map find_optimal_pos ops in
              let bb, depth, order = BatList.reduce select_optimal_pos possible_pos in
              dprintf "possible_pos for %s: %s" (Pp.var_to_string v)
                (LH.pos_to_string (bb, depth));
              (* Don't bother moving the definition within the same BB.
                 The TFs will deal with different intra BB ordering of
                 definitions.*)
              if cur_bb = bb then begin
                let pos = LH.site2pos site in
                VH.add optimal_pos_tbl v pos;
                pos
              end else begin
                (* Increase the order to uphold the data
                   dependency, that is the order of inserting the
                   definitions. *)
                let pos = (bb, depth, order + 1) in
                VH.add optimal_pos_tbl v pos;
                pos
              end
            end
          | None -> (* Globals and inputs are defined before BB_Entry *)
            let pos = LH.site2pos site in
            VH.add optimal_pos_tbl v pos; pos
      in
      (* Compute the optimal positions for the definitions *)
      dprintf "Computing optimal positions";
      let candidate_vars = BatList.filter_map LH.get_avar candidates in
      List.iter (find_optimal_pos |- ignore) candidate_vars;

      (* Maps from bb to [(v, d, o); ...], i.e. all the statements that should be
       * moved to this bb *)
      let bb2avar = Hashtbl.create (VH.length optimal_pos_tbl) in
      VH.iter (fun v (bb,d,o) -> Hashtbl.add bb2avar bb (v,d,o)) optimal_pos_tbl;
      let bb2avar = Hashtbl.find_all bb2avar in

      dprintf "Moving definitions to optimal position";
      G.fold_vertex (fun v cfg ->
          (* Pair each stmt with its distance in the BB and remove
             stmts that will be inserted or are already inserted if their
             optimal position is different from their actual position.
             Not that optimal positions are computed based on actual
             positions, so filter after determining the depths.
          *)
          let stmts = (C.get_stmts cfg
                      |- BatList.mapi LH.pair
                      |- List.filter (snd |- LH.is_candidate |- not)) v
          in
          (* Get definitions to insert, ordered by depth.*)
          let defs = (bb2avar
                     |-BatList.filter_map (fun (v, d, o) ->
                         match avar2def v with
                         | Some s -> Some (s,d,o)
                         | None -> None)
                     |- BatList.sort LH.depth_cmp) v in
          let nstmts, left = List.fold_left (fun (stmts, left) (i, s) ->
              (* Prepend definitions with a smaller
                 to the current stmts. That is, definitions not
                 depending on the current stmt. *)
              let prepend = (BatList.take_while (LH.prependable i)
                             |- BatList.sort LH.cmp_order
                             |- BatList.map LH.get_def) left in
              dprintf "Going to prepend: %s" (Print.list_to_string
                Pp.ssa_stmt_to_string prepend);
              let left = BatList.drop (List.length prepend) left in
              (stmts @ prepend @ [s], left)
            ) ([], defs ) stmts in
          let append = List.map LH.get_def left in
          dprintf "Going to append: %s"
            (Print.list_to_string Pp.ssa_stmt_to_string append);
          (* Finally, update the BB with the new definitions. *)
          C.set_stmts cfg v (nstmts @ append)
        ) cfg cfg
  end
end

let make_pass = function
  | `StartAst -> Pass ( Ast ( Transform Ast_passes.start))
  | `CollectCalls -> Pass (Ast (Analysis Ast_passes.collect_calls))
  | `VerifyNoCalls -> Pass (Ast (Analysis Ast_passes.verify_no_calls))
  | `ReplaceCallStmts -> Pass ( Ast ( Transform Ast_passes.replace_call_stmts))
  | `RemoveHaltStmts -> Pass (Ast (Transform Ast_passes.remove_halt_stmts))
  | `RemoveSpecialStmts -> Pass (Ast (Transform Ast_passes.remove_special_stmts))
  | `CoerceProgPass -> Pass (Ast (Transform Ast_passes.coerce_prog))
  | `BuildAddrmap -> Pass (AstCfg (Analysis Astcfg_passes.addrmap))
  | `RemoveIndirect -> Pass (AstCfg (Transform Astcfg_passes.remove_indirect))
  | `PruneUnreachable1 -> Pass (AstCfg (Transform Astcfg_passes.prune_unreachable1))
  | `PruneUnreachable2 -> Pass (AstCfg (Transform Astcfg_passes.prune_unreachable2))
  | `ForceSingleExit -> Pass (AstCfg (Transform Astcfg_passes.force_single_exit))
  | `CoalesceCfg1 -> Pass (AstCfg (Transform Astcfg_passes.coalesce_ast1))
  | `CoalesceCfg2 -> Pass (AstCfg (Transform Astcfg_passes.coalesce_ast2))
  | `CoalesceCfg3 -> Pass (AstCfg (Transform Astcfg_passes.coalesce_ast3))
  | `SubregLiveness -> Pass (AstCfg (Transform Astcfg_passes.subreg_liveness))
  | `BreakAfterCalls1 -> Pass (AstCfg (Transform Astcfg_passes.break_after_calls1))
  | `BreakAfterCalls2 -> Pass (AstCfg (Transform Astcfg_passes.break_after_calls2))
  | `StartSsa -> Pass ( SsaCfg ( Transform Ssa_passes.start))
  | `RemoveNoreturnEdges -> Pass (SsaCfg (Transform Ssa_passes.remove_noreturn_edges))
  | `MarkEaxLiveout -> Pass (SsaCfg (Transform Ssa_passes.mark_eax_liveout))
  | `PhiPropagationPass -> Pass (SsaCfg (Transform Ssa_passes.phi_propagation))
  | `DropNopBBs1 -> Pass (SsaCfg (Transform Ssa_passes.drop_nop_bbs1))
  | `DropNopBBs2 -> Pass (SsaCfg (Transform Ssa_passes.drop_nop_bbs2))
  | `BapSsaSimplifications1 -> Pass (SsaCfg (Transform Ssa_passes.bap_simplifications1))
  | `BapSsaSimplifications2 -> Pass (SsaCfg (Transform Ssa_passes.bap_simplifications2))
  | `BapSsaSimplifications3 -> Pass (SsaCfg (Transform Ssa_passes.bap_simplifications3))
  | `MarkStoresLiveout -> Pass (SsaCfg (Transform Ssa_passes.mark_stores_liveout))
  | `DeadCodeElimination1 -> Pass (SsaCfg (Transform Ssa_passes.dce1))
  | `DeadCodeElimination2 -> Pass (SsaCfg (Transform Ssa_passes.dce2))
  | `CoalesceSsa1 -> Pass (SsaCfg (Transform Ssa_passes.coalesce_ssa1))
  | `CoalesceSsa2 -> Pass (SsaCfg (Transform Ssa_passes.coalesce_ssa2))
  | `ComputeDataDependencies -> Pass (SsaCfg (Analysis Ssa_passes.compute_dd))
  | `ComputeFunctionInputs -> Pass (SsaCfg (Analysis Ssa_passes.compute_function_inputs))
  | `NormalizeCjmps -> Pass (SsaCfg (Transform Ssa_passes.normalize_cjmp_cond))
  | `RewriteLoadStores -> Pass (SsaCfg (Transform Ssa_passes.rewrite_loadstores))
  | `ComputeCollapsibleLoads -> Pass (SsaCfg (Analysis Ssa_passes.compute_collapsible_loads))
  | `CollapseLoads -> Pass (SsaCfg (Transform Ssa_passes.collapse_loads))
  | `PartialRedundantDefinitionElimination -> Pass (SsaCfg (Transform Ssa_passes.prde))
  | `Buoyancy -> Pass (SsaCfg (Transform Ssa_passes.buoyancy))

module FuncHashtbl = Function_info.Hashtbl

let fdir func =
  let open Function_info.Function in
  let fname = symbols_to_str func in
  (*
   * The directory name starts with the function name for easy
   * completion; we make sure it ends with the function address
   * (so that every dirname is unique). The full function name
   * is stored inside that function's directory (/function_name).
   *
   * The whole point of this exercise is to avoid going over the
   * path component limit of NAME_MAX bytes.
   *)
  let name_max = 250 in (* NAME_MAX is 255 on every unix I know -- agg *)
  let addr = match begin_address func with
    | Some x -> Printf.sprintf "%Lx" x
    | None -> failwith "No addr!"
  in
  let fnamelen = String.length fname in
  let addrlen = (String.length addr) + 1 in
  let fname =
    if fnamelen > (name_max - addrlen) then
      StringLabels.sub fname ~pos:0 ~len:(name_max - addrlen)
    else
      fname
  in
  let dir = Printf.sprintf "%s-%s" fname addr in
  assert((String.length dir) <= name_max);
  dir

let fold_vertex f cg acc =
  let acc = ref acc in
  Callgraph.Callgraph.iter_vertex (fun func ->
      acc := f func !acc) cg;
  !acc

let map_vertex f cg =
  let ncg = Callgraph.Callgraph.empty in
  let old2newv = FuncHashtbl.create (Callgraph.Callgraph.nb_vertex cg) in
  let ncg = fold_vertex (fun func acc ->
      let func' = f func in
      FuncHashtbl.add old2newv func func';
      Callgraph.Callgraph.add_vertex acc func') cg ncg in
  let acc = ref ncg in
  Callgraph.Callgraph.iter_edges_e (fun edge ->
      let call = Callgraph.Callgraph.E.label edge in
      let src = Callgraph.Callgraph.E.src edge in
      let dst = Callgraph.Callgraph.E.dst edge in
      let src' = FuncHashtbl.find old2newv src in
      let dst' = FuncHashtbl.find old2newv dst in
      acc := Callgraph.Callgraph.add_edge_e !acc (src', call, dst')) cg;
  !acc

let apply_ast_pass ?keypref:(keypref=None) pass ctx stmts =
  match pass with
  | Pass (Ast (Transform p)) ->
    dprintf "--- TRANSFORM START (ast): %s --- %s" p#name Print.fo;
    let nstmts = p#transform ctx stmts in
    dprintf "--- TRANSFORM END (ast): %s --- %s" p#name Print.fc;
    ignore(match keypref with
        | None -> ()
        | Some keypref ->
          let key = Printf.sprintf "%s/%02d-after-%s.ast" keypref ctx.idx p#name in
          Outdir.with_file_out key (fun oc ->
              let pp = new Pp.pp_oc oc in
              pp#ast_program nstmts;
              pp#close));
    ({ctx with idx = ctx.idx + 1;}, nstmts)
  | Pass (Ast (Analysis p)) ->
    dprintf "--- ANALYSIS START (ast): %s --- %s" p#name Print.fo;
    let nctx = p#analyze ctx stmts in
    dprintf "--- ANALYSIS END (ast): %s --- %s" p#name Print.fc;
    (nctx, stmts)
  | _ -> failwith "Expected an AST transform pass!"

let getfunc = function
  | Function_info.Function f -> f
  | f -> failwith (Printf.sprintf "getfunc: %s" (Function_info.to_string f))

let process_ast_pipeline ~func_filter ?(keypref=None) arch cg pipeline =
  let htbl = FuncHashtbl.create (Callgraph.Callgraph.nb_vertex cg) in
  let cg' = map_vertex (fun func ->
      let fnames = Function_info.symbols func in
      let fdesc = Function_info.to_string func in
      dprintf "AST pipeline for func %s" fdesc;
      try
        let blacklisted = BatList.Exceptionless.find Symbols.sym_is_blacklist
            fnames
        in
        ignore(match blacklisted with
            | Some sym ->
              let str = Printf.sprintf "symbol %s is blacklisted" sym in
              raise (Confusing_function str);
            | None -> ());
        match func with
        | Function_info.Function fi when func_filter func ->
          let _stmts = BatOption.get (Function_info.stmts func) in
          let _ctx = {
            arch = arch;
            function_information = [Function_info.Function fi]; (* XXX: not applicable to ast/astcfg *)
            info = [];
            idx = 0;
          } in
          let keypref = BatOption.map (fun p ->
              Printf.sprintf "%s/%s" p (fdir (getfunc func))) keypref
          in
          let (fctx, stmts) = List.fold_left (fun (ctx, stmts) pass ->
              apply_ast_pass ~keypref pass ctx stmts) (_ctx, _stmts) pipeline
          in
          FuncHashtbl.replace htbl func (Some fctx);
          Function_info.set_stmts func stmts
        | _ ->
          FuncHashtbl.replace htbl func None;
          func
      with Confusing_function msg ->
        wprintf "(AST) Could not analyze function %s: %s" fdesc msg;
        let nfunc = Function_info.set_attr func (Func_attr.Confusing msg) in
        FuncHashtbl.remove htbl func;
        FuncHashtbl.add htbl nfunc None;
        nfunc
    ) cg in
  (htbl, cg')

let apply_astcfg_pass ?keypref:(keypref=None) pass ctx cfg =
  match pass with
  | Pass (AstCfg (Transform p)) ->
    dprintf "--- TRANSFORM START (astcfg): %s --- %s" p#name Print.fo;
    let ncfg = p#transform ctx cfg in
    dprintf "--- TRANSFORM END (astcfg): %s --- %s" p#name Print.fc;
    ignore(match keypref with
        | None -> ()
        | Some keypref ->
          let key = Printf.sprintf "%s/%02d-after-%s.ast.dot" keypref ctx.idx p#name in
          Outdir.with_file_out key (fun oc ->
              Graph_dump.output_ast oc ncfg));
    ({ctx with idx = ctx.idx + 1;}, ncfg)
  | Pass (AstCfg (Analysis p)) ->
    dprintf "--- ANALYSIS START (astcfg): %s --- %s" p#name Print.fo;
    let nctx = p#analyze ctx cfg in
    dprintf "--- ANALYSIS END (astcfg): %s --- %s" p#name Print.fc;
    (nctx, cfg)
  | _ -> failwith "Expected an ASTCFG transform pass!"

let process_astcfg_pipeline ~func_filter ?keypref:(keypref=None) cg htbl pipeline =
  let cg' = map_vertex (fun func ->
      let fdesc = Function_info.to_string func in
      dprintf "ASTCFG pipeline for func %s" fdesc;
      try
        match FuncHashtbl.find htbl func with
        | Some _ctx when func_filter func ->
          let keypref = BatOption.map (fun p ->
              Printf.sprintf "%s/%s" p (fdir (getfunc func))) keypref
          in
          let _cfg = BatOption.get (Function_info.astcfg func) in
          let (fctx, ncfg) = List.fold_left (fun (ctx, cfg) pass ->
              let ctx, cfg = apply_astcfg_pass ~keypref pass ctx cfg in
              ignore(
                try
                  ignore(Cfg.AST.find_vertex cfg Cfg.BB_Indirect);
                  failwith "got BB_Indirect"
                with Not_found -> ());
              (ctx, cfg)
            ) (_ctx, _cfg) pipeline
          in
          FuncHashtbl.replace htbl func (Some fctx);
          Function_info.set_astcfg func ncfg
        | Some _
        | None -> func
      with Confusing_function msg ->
        wprintf "(ASTCFG) Could not analyze function %s: %s" fdesc msg;
        let nfunc = Function_info.set_attr func (Func_attr.Confusing msg) in
        FuncHashtbl.remove htbl func;
        FuncHashtbl.add htbl nfunc None;
        nfunc
    ) cg in
  (htbl, cg')


exception Unsupported_pass_config
let apply_ssa_cfg_pass ~pipeline_name ?keypref:(keypref=None) ?(mempref=None)
    ctx fnames cfg pass =
  match pass with
  | Pass (SsaCfg (Transform p)) ->
    let do_transform () =
      dprintf "--- TRANSFORM START (ssa): [%s:%s] [%s] --- %s" pipeline_name
        p#name fnames Print.fo;
      let ncfg = p#transform ctx cfg in
      dprintf "--- TRANSFORM END (ssa): [%s:%s] [%s] --- %s" pipeline_name
        p#name fnames Print.fc;
      ignore(match keypref with
          | None -> ()
          | Some keypref ->
            let key = Printf.sprintf "%s/%02d-after-%s.ssa.dot" keypref ctx.idx p#name in
            Outdir.with_file_out key (fun oc ->
                Graph_dump.output_ssa oc ncfg));
      ignore(match mempref with
          | None -> ()
          | Some key ->
            Outdir.with_file_out key (fun oc ->
                Printf.fprintf oc "after-%s: %d\n%!" p#name
                  ((Gc.stat ()).Gc.heap_words * 4)));
      ({ctx with idx = ctx.idx + 1;}, ncfg)
    in
    let b = new Perfacc.bench p#name in
    b#start fnames;
    Misc.finally b#stop do_transform ()
  | Pass (SsaCfg (Analysis p)) ->
    let do_analysis () =
      dprintf "--- ANALYSIS START (ssa): %s --- %s" p#name Print.fo;
      let nctx = p#analyze ctx cfg in
      dprintf "--- ANALYSIS END (ssa): %s --- %s" p#name Print.fc;
      ignore(match mempref with
          | None -> ()
          | Some key ->
            Outdir.with_file_out key (fun oc ->
                Printf.fprintf oc "after-%s: %d\n%!" p#name
                  ((Gc.stat ()).Gc.heap_words * 4)));
      (nctx, cfg)
    in
    let b = new Perfacc.bench p#name in
    b#start fnames;
    Misc.finally b#stop do_analysis ()
  | Pass _ -> raise Unsupported_pass_config

let process_ssa_pipeline ~func_filter ?keypref:(keypref=None) htbl cg pipeline =
  let pipeline_name = "ssa-pipeline" in
  let fi_list = BatList.of_enum (FuncHashtbl.keys htbl) in

  let apply_pipeline_to_func ctx func =
    (*    dprintf "apply_pipeline_to_func: entry\n";*)
    let fnames = Function_info.symbols_to_str func in
    let fdesc = Function_info.to_string func in
    dprintf "SSA pipeline for func %s" fdesc;
    try
      let cfg = BatOption.get (Function_info.ssacfg func) in
        (*
         * XXX: hack hack hack, big refactor session in progress, can't deal
         * with this too ATM.
         *)
      let ctx' = {ctx with function_information = fi_list} in
      let keypref = BatOption.map (fun p ->
          Printf.sprintf "%s/%s" p (fdir (getfunc func))) keypref
      in
      let mempref = BatOption.map (fun p ->
          Printf.sprintf "%s/ssa_pipeline" p
        ) keypref
      in
      let nctx, ncfg = List.fold_left (fun (ctx, cfg) pass ->
          apply_ssa_cfg_pass ~pipeline_name ~keypref ~mempref
            ctx fnames cfg pass
        ) (ctx', cfg) pipeline
      in
      (nctx, Function_info.set_ssacfg func ncfg)
    with Confusing_function msg ->
      wprintf "(SSA) Could not analyze function %s: %s" fdesc msg;
      let nfunc = Function_info.set_attr func (Func_attr.Confusing msg) in
      (ctx, nfunc)
  in
  let module EP = Embarassingly_parallel in
  let do_work (ctx, func) =
    (*    dprintf "do_work: entry\n"; *)
    let b = new Perfacc.bench "SSA pipeline" in
    (*    dprintf "do_work: after new bench\n";*)
    let do_pipeline () =
      match ctx with
      | Some ctx ->
        (*          dprintf "do_pipeline: before apply_pipeline_to_func\n";*)
        let nctx, nfunc = apply_pipeline_to_func ctx func in
        BatDynArray.iter (fun x ->
            dprintf "pipeline child: %s" x#get_name) (b#get_stats ())#get_children;

        (Some nctx, nfunc)
      | None ->
        (None, func)
    in
    let funcstr = Function_info.to_string func in
    let str = Marshal.to_string func [Marshal.Closures] in
    dprintf "MarshalBefore %s: %d bytes\n" funcstr (String.length str);
    b#start (Function_info.symbols_to_str func);
    let nctx, nfunc = Misc.finally b#stop do_pipeline () in
    let ret = {EP.ret = (nctx, nfunc); EP.bench = Marshal.to_string b [Marshal.Closures]} in
    let str = Marshal.to_string ret [Marshal.Closures] in
    let funcstr = Function_info.to_string nfunc in
    dprintf "Marshal %s: %d bytes\n" funcstr (String.length str);
    ret
  in
(*
  let workfunc func =
    do_work (
  in
  let update_accumulator acc index transformed_func =
  in
  let htbl = EP.fold_over workfunc update_accumulator htbl in
*)
  let do_batch htbl cg funcs =
    let results = match EP.map_list do_work funcs with
      | _,  (x :: _ as ewbs) ->
        let str = EP.exns_with_bts_to_string ewbs in
        Printf.eprintf "Got %d exceptions from workers:\n%s\n"
          (List.length ewbs) str;
        failwith "XXX: got exceptions"
      | rs, [] -> rs
    in
    List.iter (fun (ctx, func) -> FuncHashtbl.replace htbl func ctx) results;
    let mapping = FuncHashtbl.create (Callgraph.Callgraph.nb_vertex cg) in
    BatList.iter2 (fun (_, func) (_, nfunc) ->
        FuncHashtbl.add mapping func nfunc) funcs results;
    try
      (htbl, map_vertex (fun func ->
           (* The function might validly not be in this batch *)
           match FuncHashtbl.find_option mapping func with
           | Some nfunc -> nfunc
           | None -> func) cg)
    with Not_found -> failwith "Function not found in mapping"
  in
  let batchsize = 12 in
  let rec process_in_batches htbl cg funcs =
    match funcs with
    | [] -> (htbl, cg)
    | _ -> begin
        let funcs, remaining =
          match BatList.Exceptionless.split_at batchsize funcs with
          | `Ok x -> x
          | `Invalid_argument _ -> (funcs, [])
        in
        let htbl, cg = do_batch htbl cg funcs in
        process_in_batches htbl cg remaining
      end
  in
  let funcs =
    try
      fold_vertex (fun func acc ->
          if func_filter func then
            (FuncHashtbl.find htbl func, func) :: acc
          else
            acc
        ) cg []
    with Not_found -> failwith "No context for func? huh?"
  in
  process_in_batches htbl cg funcs
