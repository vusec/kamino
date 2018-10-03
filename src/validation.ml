module D = Debug.Make(struct let name = "Validation" and default=`Debug end)
open D

open BatPervasives

module VC = Var_convenience
module BC = Big_int_convenience
module C = Ssa_ext_convenience

module BatPair = struct
    let map f (a, b) = (f a, f b)
end

let ssa_ext_esp =
  let d = Asmir.decls_for_arch Asmir.arch_i386 (* XXX *) in
  let esp = List.find (fun v -> Var.name v = "R_ESP") d in
  Ssa_ext.of_var esp

module type Validator
=
sig
  type subgraph

  val validate : subgraph -> (unit, string) BatResult.t
end

module MakeSearch(Strategy:Symbeval_search.Strategy) (Symbolic:Symbeval_search.Symb) =
struct
  module S = Strategy(Symbolic)

  let rec search states final_states path =
    match S.pop_next states with
    | None -> final_states
    | Some ((state, data), states) ->
	    let (new_states, final_states) =
	      try
          (Symbolic.eval state, final_states)
        with
	      | Symbolic.Halted(halt_value, state) ->
          begin
            match halt_value with
            | Some (Symbeval.Symbolic exp) ->
              begin
                match exp with
                | Ast.Int (n,_) ->
                  ([], (n, state, (state.Symbeval.pc) :: path) :: final_states)
                | _ -> ([], final_states)
              end
            | _ -> failwith "Didn't get a halt value"
          end
	      | Symbolic.AssertFailed {Symbeval.pc=pc} ->
	        wprintf "failed assertion at %Ld\n" pc;
	        ([], final_states)  (* try other branches *)
	    in
      let q = S.add_next_states states state data new_states in
	    search q final_states ((state.Symbeval.pc) :: path)

  let eval_ast_prog initdata prog =
    let ctx = Symbolic.init prog in
    let final_states = search (S.start_at ctx initdata) [] [] in
    final_states
end

module GuidedMaxRepeatDFS (Symbolic:Symbeval_search.Symb) =
struct
  type myctx = Symbolic.myctx
  type data = int Symbeval_search.EdgeMap.t
  type initdata = int * (Type.addr list)
  type t = (myctx * data) list * (int * (Type.addr list))
  let start_at state (max_repeat, skip_list) =
    ([(state, Symbeval_search.EdgeMap.empty)], (max_repeat, skip_list))
  let pop_next  = function
    | (next::rest, config) -> Some (next, (rest, config))
    | ([], _) -> None
  let add_next_states (states, (max_repeat,skip_list)) current_state edges new_states  =
    let skip state = List.exists (fun s ->
        s = state.Symbeval.pc) skip_list in
    match new_states with
    | [] -> (states, (max_repeat, skip_list))
    | [new_state] ->
      if skip new_state
      then (states, (max_repeat, skip_list))
      else ((new_state, edges)::states, (max_repeat, skip_list))
    | _ ->
	    let add_edge new_state =
       if skip new_state
       then None
       else
         begin
	         let edge = (current_state.Symbeval.pc, new_state.Symbeval.pc) in
	         let count = try Symbeval_search.EdgeMap.find edge edges with Not_found -> 0 in
	         if count >= max_repeat then None
	         else Some(new_state, Symbeval_search.EdgeMap.add edge (count+1) edges)
         end
	    in
	    let new_states' = BatList.filter_map add_edge new_states in
	    (new_states' @ states, (max_repeat, skip_list))
end

module SymbolicSearch = MakeSearch (GuidedMaxRepeatDFS) (Symbeval_search.FastSymb)

module SymbValidator (BBMgr:Bb_cluster.BBClusterManagerSig) (Algorithm : Comparator.AlgoSig with type bbcluster_type := BBMgr.t and type bbcluster_key := Bb_cluster.ClusterHashtbl.key) : Validator
  with type subgraph = Algorithm.subgraph
=
struct
  module Subgraph = Algorithm.Subgraph
  type subgraph = Subgraph.t
  module Symbolic = Symbeval.Symbolic

  exception Unsatisfiable
  exception Cannot_validate of string

  let pred_to_str = Pp.ast_exp_to_string
  let print_pred pred = dprintf "%s" (pred_to_str pred)

  let normalize_pred = Misc.normalize_string (Str.regexp "R_[A-Z]+")

  let bb2n v =
    match Cfg.AST.G.V.label v with
    | Cfg.BB n -> n + 5
    | Cfg.BB_Entry -> 0
    | Cfg.BB_Exit -> 1
    | Cfg.BB_Indirect -> 2
    | Cfg.BB_Error -> failwith "BB_Error in a matched subgraph"

  let n2bb = function
    | 0 -> Cfg.BB_Entry
    | 1 -> Cfg.BB_Exit
    | 2 -> Cfg.BB_Indirect
    | n -> Cfg.BB (n - 5)

  (*
   * The function we found a match in might legitimately be jumping to
   * BB_Error (because of a decoding error or, more likely, because we
   * weren't able to generate a TF for a BB and consequently substituted
   * it with BB_Error). We can't allow execution to jump there, so
   * implement the following algorithm (in comments).
   *)
  let rm_bberr cfg =
    let module C = Cfg.AST in
    let rm_final_jump cfg v =
      dprintf "Removing final jump for %s" (C.v2s v);
      let n = bb2n v in
      let hlt = Ast.Halt (Ast.Int (Big_int_Z.big_int_of_int n,
                                   Type.Reg 4), []) in
      let stmts = C.get_stmts cfg v in
      let rstmts = List.rev stmts in
      let stmts, got_jmp = List.fold_left (fun (acc, found) s ->
        match s with
        | Ast.Jmp _
        | Ast.CJmp _ as jmp ->
          if found then
            (jmp :: acc, found)
          else
            (hlt :: acc, true)
        | _ ->
          (s :: acc, found)
      ) ([], false) rstmts
      in
      (* If we got here, there must have been a {c,}jmp! *)
      assert (got_jmp);
      C.set_stmts cfg v stmts
    in
    try
      let bberr = C.find_vertex cfg Cfg.BB_Error in
      dprintf "Found BB_Error";
      (*
       * 1. For all predecessors that explicitly jump to BB_Error (as
       * opposed to falling through, which might happen  as a result of
       * optimizations such as jump threading), remove the last jump
       * statement encountered and replace it with an appropriate halt.
       *)
      let cfg = C.G.fold_pred_e (fun edge g ->
        match C.G.E.label edge with
        | None -> (* fall-through edge, nothing to do *)
          dprintf "Fallthrough edge";
          (*
           * 2. Fall-through edges to BB_Error will have an out-degree
           * of zero after step 3, so we can rely on our caller to add
           * halts to them as appropriate.
           *)
          g
        | Some _ ->
          rm_final_jump g (C.G.E.src edge)) cfg bberr cfg
      in
      (* 3. Remove BB_Error itself from the CFG. *)
      C.remove_vertex cfg bberr
    with Not_found -> cfg

  let cfg_add_halts cfg =
    let module G = Cfg.AST.G in
    let cfg = rm_bberr cfg in
    let maybe_add_hlt v g =
      match G.out_degree g v with
      | 0 ->
	      let stmts = Cfg.AST.get_stmts g v in
	      let n = bb2n v in
	      (* We need to be able to lookup the BB just by looking at the
	         halt value of a final state from Symbeval
	         *)
	     let hlt = Ast.Halt (Ast.Int (Big_int_Z.big_int_of_int n, Type.Reg 4), []) in
       (* We add a halt before each return and after the last instruction.
          If we identify a return, we halt just before that.
          Otherwise we halt after the last instruction is executed.
       *)
       let stmts' = List.append (List.fold_left (fun acc stmt ->
           if Misc.is_ret Asmir.arch_i386 stmt
           then acc @ [hlt; stmt]
           else acc @ [stmt]
         ) [] stmts) [hlt] in
	      Cfg.AST.set_stmts g v stmts'
      | _ -> g
    in
    G.fold_vertex maybe_add_hlt cfg cfg

  let symbeval ?(max_repeat=7) ?(skip_list=[]) stmts =
    let prev_varnums = VC.enable_varnums in
    dprintf "Skiplist:\n%s" (Print.list_to_string Int64.to_string skip_list);
    dprintf "Executing\n\t%s" (Print.list_to_string ~sep:"\n\t" Pp.ast_stmt_to_string stmts);
    VC.restore_varnums prev_varnums;
    SymbolicSearch.eval_ast_prog (max_repeat,skip_list) stmts

  (*
   * Rewrite exp & true -> exp, we always get those in the path constraints.
   * XXX: But they shouldn't really matter for comparison purposes,
   * this might just be wasting CPU time.
   *)
  let optimize_formula exp =
    let rec aux = function
      | Ast.BinOp (Type.OR, Ast.Int (n, Type.Reg 1), rest)
      | Ast.BinOp (Type.OR, rest, Ast.Int (n, Type.Reg 1)) as e ->
        if BC.bi_is_zero n
        then aux rest
        else e
      | Ast.BinOp (Type.AND, Ast.Int (n, Type.Reg 1), rest)
      | Ast.BinOp (Type.AND, rest, Ast.Int (n, Type.Reg 1)) as e ->
	      if BC.bi_is_one n
        then aux rest
        else e
      | Ast.BinOp (Type.AND, lhs, rhs) ->
        Ast.BinOp (Type.AND, aux lhs, aux rhs)
      | Ast.BinOp (Type.OR, lhs, rhs) ->
        Ast.BinOp (Type.OR, aux lhs, aux rhs)
      | _ as e -> e
    in
    let exp' = aux exp in
    exp'

  let reverse_hashtbl tbl =
    BatHashtbl.fold (fun k v acc ->
        if BatHashtbl.mem acc v
        then (BatHashtbl.replace acc v (k :: (BatHashtbl.find acc v)); acc)
        else (BatHashtbl.add acc v [k]; acc)
      ) tbl (BatHashtbl.create (BatHashtbl.length tbl))

  let pair_states_by_path lstates rstates =
    Pp.many_parens := true;
    let print_state st =
      let pred = optimize_formula st.Symbeval.pred in
      print_pred pred;
      Symbolic.print_values st.Symbeval.delta
    in

    dprintf "Enter states left";
    List.iter (fun (_,state,_) -> print_state state) lstates;
    dprintf "Enter states right";
    List.iter (fun (_,state,_) -> print_state state) rstates;

    let expected_mapping = BatHashtbl.create 10 in
    List.iter (fun final_state ->
        let (_,state,(actual,expected)) = final_state in
        let actual = Print.list_to_string Cfg.bbid_to_string actual in
        let expected = Print.list_to_string Cfg.bbid_to_string expected in
        dprintf "Adding expected path %s for %s" expected actual;
        BatHashtbl.add expected_mapping expected final_state) lstates;
    let pairs = List.map (fun final_state ->
        let (_, state, (actual,expected)) = final_state in
        let actual = Print.list_to_string Cfg.bbid_to_string actual in
        let expected = Print.list_to_string Cfg.bbid_to_string expected in
        dprintf "Looking to pair %s with expected %s" actual expected;
        match Misc.bathashtbl_find_option expected_mapping actual with
        | None -> let reason = Printf.sprintf "Couldn't find match for %s\n" actual in
                  raise (Cannot_validate reason)
        | Some lstate ->
	        dprintf "PAIRED %s" actual;
	        (lstate, final_state)
          ) rstates in
    pairs


  let verify_equivalence subg (lstate, rstate) =
    let module C = Ssa_ext_convenience in
    (* 1. Obtain the BBs corresponding to the final states *)
    let (ln, lst, _) = lstate in
    let (rn, rst, _) = rstate in
    let lv = n2bb (Big_int_Z.int_of_big_int ln) in
    let rv = n2bb (Big_int_Z.int_of_big_int rn) in
    (* 2. Check the subgraph for a match between these BBs *)
    match Subgraph.includes_bbids subg (lv, rv) with
    | None ->
      raise (Cannot_validate
               (Printf.sprintf "Final BBs %s and %s, not paired in matching subgraph!"
                  (Cfg.bbid_to_string lv) (Cfg.bbid_to_string rv)
               )
      )
    | Some bbcmp ->
      (* 3. Obtain the assumptions *)
      let mi = Subgraph.BBCmp.match_info bbcmp in
      let me = mi.Comparator.matched_direct in
      (*
         We take the IN assumptions of the entry BB in the execution path.
         OUT assumptions are already available in the final BB due to propagation.
      *)
      let path_from_final_state (_,_,(path,_)) = path in
      let entry_bbs,_ = Subgraph.collect_edge_bbs subg in
      let entry_bbs_tbl = BatHashtbl.create (List.length entry_bbs) in
      List.iter (fun bbcmp ->
          let lhs_bb,_ = Subgraph.BBCmp.bbp bbcmp in
          let bb_id = lhs_bb.Bb.id in
          let in_asxs = (Subgraph.BBCmp.match_info bbcmp).Comparator.matched_direct.Comparator.in_asxs in
          BatHashtbl.add entry_bbs_tbl bb_id in_asxs
        ) entry_bbs;
      let in_asxs = List.fold_left (fun asxs bb_id ->
          match asxs with
          | None ->
            if BatHashtbl.mem entry_bbs_tbl bb_id
            then Some (BatHashtbl.find entry_bbs_tbl bb_id)
            else None
          | Some _ -> asxs
        ) None (path_from_final_state lstate) in
      match in_asxs with
      | Some in_asxs ->
        let esp = ssa_ext_esp in
        let in_asxs = match Assumptions.add_assumption in_asxs ([esp], [esp]) with
          | BatResult.Ok in_asxs -> in_asxs
          | BatResult.Bad str ->
            failwith str
        in
        begin
          let out_asxs = me.Comparator.out_asxs in
          let predicate_from_final_state (_,state,_) = state.Symbeval.pred in
          dprintf "Final state (%s, %s):\nPath constraint: %s\nPath: %s\nIN: %s\nOUT: %s"
	          (Cfg.bbid_to_string lv) (Cfg.bbid_to_string rv)
	          (pred_to_str (predicate_from_final_state lstate))
            (Print.list_to_string Cfg.bbid_to_string (path_from_final_state lstate))
            (Assumptions.to_string in_asxs)
	          (Assumptions.to_string out_asxs);
          (* 4. Make sure the assumptions are unique to prevent invalid equivalences in
             the final formula
             (e.g., if both sides use the same register for a different purpose). *)
          let in_asxs', l_in_map, r_in_map = Assumptions.uniqify_asxs in_asxs in
          let out_asxs', l_out_map, r_out_map = Assumptions.uniqify_asxs out_asxs in
          let remap_tbl key value map =
            BatHashtbl.fold (fun k v acc ->
                BatHashtbl.add acc (key k) (value v);
                acc
              ) map (BatHashtbl.create (BatHashtbl.length map))
          in
          (* Remap the mappings because the AST uses Var.t instead of Variable.t *)
          let l_in_map', r_in_map' = BatPair.map
              (remap_tbl C.Variable.var C.Variable.var) (l_in_map, r_in_map) in
          let l_out_map', r_out_map' = BatPair.map
              (remap_tbl C.Variable.var C.Variable.var) (l_out_map, r_out_map) in
          (* Remap the variables by their name *)
          let remap_inputs map formula =
            let find_by_name v =
              let key = BatEnum.Exceptionless.find (fun k ->
                  (Var.name k) = (Var.name v)
                ) (BatHashtbl.keys map) in
              match key with
              | Some k -> Some (BatHashtbl.find map k)
              | None -> None
            in
            let visitor = object(self)
              inherit Ast_visitor.nop

              method visit_exp = function
                | Ast.Load (arr, Ast.BinOp (_, Ast.Var base, Ast.Int (offset,typ)), endian, t) ->
                  begin
                  let ary = BatEnum.Exceptionless.find (fun k ->
                      if Var_convenience.Array.is_array k
                      then
                        begin
                          if (Var_convenience.Array.base_reg k) = base
                          then
                            begin
                              dprintf "Checking offset %s" (Big_int_Z.string_of_big_int offset);
                              Interval.Big_int.contains (Var_convenience.Array.bounds k) offset
                              end
                          else false
                        end
                      else false) (BatHashtbl.keys map)
                  in
                  match ary with
                  | Some v -> dprintf "Replacing load with %s" (Pp.var_to_string v);
                  Type.ChangeToAndDoChildren (Ast.Load (Ast.Var v, Ast.Int (offset, typ), endian, t))
                  | None -> Type.DoChildren
                              end
                | _ -> Type.DoChildren

              method visit_rvar v =
                match find_by_name v with
                | Some v' ->
                  Type.ChangeTo v'
                | None ->
                  let v' = C.Variable.of_var v in
                  if C.Variable.is_mem v' || C.Variable.is_temp v'
                  then Type.DoChildren
                  else begin
                    failwith (Printf.sprintf "Unexpected input %s!\nPossible inputs: %s\nFormula: %s"
                                   (Pp.var_to_string v)
                                   (Print.enum_to_string Pp.var_to_string (BatHashtbl.keys map))
                                   (Pp.ast_exp_to_string formula))
                  end
            end
            in
            Ast_visitor.exp_accept visitor (Flatten_mem.flatten_loads formula)
          in
          (* Find the definitions relevant to the OUT assumptions*)
          let delta_to_formula {Symbeval.delta = d} in_map out_map =
            let find_by_name v map =
              let key = BatEnum.Exceptionless.find (fun k ->
                  (Var.name k) = (Var.name v)
                ) (BatHashtbl.keys map) in
              match key with
              | Some k -> Some (BatHashtbl.find map k)
              | None -> None
            in
            Var.VarHash.fold (fun v def f ->
                match find_by_name v out_map with
                | Some v' ->
                  begin
                    match def with
                    | Symbeval.Symbolic exp ->
                      Ast.exp_and f (Ast.exp_eq (Ast.Var v') (remap_inputs in_map exp))
                    | Symbeval.ConcreteMem _ -> failwith "Expected a symbolic value!"
                  end
                | None -> f
              ) d Ast.exp_true
          in
          (* 5. Generate the formula to validate. *)
          let formula =
            optimize_formula
              (Ast.exp_and
                 (Ast.exp_and
                    (Ast.exp_and (Assumptions.to_formula in_asxs')
                       (Assumptions.to_formula out_asxs'))
                    (Ast.exp_and
                       (* XXX what about index variables in loads, which could be part of
                          the IN asxs. *)
                       (delta_to_formula lst l_in_map' l_out_map')
                       (delta_to_formula rst r_in_map' r_out_map')))
                 (Ast.exp_and
                    (remap_inputs l_in_map' (predicate_from_final_state lstate) )
                    (remap_inputs r_in_map' (predicate_from_final_state rstate))))
          in
          dprintf "Formula:\n%s" (Pp.ast_exp_to_string formula);
          let out = Pervasives.open_out ("formula_" ^
                                           (string_of_int
                                              (int_of_float (Unix.time ()))) ^".stp") in
          let pp = new Stp.pp_oc out in
          pp#valid_ast_exp (Ast.exp_not formula);
          pp#flush;
          pp#close;
          Pervasives.flush out;
          Pervasives.close_out out;
          let is_satisfiable = Solver.CVC3Exec.is_satisfiable formula in
          if is_satisfiable then dprintf "The formula is satisfiable!"
          else
            begin
              dprintf "The formula is not satisfiable!";
              raise Unsatisfiable
            end
        end
      | None ->
        raise (Cannot_validate "Cannot find IN assumptions for execution trace!")

  let rec find_labels = function
    | [] -> (None, None)
    | Ast.Label (l,_) :: rest ->
      begin
        (* Check if the label is follow by another label.
           It is a common pattern that an address label is follow by a name
           label. Both types are used in jmps.
        *)
        match rest with
        | Ast.Label (l',_) :: _ ->
          (Some l, Some l')
        | _ -> (Some l, None)
      end
    | _ :: rest -> find_labels rest

  (* XXX: move this to an appropiate module *)
  let only_halt_or_comment stmts =
    List.fold_left (fun acc stmt ->
      match stmt with
      | Ast.Halt _ -> acc
      | Ast.Comment _ -> acc
      | _ -> false
    ) true stmts

  (* XXX: Gross hack fixing BB id mismatches between the CFG generated from
     the unmodified AST and the AST modified by our pipeline.
     This hack assumes that the labels remain the same and uses this to generate
     a label to BB mapping that uses the modified AST CFG's BB ids.
     This mapping is used to create a path of executed BBs from a list of executed
     PCs.
     This hack is required because the assumptions use the BB ids from a CFG based
     on the modified AST while we symbolically execute the unmodified AST.
     To match both executions we create a path of the executed BBs because matching
     path predicates is not feasible ATM.
  *)
  let compute_bb_mappings ast_cfg ssa_cfg  =
    let make_lab2bb cfg = Cfg.AST.G.fold_vertex (fun v acc ->
        let stmts = Cfg.AST.get_stmts cfg v in
        (* Some BBs only contain comments (e.g., BB_Exit ) *)
        if Bb.contains_code stmts && not (only_halt_or_comment stmts)
        then
          begin
            match find_labels stmts with
            | Some l, Some l'->
              BatHashtbl.add acc l (Cfg.AST.G.V.label v);
              BatHashtbl.add acc l' (Cfg.AST.G.V.label v);
              acc
            | Some l, None ->
              BatHashtbl.add acc l (Cfg.AST.G.V.label v);
              acc
            | None, Some _  -> failwith "This cannot happen!"
            | None, None -> failwith (Printf.sprintf "BB %s does not contain a label!\n%s"
                                     (Cfg.AST.v2s v) (Print.list_to_string Pp.ast_stmt_to_string stmts))
          end
        else acc
      ) cfg (BatHashtbl.create (Cfg.AST.G.nb_vertex cfg))
    in
    (*
      Lang agnostic mapper from address to BB ids containing the address.

      XXX: What about expanded rep* prefixes? Currently expecting those to fail.
    *)
    let make_addr2bb fold_vertex get_stmts pp label get_addr cfg =
      fold_vertex (fun v acc ->
        let stmts = get_stmts cfg v in
        match get_addr stmts with
        | Some addr -> BatHashtbl.add acc addr (label v);
          acc
        | None ->
          begin
            match (label v) with
            | Cfg.BB_Entry | Cfg.BB_Exit | Cfg.BB_Indirect | Cfg.BB_Error ->
              acc
            | Cfg.BB n ->
              raise (Cannot_validate
                       (Printf.sprintf "Unable to determine address of BB %i!\n%s"
                          n (Print.list_to_string pp stmts)))
             end
        ) cfg (BatHashtbl.create 8)in
    let ssa_addr2bb = make_addr2bb Cfg.SSA.G.fold_vertex Cfg.SSA.get_stmts Pp.ssa_stmt_to_string
        Cfg.SSA.G.V.label Bb.get_bbaddr_from_ssa ssa_cfg in
    let ast_addr2bb = make_addr2bb Cfg.AST.G.fold_vertex Cfg.AST.get_stmts Pp.ast_stmt_to_string
      Cfg.AST.G.V.label Bb.get_bbaddr ast_cfg in
    (*
      Using addresses we locate the BBs containing these addresses and store a
      mapping of AST BBs to SSA BBs that contain the same address *but* have a
      different id.
    *)
    let bb2bb = BatHashtbl.fold (fun k v acc ->
        let bb = BatHashtbl.find ssa_addr2bb k in
        if bb <> v then begin
          BatHashtbl.add acc v bb;
          acc
        end else acc
      ) ast_addr2bb (BatHashtbl.create 8) in
    let lab2bb = make_lab2bb ast_cfg in
    (lab2bb, bb2bb)

  let map_paths subg (af,cfg,lab2bb,bb2bb) (af',cfg',lab2bb',bb2bb') states states' =
    (* Collect the first label of each BB *)
    let aux af cfg lab2bb bb2bb bb2bb' summary2bbcmp other_summary states =
      List.map (fun (halt_value, state, path) ->
          let path = List.rev path in
          let addr_to_label = reverse_hashtbl (state.Symbeval.lambda) in
          let prev_mapped_pc = ref Int64.minus_one in
          let labelled_path = BatList.filter_map (fun pc ->
              match Misc.bathashtbl_find_option addr_to_label pc with
              | Some [] -> failwith "This will never happen"
              | Some [x] ->
                if !prev_mapped_pc <> (Int64.pred pc)
                then
                  begin
                    prev_mapped_pc := pc;
                    Some x
                  end
                else
                  begin
                    None
                  end
              | Some (h::t) -> failwith "Address is associated with multiple labels!"
              | None -> None
            ) path in
          let bb_path = BatList.filter_map (fun lab ->
              Misc.bathashtbl_find_option lab2bb lab
            ) labelled_path in
          let expected_bb_path = BatList.filter_map (fun bb ->
              let bb' = BatHashtbl.find_default bb2bb bb bb in
              match Bb.BBidMap.Exceptionless.find bb' af.Ktype.fbbs with
              | Some summary ->
                begin
                  match summary2bbcmp subg summary with
                  | Some bbcmp ->
                    begin
                    let summary = other_summary (Subgraph.BBCmp.bbp bbcmp) in

                    match (BatHashtbl.find_default bb2bb' summary.Bb.id [summary.Bb.id]) with
                    | [h] -> Some h
                    | _ -> failwith "Failed to map BB id from summary!"
                    end
                  | None ->
                    dprintf "Failed to find a matching BB for %s!"
                      (Cfg.bbid_to_string bb);
                    None
                end
              | None -> failwith (Printf.sprintf "Failed to find summary for %s (%s)!\n%s"
                                    (Cfg.bbid_to_string bb) (Cfg.bbid_to_string bb')
                                    (Print.enum_to_string (Cfg.bbid_to_string)
                                                 (Bb.BBidMap.keys af.Ktype.fbbs)))
            ) bb_path in
          (halt_value, state, (bb_path, expected_bb_path))
        ) states in
    let states = aux af cfg lab2bb bb2bb (reverse_hashtbl bb2bb') Subgraph.includes_bbl snd states in
    let states' = aux af' cfg' lab2bb' bb2bb' (reverse_hashtbl bb2bb) Subgraph.includes_bbr fst states' in
    (states, states')

  (* XXX: This assumes that the symbolic context is created with build_default_context! *)
  let labels2pc stmts =
    let mapping = Hashtbl.create (List.length stmts) in
    ignore(List.fold_left (fun pc stmt ->
        match stmt with
        | Ast.Label (lab, _) ->
          Hashtbl.add mapping lab pc; Int64.succ pc
        | _ -> Int64.succ pc
      ) Int64.zero stmts);
    mapping

  let prepare_function af =
    let stmts = Function_info.Function.unmodified_stmts af.Ktype.function_info in
    let cfg = Cfg_ast.of_prog stmts
              |> Hacks.ast_remove_indirect
              |> Prune_unreachable.prune_unreachable_ast
              |> Coalesce.coalesce_ast
              |> cfg_add_halts
    in
    let stmts' = cfg |> Cfg_ast.to_prog |> Memory2array.coerce_prog in
    (cfg, stmts')

  let do_validate subg =
    let module P = BatPair in
    let af,af' = Subgraph.afs subg in
    let ((cfg, stmts), (cfg', stmts')) = P.map prepare_function (af,af') in
    let (lab2bb,bb2bb), (lab2bb',bb2bb') =
      P.map(uncurry compute_bb_mappings)
        ((cfg, af.Ktype.cfg), (cfg', af'.Ktype.cfg)) in
    let labels2pc, labels2pc' = P.map labels2pc (stmts,stmts') in
    let skip_list, skip_list' =
      let aux af cfg includes bb2bb label2pc = Cfg.AST.G.fold_vertex (fun v acc ->
        let bb = Cfg.AST.G.V.label v in
        let bb' = BatHashtbl.find_default bb2bb bb bb in
        match Bb.BBidMap.Exceptionless.find bb' af.Ktype.fbbs with
        | Some summary ->
           begin
             match includes summary with
             | Some _ -> acc
             | None ->
                let stmts = Cfg.AST.get_stmts cfg v in
                (*
                  If there are no meaningfull statements in the BB (e.g. BB_Exit)
                  Just keep it, because it cannot modify the final state.
                *)
                if (only_halt_or_comment stmts) ||  (List.length stmts) = 0
                then acc
                else begin
                  let pc2range pc =
                    let rec aux n acc =
                      if (compare n pc) = (-1)
                      then acc
                      else aux (Int64.pred n) (n :: acc)
                    in
                    let last_pc = Int64.add pc (Int64.of_int (List.length stmts - 1)) in
                    aux last_pc [] in
                  match find_labels stmts with
                  | Some lab, _ ->
                     (match label2pc lab with
                     | Some pc ->
                        let range = pc2range pc in
                        range @  acc
                     | None -> failwith (Printf.sprintf "BB %s has no mapped pc!"
                                           (Cfg.bbid_to_string bb)))
                  | None, Some _ (* Will never happen! *)
                  | None, None -> failwith (Printf.sprintf "BB %s has no address!"
                                              (Cfg.bbid_to_string bb))
                end
           end
        | None -> failwith (Printf.sprintf "Failed to find summary for %s (%s)!"
                              (Cfg.bbid_to_string bb) (Cfg.bbid_to_string bb'))
      ) cfg [] in
      (aux af cfg (Subgraph.includes_bbl subg) bb2bb (Misc.bathashtbl_find_option labels2pc),
       aux af' cfg' (Subgraph.includes_bbr subg) bb2bb' (Misc.bathashtbl_find_option labels2pc'))
    in
    let eval skip_list stmts =
      symbeval ~skip_list stmts
    in
    let states, states' = P.map (uncurry eval) ((skip_list,stmts),(skip_list',stmts')) in
    let states, states' = map_paths subg (af,cfg,lab2bb,bb2bb)
      (af',cfg',lab2bb',bb2bb') states states' in
    let no_states, no_states' = P.map List.length (states, states') in
    if no_states = no_states'
    then
      begin
        let pairs = pair_states_by_path states states' in
        List.iter (verify_equivalence subg) pairs
      end
    else
      let str = Printf.sprintf "Number of states mismatch, %i vs %i"
        no_states no_states'
      in
      raise (Cannot_validate str)

  let validate subg =
    try
      do_validate subg;
      BatResult.Ok ()
    with
    | Unsatisfiable ->
      BatResult.Bad "Unsatisfiable match"
    | Cannot_validate reason ->
      BatResult.Bad (Printf.sprintf "Cannot validate: %s" reason)
    | Not_found ->
      BatResult.Bad "Internal error: Not_found in validate"
    | Symbolic.UnknownLabel lab ->
      let str = Printf.sprintf "Encountered unknown label %s"
          (Pp.label_to_string lab) in
      BatResult.Bad str
end
