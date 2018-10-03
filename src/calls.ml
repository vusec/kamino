module D = Debug.Make(struct let name = "Calls" and default=`Debug end)
open D

let fi_make_conservative ?keypref:(keypref=None) cg fi =
  let module C = Cfg.AST in
  let module E = C.G.E in
  dprintf "fi_make_conservative for %s" (Function_info.to_string fi);
  let orig_cfg = BatOption.get (Function_info.astcfg fi) in
  let call_edges = Callgraph.Callgraph.succ_e cg fi in
  let calls = List.map (fun call_edge ->
    let callee = Callgraph.Callgraph.E.dst call_edge in
    let _, {Callgraph.call_site = call_site}, _ = call_edge in
    (call_site, callee)) call_edges
  in
  let get_call addr =
    try
      let res = BatList.find_map (fun (site, target) ->
        if Int64.compare site addr = 0 then
          Some target
        else
          None) calls
      in
      Some res
    with Not_found -> None
  in
  let maybe_redirect cfg vertex out_edge target =
    let open Function_info in
    let do_redirect () =
      let cfg = C.remove_edge_e cfg out_edge in
      let cfg, bberr = Cfg_ast.find_error cfg in
      let edge_to_err = E.create vertex None bberr in
      dprintf "redirecting to BB_Error";
      C.add_edge_e cfg edge_to_err
    in
    match target with
    | ExternalFunction _ ->
      (*
       * For an external function, the ABI allows
       * us to account for side-effects.
       *)
      cfg
    | Indirect ->
      begin
        match Options.summarize_calls with
        | Options.CallSumCdecl ->
          cfg
        | Options.CallSumCalculate ->
          (*
           * Eh, in practice we could probably assume cdecl here,
           * but we have bigger problems WRT indirect calls...
           *)
          do_redirect ()
      end
    | Unknown _ ->
      (* Can't say much for this... *)
      do_redirect ()
    | Function _ ->
      begin
        match Options.summarize_calls with
        | Options.CallSumCdecl ->
          cfg
        | Options.CallSumCalculate ->
         (*
          * Observable functions we handle conservatively for now. In the
          * future, we need to be looking at control-flow dependent stores
          * and whatnot.
          *)
          do_redirect ()
      end
  in
  let ncfg = C.G.fold_edges_e (fun e ng ->
    let src = E.src e in
    let stmts = C.get_stmts orig_cfg src in
    match Bb.get_bbbounds_from_ast stmts with
    | None ->
      (*
       * No bounds means "empty" BB (i.e. no actual code). In that case,
       * we can be sure there are no calls there.
       *)
      ng
    | Some (low, high) ->
      (match get_call high with
      | None ->
        ng (* Does not end with a call *)
      | Some target ->
        maybe_redirect ng src e target)) orig_cfg orig_cfg
  in
  ignore(match keypref with
  | None -> ()
  | Some keypref ->
    let key = Printf.sprintf "%s/after-account-for-calls.ast.dot" keypref in
    Outdir.with_file_out key (fun oc ->
        Graph_dump.output_ast oc ncfg));
  Function_info.set_astcfg fi ncfg

let account_for_calls ~func_filter ?keypref:(keypref=None) cg =
  dprintf "Trying to account for calls";
  let do_func fi =
    match fi with
    | Function_info.Function func when func_filter fi ->
      let keypref = BatOption.map (fun p ->
          Printf.sprintf "%s/%s" p (Analysis_pass.fdir func)) keypref
      in
      fi_make_conservative ~keypref cg fi
    | _ ->
      fi
  in
  Analysis_pass.map_vertex do_func cg
