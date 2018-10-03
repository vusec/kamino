let output_ssa oc p =
  Cfg_pp.SsaStmtsDot.output_graph oc p

let output_ast oc p =
  Cfg_pp.AstStmtsDot.output_graph oc p

let output_ast_bbids f p =
  let oc = open_out f in
  Cfg_pp.AstBBidDot.output_graph oc p;
  close_out oc

let output_ast_cdg f p =
  let oc = open_out f in
  let exit_nodes =
    Cfg.AST.G.fold_vertex (fun v acc ->
      if (Cfg.AST.G.out_degree p v) = 0
      then v :: acc
      else acc) p [] in
  let rec add_exit cfg exit_nodes =
    let connect_exit exit =
      let (cfg, exit') = Cfg_ast.find_exit cfg in
      Cfg.AST.add_edge cfg exit exit'
    in
    match exit_nodes with
    | [] -> failwith "Couldn't find exit node!"
    | [exit] -> connect_exit exit
    | h :: t -> add_exit (connect_exit h) t
  in
  let cdg = Depgraphs.CDG_AST.compute_cdg (add_exit p exit_nodes) in
  Cfg_pp.AstBBidDot.output_graph oc cdg;
  close_out oc

let output_ast_pdg f p =
  let oc = open_out f in
  let pdg = Depgraphs.PDG_AST.compute_pdg p in
  Cfg_pp.AstStmtsDot.output_graph oc pdg;
  close_out oc

let output_depgraphs base astcfg =
  output_ast_bbids (base ^ ".bbids.dot") astcfg;
  output_ast_cdg (base ^ ".cdg.dot") astcfg;
  output_ast_pdg (base ^ ".pdg.dot") astcfg
