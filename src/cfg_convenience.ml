module GetExitBBs(G : Graph.Sig.G) =
struct
  let get_exit_bbs cfg =
    let exit_vs = G.fold_vertex (fun v acc ->
        match G.out_degree cfg v with
        | 0 -> v::acc
        | _ -> acc) cfg []
    in
    match exit_vs with
    | [] -> failwith "No exit vertex!"
    | vs -> vs
end

module AST : sig
  val get_exit_bbs : Cfg.AST.G.t -> Cfg.AST.G.V.t list
  val rewrite_by_bb_stmts : Cfg.AST.G.t -> (Ast.stmt list -> Ast.stmt list) -> Cfg.AST.G.t
end = struct
  include GetExitBBs(Cfg.AST.G)
  let rewrite_by_bb_stmts g f =
    Cfg.AST.G.fold_vertex (fun v acc ->
        let stmts = Cfg.AST.get_stmts g v in
        Cfg.AST.set_stmts acc v (f stmts)) g g
end

module SSA : sig
  val get_exit_bbs : Cfg.SSA.G.t -> Cfg.SSA.G.V.t list
  val walk_from_bb_inclusive : (Cfg.SSA.G.V.t -> 'a -> 'a) -> Cfg.SSA.G.t ->
    'a -> Cfg.bbid -> (Cfg.SSA.G.t -> Cfg.SSA.G.V.t -> Cfg.SSA.G.V.t list) ->
    'a
  val walk_from_bb : (Cfg.SSA.G.V.t -> 'a -> 'a) -> Cfg.SSA.G.t -> 'a ->
    Cfg.bbid -> (Cfg.SSA.G.t -> Cfg.SSA.G.V.t -> Cfg.SSA.G.V.t list) -> 'a
  val walk_bb_predecessors_inclusive : (Cfg.SSA.G.V.t -> 'a -> 'a) -> Cfg.SSA.G.t -> 'a -> 'a
  val walk_bb_successors_inclusive : (Cfg.SSA.G.V.t -> 'a -> 'a) -> Cfg.SSA.G.t -> 'a -> 'a
end = struct
  include GetExitBBs(Cfg.SSA.G)

  let rec do_walk_from_bb f g next to_visit visited a =
    if BatSet.is_empty to_visit then a
    else
      let bb, visits_left = BatSet.pop to_visit in
      let next_candidates = next g bb in
      let next_to_visit = BatSet.diff (BatSet.of_list next_candidates) visited in
      let to_visit' = BatSet.union visits_left next_to_visit in
      let a' = f bb a in
      let visited' = BatSet.add bb visited in
      do_walk_from_bb f g next to_visit' visited' a'

  let walk_from_bb_inclusive f g a start next =
    try
      let start_bb = Cfg.SSA.find_vertex g start in
      do_walk_from_bb f g next (BatSet.singleton start_bb) BatSet.empty a
    with Not_found ->
      Printf.eprintf "Could not find %s" (Cfg.bbid_to_string start);
      failwith "Could not find start vertex"

  let walk_from_bb f g a start next =
    try
      let start_bb = Cfg.SSA.find_vertex g start in
      let seeds = next g start_bb in
      do_walk_from_bb f g next (BatSet.of_list seeds) BatSet.empty a
    with Not_found ->
      Printf.eprintf "Could not neighbors or vertex of %s" (Cfg.bbid_to_string start);
      failwith "Could not find neighbors of or the start vertex itself"

  let walk_bb_predecessors_inclusive f g a =
    let exit_bb = match get_exit_bbs g with
      | [bb] -> bb
      | _ -> failwith "More than one exit vertex!"
    in
    let exit_v = Cfg.SSA.G.V.label exit_bb in
    walk_from_bb_inclusive f g a exit_v Cfg.SSA.G.pred
  let walk_bb_successors_inclusive f g a =
    walk_from_bb_inclusive f g a Cfg.BB_Entry Cfg.SSA.G.succ
end
