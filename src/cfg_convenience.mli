module AST : sig
  val get_exit_bbs : Cfg.AST.G.t -> Cfg.AST.G.V.t list
  val rewrite_by_bb_stmts : Cfg.AST.G.t -> (Ast.stmt list -> Ast.stmt list) -> Cfg.AST.G.t
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
end
