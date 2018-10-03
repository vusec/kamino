type t
type uniq_t

val empty : t
val merge_equivs : t -> t -> (t, string) BatResult.t
val to_string : t -> string
val sexp_of_t : ?lr:bool -> t -> Sexplib.Sexp.t
val of_desc : (Ssa_ext.Variable.t list * Ssa_ext.Variable.t list) list -> t
val normalize : t -> t
val verify_against_single : t -> (Ssa_ext.Variable.t * Ssa_ext.Variable.t) -> (unit, string) BatResult.t
val compare : t -> t -> int
val add_assumption : t -> (Ssa_ext.Variable.t list * Ssa_ext.Variable.t list) -> (t, string) BatResult.t
val number : t -> int
val simplify_asxs : t -> t -> (t * t, string) BatResult.t
val fold_left : ('a -> (Ssa_ext.Variable.t list * Ssa_ext.Variable.t list) -> 'a) -> 'a -> t -> 'a
val filter_vis : t -> Visibility.t -> Visibility.t -> (Cfg.bbid * Cfg.bbid) -> t
val to_formula : uniq_t -> Ast.exp
val relevant_vars : t -> Var.VarSet.t * Var.VarSet.t
(** Uniqify the variables in the assumptions according to their side (e.g., LHS or RHS) *)
val uniqify_asxs : t -> (uniq_t  * (Ssa_ext.Variable.t,  Ssa_ext.Variable.t) BatHashtbl.t * (Ssa_ext.Variable.t,  Ssa_ext.Variable.t) BatHashtbl.t)
