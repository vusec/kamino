val cmp_exprs : Assumptions.t ->
  ?running_assumption:(Ssa_ext.Variable.t list * Ssa_ext.Variable.t list) option ->
  Ssa_ext.Expression.t -> Ssa_ext.Expression.t -> (Assumptions.t * bool)

val cmp_vars : Assumptions.t ->
  ?running_assumption:(Ssa_ext.Variable.t list * Ssa_ext.Variable.t list) option ->
  Ssa_ext.Variable.t -> Ssa_ext.Variable.t -> (Assumptions.t * bool)

val cmp_vals : Assumptions.t ->
  ?running_assumption:(Ssa_ext.Variable.t list * Ssa_ext.Variable.t list) option ->
  Ssa_ext.Value.t -> Ssa_ext.Value.t -> (Assumptions.t * bool)

val chunks_equiv : Assumptions.t -> Ssa_ext.Expression.t -> Ssa_ext.Expression.t ->
  (Assumptions.t * bool)
