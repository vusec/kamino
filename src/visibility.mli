
type t

val initialize : ?keypref:string option -> Cfg.SSA.G.t -> t
val var_visible : t -> Var.t -> Cfg.bbid -> bool
val var_is_live_in_defining_bb : t -> Var.t -> Cfg.bbid -> bool
val var_useful : t -> Var.t -> Cfg.bbid -> bool
val var_def_used : t -> Var.t -> Cfg.bbid -> bool
val to_string : t -> string
val var_is_external : t -> Var.t -> bool
val var_is_used_exn : t -> Var.t -> Cfg.bbid -> bool
