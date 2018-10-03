type t

val empty : t
val add : t -> Callgraph.call_target -> t
val call_at_addr : t -> Type.addr -> Callgraph.call_target option
val fold : (Callgraph.call_target -> 'acc -> 'acc) -> t -> 'acc -> 'acc
val filter_by_site : (Type.addr -> bool) -> t -> Callgraph.call_target list
val to_string : t -> string
