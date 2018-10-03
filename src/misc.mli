
type arch = Asmir.arch

val bathashtbl_find_option : ('a, 'b) BatHashtbl.t -> 'a -> 'b option
val finally_with_exn : (exn option -> unit) -> ('a -> 'b) -> 'a -> 'b
val finally : (unit -> unit) -> ('a -> 'b) -> 'a -> 'b

module type HashableStringSig =
sig
  type t = string
  val equal : t -> t -> bool
  val hash : t -> int
end;;

module HashableString : HashableStringSig;;

val ary_bsearch : 'v array -> ('v -> 'k) -> ('k -> 'k -> int) -> 'k -> int option
val list_pad : int -> 'a -> 'a list -> 'a list
val npartition : ('v -> 'k) -> 'v list -> ('k, 'v list) BatHashtbl.t
val list_unique_pairs : 'a list -> ('a * 'a) list
val permutations : 'a list -> 'a list list
val longest_common_prefix_n : ('a -> 'a -> bool) -> 'a list list -> 'a list
val ffs : Int64.t -> int option
val bi_is_mask : (Big_int_Z.big_int * Type.typ) -> int option
val bi_bit_ranges : (Big_int_Z.big_int * Type.typ) -> BatISet.t
val lists_do_match : 's -> 'l list -> 'r list -> ('s -> 'l -> 'r -> ('s * 'c) option) ->
  ('s * 'c list * 'l list * 'r list)
val is_call : arch -> Ast.stmt -> bool
val is_ret : arch -> Ast.stmt -> bool
val call_is_getpc: arch -> Type.addr -> Ast.stmt -> bool
val ast_replace_calls : arch -> Ast.program -> Ast.program
val normalize_string: Str.regexp -> string -> string
val strcmp : string -> expected:string -> got:string -> (unit, string) BatResult.t
val stmts_with_addrs: Ast.stmt list -> (Type.addr option * Ast.stmt) list
val ast_stmts_eq : Ast.stmt -> Ast.stmt -> (unit, string) BatResult.t
val astcfgs_identical : Cfg.AST.G.t -> Cfg.AST.G.t -> (unit, string) BatResult.t
val astcfgs_isomorphic : Cfg.AST.G.t -> Cfg.AST.G.t -> (unit, string) BatResult.t
val ssacfgs_isomorphic : Cfg.SSA.G.t -> Cfg.SSA.G.t -> (unit, string) BatResult.t
type frange = (string * Int64.t * Int64.t)
val demangle_franges : frange list -> frange list
val dedup_franges : frange list -> (string list * Int64.t * Int64.t) list
val type_width_equal : Type.typ -> Type.typ -> bool
module Pervasives :
sig
  val (|-) : ('a -> 'b) -> ('b -> 'c) -> ('a -> 'c)
end;;
