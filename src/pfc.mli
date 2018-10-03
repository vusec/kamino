module type CachedObjSig =
sig
  type id
  type element
  val id_to_string : id -> string
end

module type MakePersistentCacheSig =
  functor (CachedObj : CachedObjSig) ->
sig
  type element = CachedObj.element
  type id = CachedObj.id
  type t
  val create : string -> string -> t
  val get : t -> id -> element list option
  val put : t -> id -> element -> unit
end;;

module MakePersistentCache : MakePersistentCacheSig;;
