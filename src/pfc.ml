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

module MakePersistentCache = functor (CachedObj : CachedObjSig) ->
struct
  type element = CachedObj.element
  type id = CachedObj.id
  type t = {
    basepath : string;
  }
  let create path name = {basepath = (Printf.sprintf "%s.%s" path name);}
  (* XXX: verify that this file is newer than the basefile *)
  let elpath cache id = (Printf.sprintf "%s.%s.pfc" (cache.basepath) (CachedObj.id_to_string id))
  let get cache id =
    let path = elpath cache id in
    try
      let ic = open_in_bin path in
      let ret = ref [] in
      try
	while true do
	  let el = (Marshal.from_channel ic : element) in
	  ret := el :: !ret
	done;
	None
      with End_of_file -> Some (List.rev !ret)
    with Sys_error _ -> None
  let put cache id el =
    let path = elpath cache id in
    let oc = open_out_gen [Open_binary; Open_creat; Open_append] 0o660 path in
    Marshal.to_channel oc el [];
    close_out oc
end
