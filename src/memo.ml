module D = Debug.Make(struct let name = "Memo" and default=`NoDebug end)
open D

module type SingleMemoizableSig = sig
  type k
  type v
  type priv
  val lookup : priv -> k -> v
  val finalize: v -> unit
  val k_to_string: k -> string
end;;

module type SingleMemoizerSig =
  functor (Memo : SingleMemoizableSig) ->
sig
  type key = Memo.k
  type value = Memo.v
  type priv = Memo.priv
  type t
  val create : priv -> t
  val lookup : t -> key -> value
end;;

module MakeSingleMemoizer : SingleMemoizerSig  = functor (Memoizable : SingleMemoizableSig) ->
struct
  type key = Memoizable.k
  type value = Memoizable.v
  type priv = Memoizable.priv
  type t = ((key * value) option * priv) ref
  let create p = ref (None, p)
  let lookup memo k = match !memo with
      | (None, p) ->
	let () = dprintf "memo: no saved\n" in
	let v = Memoizable.lookup p k in
	let () = memo := (Some (k, v), p) in
	v
      | (Some (saved_k, saved_v), p) ->
	let k_str = Memoizable.k_to_string k in
	let saved_str = Memoizable.k_to_string saved_k in
	dprintf "%s vs %s (saved)" k_str saved_str;
	if 0 = (String.compare saved_str k_str) then
	  let () = dprintf "match!\n" in
	  saved_v
	else
	  let () = dprintf "no match\n" in
	  let () = Memoizable.finalize saved_v in
	  let v = Memoizable.lookup p k in
	  let () = memo := (Some (k, v), p) in
	  v
end;;

