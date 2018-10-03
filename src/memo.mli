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

module MakeSingleMemoizer : SingleMemoizerSig;;
