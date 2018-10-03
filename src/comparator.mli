type matched_exprs = {
  in_asxs : Assumptions.t;
  out_asxs :Assumptions.t;
}

type bbcmp_res =
| Exact of float
| Partial of (int * int)
| Subset of (int * int)
| Superset of (int * int)
| Fail

val bbcmp_res_to_str: bbcmp_res -> string

type match_info = {
  matched_direct : matched_exprs;
  missing1 : Transfer_function.t list;
  missing2 : Transfer_function.t list;
}

module type BBCmpResSig =
sig
  type t
  val create : (Bb.bb_summary * Bb.bb_summary) -> bbcmp_res -> match_info -> t
  val res : t -> bbcmp_res
  val bbp : t -> (Bb.bb_summary * Bb.bb_summary)
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexplib.Sexp.t
  val to_string : t -> string
  val match_info : t -> match_info
  val update_match_info: t -> match_info -> t
  val equal : t -> t -> bool
end;;

module type BBCmpResRichSig =
sig
  include BBCmpResSig
end;;

module type CfgMatchingPolicy =
sig
  module BBCmp : BBCmpResSig
  val accept_as_seed : bb1:Bb.bb_summary -> bb2:Bb.bb_summary -> bool
  val accept_expansion : nonexact:bbcmp_res option -> BBCmp.t -> bool
end

module WholeFunctionMatchingPolicy : (functor (BBCmp : BBCmpResSig) -> CfgMatchingPolicy)
module ExhaustiveMatchingPolicy : (functor (BBCmp : BBCmpResSig) -> CfgMatchingPolicy)
module FuzzyInlineMatchingPolicy : (functor (BBCmp : BBCmpResSig) -> CfgMatchingPolicy)

val matchingpolicyfactory : (module BBCmpResSig) -> string -> (module CfgMatchingPolicy)

module type MatchingSubgraphSig =
sig
  type t
  module BBCmp : BBCmpResSig
  type bbcmp = BBCmp.t
  open Cmpres
  module Flags :
  sig
    type t = func_cmp_flags
    val to_string : t -> string
  end
  module FlagsSet : (BatSet.S with type elt = func_cmp_flags)

  type matched_edge = {
    src : Cfg.bbid;
    dst : Cfg.bbid;
  }
  val create : (Ktype.analyzed_func * Ktype.analyzed_func) -> bbcmp list -> t
  val add : t -> bbcmp -> t option
  val size : t -> int
  val res : t -> cfgcmp_res
  val flags : t -> FlagsSet.t
  val flags_to_str : FlagsSet.t -> string
  val to_string : t -> string
  val includes_any_of_edgep : t -> (matched_edge * matched_edge) -> bool
  val includes_bbids : t -> (Cfg.bbid * Cfg.bbid) -> bbcmp option
  val includes_bbp : t -> (Bb.bb_summary * Bb.bb_summary) -> bbcmp option
  val includes_bbl: t -> Bb.bb_summary -> bbcmp option
  val includes_bbr: t -> Bb.bb_summary -> bbcmp option
  val afs : t -> (Ktype.analyzed_func * Ktype.analyzed_func)
  val find_bbp_l : t -> Cfg.bbid -> (Bb.bb_summary * Bb.bb_summary) option
  val find_bbp_r : t -> Cfg.bbid -> (Bb.bb_summary * Bb.bb_summary) option
  val add_edgepair : t -> (matched_edge * matched_edge) -> t
  val map_bbcmps : t -> (bbcmp -> bbcmp) -> t
  val diff_bbcmps : t -> t -> bbcmp list
  val fpit_assumptions : t -> t option
  val good_enough : t -> bool
  val collect_edge_bbs : t -> (bbcmp list * bbcmp list)
  val dump : t -> out_channel -> unit
end;;

module type AlgoSig =
sig
  type t
  type bbcluster_key
  type bbcluster_type
  type prog_summary = (Ktype.analyzed_prog * bbcluster_type)
  module Subgraph : MatchingSubgraphSig
  type subgraph = Subgraph.t
  val init : unit -> t
  val compare : t -> ?entries_only:bool -> prog_summary -> prog_summary ->
    ((bbcluster_key * subgraph list) list *
     Embarassingly_parallel.exn_with_bt list)
end;;

module Algo
    (BBMgr : Bb_cluster.BBClusterManagerSig)
    (Policy : CfgMatchingPolicy):
  AlgoSig with type bbcluster_type := BBMgr.t and type bbcluster_key := Bb_cluster.ClusterHashtbl.key;;
module BBCmpResPlain : BBCmpResSig
module BBCmpResRich : BBCmpResRichSig
