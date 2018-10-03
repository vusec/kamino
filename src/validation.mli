module type Validator
=
sig
  type subgraph

  val validate : subgraph -> (unit, string) BatResult.t
end

module SymbValidator (BBMgr:Bb_cluster.BBClusterManagerSig) (Algorithm : Comparator.AlgoSig with type bbcluster_type := BBMgr.t and type bbcluster_key := Bb_cluster.ClusterHashtbl.key) : Validator
  with type subgraph = Algorithm.subgraph
