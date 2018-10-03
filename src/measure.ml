type measure_arg = Ktype.analyzed_func * Bb.bb_summary * Ssa_ext.Expression.t

module type S =
sig
  val selector : string

  val measure : measure_arg -> int
end

module TransferFunctionDepth : S =
struct
  let selector = "TransferFunctionDepth"

  let measure (_,_,tf) =
    let rec depth_var = function
      | Ssa_ext.Variable.Var _ -> 1
      | Ssa_ext.Variable.VarExp (_,exp,_) -> 1 + (depth_exp exp)
    and depth_value = function
      | Ssa_ext.Value.Int _ -> 1
      | Ssa_ext.Value.Var var -> 1 + (depth_var var)
      | Ssa_ext.Value.Lab _ -> 1
    and depth_exp exp =
      (* XXX: for now we treat Phis with depth 1 *)
      let rev_compare x y = (-1) * (compare x y) in
      let vals,_,_,_,_,_,_,_,_ = Ssa_ext.Expression.getargs exp in
      let l = List.sort rev_compare (List.map (fun v -> depth_value v) vals) in
      if List.length l == 0
      then 1
      else List.hd l
    in
    depth_exp tf
end

module TransferFunctionRoot : S =
struct
  let selector = "TransferFunctionRoot"

  (* XXX: Need to consider the bin- and unops! *)
  let measure (_,_,tf) =
    Ssa_ext.num_exp tf
end

module BbTransferFunctionCardinality : S =
struct
  let selector = "BbTransferFunctionCardinality"

  let measure (_,bbsum,_) =
    let module StringMap = BatMap.Make(String) in
    match bbsum.Bb.tfs with
    | Some tfs -> StringMap.cardinal tfs
    | None -> failwith "BB with no TFs in cluster!"
end

module BbCardinal : S =
struct
  let selector = "BbCardinal"

  let measure (afunc,_,_) =
    let cfg = afunc.Ktype.cfg in
    Cfg.SSA.G.nb_vertex cfg
end

module DomTreePosition : S =
struct
  let selector = "DomTreePosition"

  let measure (afunc,bbsum,_) =
    let begin_vertex = Cfg.SSA.G.V.create Cfg.BB_Entry in
    let vertex = Cfg.SSA.find_vertex afunc.Ktype.cfg bbsum.Bb.id in
    let rec find_path_backwards acc from to_ =
      if from = to_
      then List.rev acc
      else
        let idom = afunc.Ktype.dominfo.Ktype.SsaDom.idom to_ in
        find_path_backwards (idom :: acc) from idom
    in
    List.length (find_path_backwards [] begin_vertex vertex)
end

module IsDominator : S =
struct
  let selector = "IsDominator"

  let measure (afunc,bbsum,_) =
    let vertex = Cfg.SSA.find_vertex afunc.Ktype.cfg bbsum.Bb.id in
    let doms = afunc.Ktype.dominfo.Ktype.SsaDom.dominees vertex in
    if List.length doms > 0
    then 1
    else 0
end

module DomineesCardinal : S =
struct
  let selector = "DomineesCardinal"

  let measure (afunc,bbsum,_) =
    let vertex = Cfg.SSA.find_vertex afunc.Ktype.cfg bbsum.Bb.id in
    let doms = afunc.Ktype.dominfo.Ktype.SsaDom.dominees vertex in
    List.length doms
end

module DominatorCardinal : S =
struct
  let selector = "DominatorCardinal"

  let measure (afunc,bbsum,_) =
    let vertex = Cfg.SSA.find_vertex afunc.Ktype.cfg bbsum.Bb.id in
    let doms = afunc.Ktype.dominfo.Ktype.SsaDom.dominators vertex in
    List.length doms
end
