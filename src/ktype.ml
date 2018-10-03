module SsaDom = Dominator.Make(Cfg.SSA.G);;

type analysis_pass_result =
  [
    | `Callinfo of Callinfo.t
    | `Retinfo of Type.addr list
    | `Hltinfo of Type.addr list
    | `Addrmap of (Type.addr, Cfg.bbid) BatHashtbl.t
    | `DataDependencies of (Var.VarSet.t * Depgraphs.DDG_SSA.location Var.VarHash.t *
                              Depgraphs.DDG_SSA.location list Var.VarHash.t)
    | `Inputs of Var.VarSet.t
    | `MemAccesses of Memrange.t
    | `CollapsibleLoads of (Depgraphs.DDG_SSA.location, Ssa.value) BatHashtbl.t
  ]

type analyzed_func = {
  function_info: Function_info.Function.t;
  cfg: Cfg.SSA.G.t;
  fbbs: Bb.bb_summary Bb.BBidMap.t;
  dominfo: SsaDom.dom_functions;
  visibility: Visibility.t;
  callinfo: Callinfo.t;
}

type analyzed_prog = {
  pname: string;
  pranges: Address_ranges.address_ranges_type;
  pfuncs: (Type.addr, analyzed_func) Hashtbl.t;
}

module Exceptions = struct
  exception Confusing_function of string
end

let v2bb af v =
  try
    Bb.BBidMap.find (Cfg.SSA.G.V.label v) af.fbbs 
  with Not_found ->
    let str = Printf.sprintf "No bb_summary for %s" (Cfg.SSA.v2s v) in
    failwith str

let bb2v af bb =
  try
    Cfg.SSA.find_vertex af.cfg bb.Bb.id
  with Not_found ->
    let str = Printf.sprintf "Failed to find %s in function %s"
      (Cfg.bbid_to_string bb.Bb.id) (Function_info.Function.to_string af.function_info) in
    failwith str
