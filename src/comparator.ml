module D = Debug.Make(struct let name = "Comparator" and default=`Debug end)
open D

module Function = Function_info.Function

module BatPair = struct
    let map f (a, b) = (f a, f b)
end

let ( -| ) f g x = f (g x)

type matched_exprs = {
  (* XXX: these need to be maintained on edges *)
  in_asxs : Assumptions.t;
  out_asxs :Assumptions.t;
}

type bbcmp_res =
  | Exact of float
  | Partial of (int * int) (* fraction: nom/denom *)
  | Subset of (int * int) (* matched, available on RHS *)
  | Superset of (int * int) (* matched, available on LHS *)
  | Fail

let bbcmp_res_to_str = function
  | Exact score -> Printf.sprintf "EXACT (%.2f)" score
  | Partial (m, av)  -> Printf.sprintf "PARTIAL (%d/%d)" m av
  | Subset (m, av) -> Printf.sprintf "SUBSET (%d/%d)" m av
  | Superset (m, av) -> Printf.sprintf "SUPERSET (%d/%d)" m av
  | Fail -> "FAIL"

open Sexplib
let cmpres_to_sexp = function
  | Exact score -> Sexp.List [Sexp.of_string "EXACT"; Std.sexp_of_float score]
  | Partial (m, av) ->
    Sexp.List [Sexp.Atom "PARTIAL"; Sexp.List [Std.sexp_of_int m; Std.sexp_of_int av]]
  | Subset (m, av) ->
    Sexp.List [Sexp.Atom "SUBSET"; Sexp.List [Std.sexp_of_int m; Std.sexp_of_int av]]
  | Superset (m, av) ->
    Sexp.List [Sexp.Atom "SUPERSET"; Sexp.List [Std.sexp_of_int m; Std.sexp_of_int av]]
  | Fail -> Sexp.of_string "FAIL"

module StringMap = BatMap.Make(String)

type match_info = {
  matched_direct : matched_exprs;
  missing1 : Transfer_function.t list;
  missing2 : Transfer_function.t list;
}

let empty_match_info = {
  matched_direct = {in_asxs = Assumptions.empty; out_asxs = Assumptions.empty};
  missing1 = [];
  missing2 = [];
}

module type BBCmpResSig =
sig
  type t
  val create : (Bb.bb_summary * Bb.bb_summary) -> bbcmp_res -> match_info -> t
  val res : t -> bbcmp_res
  val bbp : t -> (Bb.bb_summary * Bb.bb_summary)
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexp.t
  val to_string : t -> string
  val match_info : t -> match_info
  val update_match_info: t -> match_info -> t
  val equal : t -> t -> bool
end;;

module type BBCmpResRichSig =
sig
  include BBCmpResSig
end;;

module BBCmpResRich : BBCmpResRichSig =
struct
  type t = ((Bb.bb_summary * Bb.bb_summary) * bbcmp_res * match_info)
  let create bbp res mi = (bbp, res, mi)
  let res = function
    | (_, r, _) -> r
  let match_info = function
    | (_, _, mi) -> mi
  let bbp = function
    | (p, _, _) -> p
  let compare lhs rhs =
    let (a, b) = bbp lhs in
    let (c, d) = bbp rhs in
    let ldiff = Cfg.BBid.compare a.Bb.id c.Bb.id in
    if ldiff <> 0 then
      ldiff
    else
      Cfg.BBid.compare b.Bb.id d.Bb.id

  let equal lhs rhs =
    let (a, b) = bbp lhs in
    let (c, d) = bbp rhs in
    (a.Bb.id = c.Bb.id) && (b.Bb.id = d.Bb.id)
  let update_match_info (bbp, res, mi) nmi = (bbp, res, nmi)
  let sexp_of_t (bbp, res, mi) =
    let bb_to_sexp bbsum = Sexp.of_string (Cfg.bbid_to_string bbsum.Bb.id) in
    let bbs = Conv.sexp_of_pair bb_to_sexp bb_to_sexp bbp in
    let res = cmpres_to_sexp res in
    let in_asxs = Assumptions.sexp_of_t ~lr:true mi.matched_direct.in_asxs in
    let out_asxs = Assumptions.sexp_of_t ~lr:true mi.matched_direct.out_asxs in
    let asxs = Sexp.List [Sexp.List [Sexp.of_string "IN"; in_asxs];
                          Sexp.List [Sexp.of_string "OUT"; out_asxs];] in
    Sexp.List [res; bbs; asxs]
  let to_string t = Sexp.to_string_hum (sexp_of_t t)
end;;

module BBCmpResPlain = BBCmpResRich;;

(* given a bb and its program, locate its function and its vertex *)
let get_bb_ctx p bb =
  let open Ktype in
  let af = Hashtbl.find p.pfuncs bb.Bb.bb_fbegin in
  let vertex = Cfg.SSA.find_vertex af.cfg bb.Bb.id in
  (af, vertex)

let accept_as_seed_both_entry ~bb1 ~bb2 =
  (bb1.Bb.id = Cfg.BB_Entry) && (bb2.Bb.id = Cfg.BB_Entry)

let accept_as_seed_left_entry ~bb1 ~bb2 =
  bb1.Bb.id = Cfg.BB_Entry

module Accept_expansions (BBCmp : BBCmpResSig) =
struct
  let accept_expansion_permissive_consistent ~nonexact nbbcmp =
    let n = "accept_expansion_permissive_consistent" in
    let nstr = BBCmp.to_string nbbcmp in
    let nres = BBCmp.res nbbcmp in

    (* What (if any) was the first nonexact match we ran into? *)
    match nonexact with
    | None -> (* Haven't seen any non-exact matches so far *)
      begin
        match nres with
        | Exact _
        | Subset _
        | Superset _ ->
          dprintf "%s: accepting %s [no non-exact matches so far]"
            n (BBCmp.to_string nbbcmp);
          true
        | _ ->
          false
      end
    | Some accept_limitation ->
      begin
        match accept_limitation, nres with
        | Exact _, _ ->
          failwith "accept_limitation is Exact"
        | _, Exact _ ->
          dprintf "%s: accepting %s [Exact]" n nstr;
          true
        | Subset _, Subset _ ->
          dprintf "%s: accepting %s [Subset]" n nstr;
          true
        | Superset _, Superset _ ->
          dprintf "%s: accepting %s [Superset]" n nstr;
          true
        | _ ->
          dprintf "%s: rejecting %s" n nstr;
          false
      end
  (*
   * TBD: also provide a less-fuzzy mode where we hook into
   * the expansion logic and only accept partials immediately
   * bordering our Exact/Subset/Superset 'core' match.
   *)
  let accept_expansion_all_partials ~nonexact nbbcmp =
    match BBCmp.res nbbcmp with
    | Fail -> false
    | _ -> true
end

module type CfgMatchingPolicy =
sig
  module BBCmp : BBCmpResSig
  val accept_as_seed : bb1:Bb.bb_summary -> bb2:Bb.bb_summary -> bool
  val accept_expansion : nonexact:bbcmp_res option -> BBCmp.t -> bool
end

module WholeFunctionMatchingPolicy(BBCmp : BBCmpResSig) =
struct
  module BBCmp = BBCmp
  let accept_as_seed = accept_as_seed_both_entry
  let accept_expansion =
    let module AE = Accept_expansions(BBCmp) in
    AE.accept_expansion_permissive_consistent
end

module ExhaustiveMatchingPolicy(BBCmp : BBCmpResSig) =
struct
  module BBCmp = BBCmp
  let accept_as_seed ~bb1 ~bb2 = true
  let accept_expansion =
    let module AE = Accept_expansions(BBCmp) in
    AE.accept_expansion_permissive_consistent
end

module FuzzyInlineMatchingPolicy(BBCmp : BBCmpResSig) =
struct
  module BBCmp = BBCmp
  let accept_as_seed = accept_as_seed_left_entry
  let accept_expansion =
    let module AE = Accept_expansions(BBCmp) in
    AE.accept_expansion_all_partials
end

let matchingpolicyfactory bbcmp str =
  let module BBCmp = (val bbcmp : BBCmpResSig) in
  match str with
  | "exhaustive" -> (module ExhaustiveMatchingPolicy(BBCmp) : CfgMatchingPolicy)
  | "whole-function" -> (module WholeFunctionMatchingPolicy(BBCmp) : CfgMatchingPolicy)
  | "fuzzy-inline" -> (module FuzzyInlineMatchingPolicy(BBCmp) : CfgMatchingPolicy)
  | _ -> failwith (Printf.sprintf "Unrecognized matching policy: %s" str)

open Cfg_convenience;;

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

module MatchingSubgraph(BBCmp : BBCmpResSig) (Policy : CfgMatchingPolicy with module BBCmp = BBCmp) : MatchingSubgraphSig
=
struct
  open Cmpres
  module Flags =
  struct
    type t = func_cmp_flags
    let compare = compare
    let to_string = function
      | FIdenticalFunctions -> "FIdenticalFunctions"
      | FIsomorphicVanilla -> "FIsomorphicVanilla"
      | FIsomorphicFinal -> "FIsomorphicFinal"
  end
  module FlagsSet = BatSet.Make(Flags)
  module BBCmp = BBCmp
  type bbcmp = BBCmp.t
  type matched_edge = {
    src : Cfg.bbid;
    dst : Cfg.bbid;
  }
  type t = {
    af1 : Ktype.analyzed_func;
    af2 : Ktype.analyzed_func;
    flags : FlagsSet.t;
    bbcmps : bbcmp list;
    edgepairs : (matched_edge * matched_edge) list;
    first_nonexact_res : bbcmp_res option;
  }
  exception Conflict_on_asx_prop of string

  let edgepairs_cmp a b =
    let string_of_edgepair (e1, e2) =
      let s = Cfg.bbid_to_string in
      Printf.sprintf "%s-%s-%s-%s" (s e1.src) (s e1.dst) (s e2.src) (s e2.dst)
    in
    String.compare (string_of_edgepair a) (string_of_edgepair b)

  let subgraph_cmp ~cfg1 ~cfg2 bbcmps =
    let cfgsize cfg = Cfg.SSA.G.nb_vertex cfg in
    let partial = Partial (-1, -1) in
    let subset = Subset (-1, -1) in
    let superset = Superset (-1, -1) in
    let exact = Exact (-1.) in
    let fuzziness () =
      let cnt, sum, n_partial, n_sub, n_sup =
        List.fold_left (fun (cnt, sum, n_partial, n_sub, n_sup) bbcmp ->
            match BBCmp.res bbcmp with
            | Partial (matched, available) ->
              (cnt + 1, ((float matched) /. (float available)) +. sum, n_partial + 1, n_sub, n_sup)
            | Subset (matched, available) ->
              (cnt + 1, ((float matched) /. (float available)) +. sum, n_partial, n_sub + 1, n_sup)
            | Superset (matched, available) ->
              (cnt + 1, ((float matched) /. (float available)) +. sum, n_partial, n_sub, n_sup + 1)
            | Exact _ ->
              (cnt + 1, 1. +. sum, n_partial, n_sub, n_sup)
            | Fail ->
              failwith "Found Fail while calculating fuzziness")
          (0, 0., 0, 0, 0) bbcmps
      in
      let counts = {n_total = cnt; n_partial; n_sub; n_sup;} in
      (sum /. (float cnt), counts)
    in
    let resultset =
      List.fold_left (fun set bbcmp ->
          let res = match BBCmp.res bbcmp with
            | Exact _ -> exact
            | Partial _ -> partial
            | Subset _ -> subset
            | Superset _ -> superset
            | Fail -> Fail in
          BatSet.add res set) BatSet.empty bbcmps
    in
    assert (not (BatSet.mem Fail resultset));

    let nmatches = List.length bbcmps in
    let s1 = cfgsize cfg1 in
    let s2 = cfgsize cfg2 in
    dprintf "s1 = %d, s2 = %d\n" s1 s2;
    let fuzziness =
      match (BatSet.mem partial resultset),
            (BatSet.mem subset resultset),
            (BatSet.mem superset resultset) with
      | true, _, _ -> Fuzzy (fuzziness ())
      | false, true, true -> Fuzzy (fuzziness ())
      | false, true, false -> SubsetAndExact
      | false, false, true -> SupersetAndExact
      | false, false, false -> ExactOnly
    in
    let overlap =
      if ((s1 = s2) && (s1 = nmatches)) then
        OverlapTotal nmatches
      else if ((nmatches = s2) && (s1 > s2)) then
        OverlapSuperset nmatches
      else if ((nmatches = s1) && (s1 < s2)) then
        OverlapSubset nmatches
      else
        OverlapPartial (nmatches, max s1 s2)
    in
    {fuzziness; overlap}

  let calc_flags af1 af2 =
    try
      let stmts1 = Function.unmodified_stmts af1.Ktype.function_info in
      let stmts2 = Function.unmodified_stmts af2.Ktype.function_info in
      let cfg1 = Cfg_ast.of_prog stmts1 in
      let cfg2 = Cfg_ast.of_prog stmts2 in
      begin
        let flags = match Misc.astcfgs_isomorphic cfg1 cfg2 with
          | BatResult.Ok () ->
            begin
              (*
               * XXX: we should be shouting out a warning if the functions are
               * identical but our final result is not an Exact match (this
               * can legitimately happen, but we should definitely be drawing
               * attention to such cases).
               *)
              match Misc.astcfgs_identical cfg1 cfg2 with
              | BatResult.Ok () ->
                (*
                 * Identical supersedes vanilla isomorphic, don't add the latter
                 * when we already have the former, it would just be noise.
                 *)
                FlagsSet.add FIdenticalFunctions FlagsSet.empty
              | BatResult.Bad reason ->
                (*
                 * Make sure we emit a greppable diagnostic so that one can debug
                 * Misc.functions_identical
                 *)
                dprintf "calc_flags: %s NOT identical to %s (%s)"
                  (Function.to_string af1.Ktype.function_info)
                  (Function.to_string af2.Ktype.function_info)
                  reason;
                FlagsSet.add FIsomorphicVanilla FlagsSet.empty
            end
          | BatResult.Bad _ ->
            dprintf "calc_flags: astcfg for %s NOT identical to %s (%s)"
              (Function.to_string af1.Ktype.function_info)
              (Function.to_string af2.Ktype.function_info)
              "Not isomorphic";
            FlagsSet.empty
        in
        let cfg1 = Function.ssacfg af1.Ktype.function_info in
        let cfg2 = Function.ssacfg af2.Ktype.function_info in
        match Misc.ssacfgs_isomorphic cfg1 cfg2 with
        | BatResult.Ok () -> FlagsSet.add FIsomorphicFinal flags
        | BatResult.Bad _ -> flags
      end
    with Not_found ->
      failwith "Internal error: no unmodified statements for functions"

  let create (af1, af2) bbcmps =
    {
      af1; af2; bbcmps;
      flags = calc_flags af1 af2;
      edgepairs = [];
      first_nonexact_res = None;
    }
  let size subg = List.length subg.bbcmps
  let res subg =
    let cfg1 = Function.ssacfg subg.af1.Ktype.function_info in
    let cfg2 = Function.ssacfg subg.af2.Ktype.function_info in
    subgraph_cmp ~cfg1 ~cfg2 subg.bbcmps
  let flags subg = subg.flags
  let flags_to_str flags =
    let flags = FlagsSet.enum flags in
    Print.enum_to_string ~enclosing:("", "") Flags.to_string flags
  let sexp_of_edgep (me1, me2) =
    let sexp_of_me {src; dst} =
      Sexp.List [Sexp.of_string "E";
                 Sexp.of_string (Cfg.bbid_to_string src);
                 Sexp.of_string (Cfg.bbid_to_string dst);]
    in
    let me1 = sexp_of_me me1 in
    let me2 = sexp_of_me me2 in
    Sexp.List [Sexp.of_string "EP"; me1; me2]
  let bbcmps_sort bbcmps = List.sort BBCmp.compare bbcmps

  let sexp_of_t subg =
    (*
     * XXX: should be using to_string here, but too much work to update
     * the expected strings in the testcases ATM.
     *)
    let func1 = Function.symbols_to_str subg.af1.Ktype.function_info in
    let func2 = Function.symbols_to_str subg.af2.Ktype.function_info in
    let funcs = Sexp.List [Sexp.of_string "functions";
                           Sexp.List [Sexp.Atom func1;
                                      Sexp.Atom func2]]
    in
    let cmpres = cfgcmp_res_to_sexp (res subg) in
    let bbcmps = Std.sexp_of_list BBCmp.sexp_of_t (bbcmps_sort subg.bbcmps) in
    let bbcmp = Sexp.List [Sexp.of_string "bbcmps"; bbcmps] in
    let edgeps = Std.sexp_of_list sexp_of_edgep (List.sort edgepairs_cmp subg.edgepairs) in
    let edgep = Sexp.List [Sexp.of_string "edgepairs"; edgeps] in
    Sexp.List [Sexp.of_string "subgraph"; funcs; cmpres; bbcmp; edgep;]
  let to_string subg =
    let open BatPervasives in
    subg |> sexp_of_t |> Sexp.to_string_hum
  let includes_any_of_edgep subg edgep =
    let module G = Cfg.SSA.G in
    let edgep_src1 = (fst edgep).src in
    let edgep_dst1 = (fst edgep).dst in
    let edgep_src2 = (snd edgep).src in
    let edgep_dst2 = (snd edgep).dst in
    try
      let _ = List.find (fun (medge1, medge2) ->
          let src1 = medge1.src in
          let dst1 = medge1.dst in
          let src2 = medge2.src in
          let dst2 = medge2.dst in
          ((dst1 = edgep_dst1) && (src1 = edgep_src1)) ||
          ((dst2 = edgep_dst2) && (src2 = edgep_src2))) subg.edgepairs in
      true
    with Not_found -> false

  let includes_bbids subg (bbidl, bbidr) =
    let open Bb in
    try
      let ret = List.find (fun cmpres ->
          let (bb1, bb2) = BBCmp.bbp cmpres in
          (bb1.id = bbidl) && (bb2.id = bbidr)) subg.bbcmps in
      Some ret
    with Not_found -> None

  let includes_bbp subg (bbl, bbr) =
    let open Bb in
    try
      let ret = List.find (fun cmpres ->
          let (bb1, bb2) = BBCmp.bbp cmpres in
          (bb1.id = bbl.id) && (bb2.id = bbr.id)) subg.bbcmps in
      Some ret
    with Not_found -> None
  let includes_bbl subg bbl =
    try
      let ret = List.find (fun bbcmp ->
          let (a, _) = BBCmp.bbp bbcmp in
          a.Bb.id = bbl.Bb.id) subg.bbcmps in
      Some ret
    with Not_found -> None
  let includes_bbr subg bbr =
    try
      let ret = List.find (fun bbcmp ->
          let (_, b) = BBCmp.bbp bbcmp in
          b.Bb.id = bbr.Bb.id) subg.bbcmps in
      Some ret
    with Not_found -> None
  let add subg cmp =
    let do_add subg cmp =
      let bbp = BBCmp.bbp cmp in
      dprintf "adding (%s, %s) to the matched fragment"
        (Cfg.bbid_to_string (fst bbp).Bb.id) (Cfg.bbid_to_string (snd bbp).Bb.id);
      if None <> (includes_bbp subg bbp) then begin
        let module C = Cfg.SSA in
        let (a, b) = bbp in
        let (av, bv) = (Ktype.bb2v subg.af1 a, Ktype.bb2v subg.af2 b) in
        dprintf "subgraph: %s" (to_string subg);
        dprintf "Trying to add bbp (%s, %s)" (Cfg.SSA.v2s av) (Cfg.SSA.v2s bv);
        failwith "tried to re-add visited bb";
      end;
      let nbbcmps = cmp :: subg.bbcmps in
      let open Ktype in
      Some {subg with bbcmps = nbbcmps;}
    in
    let nonexact = subg.first_nonexact_res in
    if Policy.accept_expansion ~nonexact cmp then begin
      (* If necessary, update subg.first_nonexact_res *)
      let subg = match nonexact, BBCmp.res cmp with
        | None, Exact _ -> subg
        | None, res -> {subg with first_nonexact_res = Some res}
        | _ -> subg
      in
      do_add subg cmp
    end else begin
      None
    end
  let includes_vertex_l subg v =
    try
      let ret = List.find (fun bbcmp ->
          let (a, _) = BBCmp.bbp bbcmp in
          a.Bb.id = v) subg.bbcmps in
      Some ret
    with Not_found -> None
  let includes_vertex_r subg v =
    try
      let ret = List.find (fun bbcmp ->
          let (_, b) = BBCmp.bbp bbcmp in
          b.Bb.id = v) subg.bbcmps in
      Some ret
    with Not_found -> None

  let do_find_bbp subg selecta descr bbid =
    let bbp2str (l, r) = Printf.sprintf "(%s, %s)"
        (Cfg.bbid_to_string l.Bb.id)
        (Cfg.bbid_to_string r.Bb.id)
    in
    let bbps = List.map BBCmp.bbp subg.bbcmps in
    match List.filter selecta bbps with
    | [] -> None
    | [bbp] -> Some bbp
    | bbps ->
      let bbpstr = Print.list_to_string ~sep:"; " bbp2str bbps in
      let str = Printf.sprintf "bb %s is a %s component of multiple bbps: %s"
          (Cfg.bbid_to_string bbid) descr bbpstr
      in
      failwith str

  let find_bbp_l subg bbid =
    let sel (l, _) = l.Bb.id = bbid in
    do_find_bbp subg sel "left" bbid

  let find_bbp_r subg bbid =
    let sel (_, r) = r.Bb.id = bbid in
    do_find_bbp subg sel "right" bbid

  let add_edgepair subg edgep =
    let open BatPervasives in
    dprintf "add_edgepair %s" (edgep |> sexp_of_edgep |> Sexp.to_string);
    assert(not (includes_any_of_edgep subg edgep));
    let (e_l, e_r) = edgep in
    ignore (match find_bbp_l subg e_l.src with
        | None -> failwith "XXX"
        | Some (l, r) ->
          assert (l.Bb.id = e_l.src);
          assert (r.Bb.id = e_r.src));
    ignore (match find_bbp_l subg e_l.dst with
        | None -> failwith "XXX"
        | Some (l, r) ->
          assert (l.Bb.id = e_l.dst);
          assert (r.Bb.id = e_r.dst));
    {subg with edgepairs = (edgep::subg.edgepairs)}
  let afs subg = (subg.af1, subg.af2)
  let map_bbcmps subg f =
    {subg with bbcmps = List.map f subg.bbcmps}
  let diff_bbcmps g_a g_b =
    let in_b bbcmp =
      try
        let _ = List.find (BBCmp.equal bbcmp) g_b.bbcmps in
        true
      with Not_found -> false
    in
    List.filter (fun bbcmp_a ->
        not (in_b bbcmp_a)) g_a.bbcmps
  let bbcmp_preds subg bbcmp =
    let (bb, bb') = BBCmp.bbp bbcmp in
    let pred_edgeps = List.filter (fun (edge, edge') ->
        if edge.dst = bb.Bb.id then begin
          if edge'.dst <> bb'.Bb.id then begin
            let str = Printf.sprintf
                "edge.dst: %s, edge'.dst: %s, bb.id: %s, bb'.id: %s"
                (Cfg.bbid_to_string edge.dst)
                (Cfg.bbid_to_string edge'.dst)
                (Cfg.bbid_to_string bb.Bb.id)
                (Cfg.bbid_to_string bb'.Bb.id)
            in
            failwith str
          end;
          true
        end else
          false
      ) subg.edgepairs in
    List.map (fun edgep ->
        let (edge, edge') = edgep in
        (edge.src, edge'.src)) pred_edgeps

  let bbcmp_succs subg bbcmp =
    let (bb, bb') = BBCmp.bbp bbcmp in
    let succ_edgeps = List.filter (fun (edge, edge') ->
        if edge.src = bb.Bb.id then begin
          if edge'.src <> bb'.Bb.id then begin
            let str = Printf.sprintf
                "edge.src: %s, edge'.src: %s, bb.id: %s, bb'.id: %s"
                (Cfg.bbid_to_string edge.src)
                (Cfg.bbid_to_string edge'.src)
                (Cfg.bbid_to_string bb.Bb.id)
                (Cfg.bbid_to_string bb'.Bb.id)
            in
            failwith str
          end;
          true
        end else
          false
      ) subg.edgepairs in
    List.map (fun edgep ->
        let (edge, edge') = edgep in
        (edge.dst, edge'.dst)) succ_edgeps

  (*
   * Do fixed-point iteration to propagate the IN/OUT assumptions
   * to the edges of the matched fragment
   *)
  let fpit_assumptions subg =
    let bbp2idp (bb1, bb2) = (bb1.Bb.id, bb2.Bb.id) in
    let bbp2str (bb1, bb2) = Printf.sprintf "(%s, %s)"
        (Cfg.bbid_to_string bb1.Bb.id) (Cfg.bbid_to_string bb2.Bb.id) in
    let import_bbcmps subg =
      let htbl = BatHashtbl.create (List.length subg.bbcmps) in
      List.iter (fun bbcmp ->
          let key = bbp2idp (BBCmp.bbp bbcmp) in
          BatHashtbl.add htbl key bbcmp) subg.bbcmps;
      htbl
    in
    let af1, af2 = afs subg in
    let vis1, vis2 = (af1.Ktype.visibility, af2.Ktype.visibility) in
    let bbcmpht = import_bbcmps subg in
    (*
     * We want to be able to modify the hashtable while iterating over it,
     * so iterate over the keys instead. We might replace the bbcmp associated
     * with a key, but keys themselves are never added/removed
    *)
    let keys = BatHashtbl.keys bbcmpht in
    BatEnum.force keys;

    let propagate_for_bbcmp (bbcmp : BBCmp.t) =
      let preds = bbcmp_preds subg bbcmp in
      let succs = bbcmp_succs subg bbcmp in
      let matchi = BBCmp.match_info bbcmp in
      let this_in = matchi.matched_direct.in_asxs in
      let this_out = matchi.matched_direct.out_asxs in
      let mods = ref 0 in
      let get_target_in mi = mi.matched_direct.in_asxs in
      let get_target_out mi = mi.matched_direct.out_asxs in
      let set_target_in mi n = {mi with matched_direct = {
          mi.matched_direct with in_asxs = n}} in
      let set_target_out mi n = {mi with matched_direct = {
          mi.matched_direct with out_asxs = n};} in
      let propagate_inner get_target_asxs set_target_asxs our_asxs targets =
        List.iter (fun key ->
            (* Look up the BB we're propagating _to_ *)
            let target_bbcmp = match Misc.bathashtbl_find_option bbcmpht key with
              | Some v ->
                v
              | None ->
                dprintf "subg so far: %s" (to_string subg);
                let str = Printf.sprintf "Oops, no value for key (%s, %s))!"
                    (Cfg.bbid_to_string (fst key)) (Cfg.bbid_to_string (snd key)) in
                failwith str (* Cannot possibly happen ;) *)
            in
            let target_bbp = BBCmp.bbp target_bbcmp in
            let target_mi = BBCmp.match_info target_bbcmp in
            let target_asxs = get_target_asxs target_mi in

            let prev_target_asxs = Assumptions.to_string target_asxs in
            let filtered = Assumptions.filter_vis our_asxs vis1 vis2
                ((fst target_bbp).Bb.id, (snd target_bbp).Bb.id) in
            dprintf "ASXS before filtering: %s" (Assumptions.to_string our_asxs);
            dprintf "ASXS after filtering: %s" (Assumptions.to_string filtered);
            match Assumptions.merge_equivs target_asxs filtered with
            | BatResult.Ok nasxs ->
              let nasxs_str = Assumptions.to_string nasxs in
              (* Are the assumptions different now? *)
              if 0 <> String.compare nasxs_str prev_target_asxs then begin
                let nmi = set_target_asxs target_mi nasxs in
                let ntarg = BBCmp.update_match_info target_bbcmp nmi in
                Hashtbl.replace bbcmpht (bbp2idp target_bbp) ntarg;
                mods := !mods + 1;
              end;
            | BatResult.Bad str ->
              let msg = Printf.sprintf "Conflict on propagating assumptions from \
                                        %s to %s: %s (tried to merge this:\n%s\n with target\n%s"
                  (bbp2str (BBCmp.bbp bbcmp)) (bbp2str target_bbp) str
                  (Assumptions.to_string our_asxs) prev_target_asxs in
              dprintf "%s" msg;
              raise (Conflict_on_asx_prop msg)
          ) targets
      in
      propagate_inner get_target_out set_target_out this_out succs;
      propagate_inner get_target_in set_target_in this_in preds;
      !mods
    in
    let propagateN () =
      BatEnum.fold (fun acc key ->
          let bbcmp = match Misc.bathashtbl_find_option bbcmpht key with
            | Some v -> v
            | None -> failwith "No BBCmp for key!"
          in
          let mods = propagate_for_bbcmp bbcmp in
          (acc + mods)
        ) 0 keys
    in
    let iterate count =
      let keep_going = ref true in
      let i = ref 1 in
      while !keep_going do
        let mods = propagateN () in
        if 0 = mods then
          keep_going := false;
        if !i > count then
          let str = Printf.sprintf "Fixed-point iteration failed to \
                                    settle after %d iterations" count in
          failwith str;
      done;
    in
    try
      iterate 30; (* XXX: this needs to be based on some size property *)
      let nbbcmps = BatList.of_enum (BatHashtbl.values bbcmpht) in
      Some {subg with bbcmps = nbbcmps}
    with Conflict_on_asx_prop str ->
      dprintf "Could not propagate assumptions: %s" str;
      None

  (*
   * Is the matched fragment the best that we could ever get
   * for this function pair so that we shouldn't consider
   * comparing BBs from the same respective functions to each
   * other again?
   *)
  (* XXX: should probably move this to the Policy *)
  let good_enough subg =
    match (res subg).overlap with
    | OverlapSubset _
    | OverlapSuperset _ ->
      true
    | OverlapPartial (n, d) ->
      let cfg1 = subg.af1.Ktype.cfg in
      let cfg2 = subg.af2.Ktype.cfg in
      let cfgsize cfg = Cfg.SSA.G.nb_vertex cfg in
      let s1 = cfgsize cfg1 in
      let s2 = cfgsize cfg2 in
      n > (s1 / 2) && n > (s2 / 2)
    | OverlapTotal _ ->
      true

  let collect_edge_bbs subg =
    let aux next degree =
      let open BatPervasives in
      let module P = BatPair in
      let bbcmps {bbcmps} = bbcmps in
      List.fold_left (fun acc bbcmp ->
          (* Collect the BB summaries *)
          let lbbsum, rbbsum = BBCmp.bbp bbcmp in
          (* Find the corresponding vertices in the CFG *)
          let af1, af2 = afs subg in
          let lv, rv = P.map (uncurry Ktype.bb2v) ((af1, lbbsum),(af2, rbbsum)) in
          (* Get the next BBs *)
          let lnext, rnext =
            P.map (uncurry next) ((af1.Ktype.cfg, lv), (af2.Ktype.cfg, rv)) in
          (* Filter all next BBs part of the fragment *)
          let v2l af = Cfg.SSA.G.V.label in
          let left bbmcp =
            let (bbsum, _) = BBCmp.bbp bbcmp in
            bbsum
          in
          let right bbcmp =
            let (_, bbsum) = BBCmp.bbp bbcmp in
            bbsum
          in
          let remove_fragments_bbs af bbs side =
            List.filter (fun bb ->
                let res = BatList.Exceptionless.find (fun bbcmp ->
                    let bbsum = side bbcmp in
                    (v2l af bb) = bbsum.Bb.id
                  ) (bbcmps subg) in
                match res with
                | Some _ -> false
                | None -> true
              ) bbs in
          (* Collect possible edge BBs *)
          let lnext' = remove_fragments_bbs af1 lnext left in
          let rnext' = remove_fragments_bbs af2 rnext right in
          (match lnext',rnext' with
           | h::t, h'::t' ->
             bbcmp :: acc
           | h::t, [] ->
             if (degree af2.Ktype.cfg rv) = 0
             then bbcmp :: acc
             else acc
           | [], h::t ->
             if (degree af1.Ktype.cfg lv) = 0
             then bbcmp :: acc
             else acc
           | [], [] ->
             if ((degree af1.Ktype.cfg lv) = 0) &&
                ((degree af2.Ktype.cfg rv) = 0)
             then bbcmp :: acc
             else acc)
        ) [] (bbcmps subg)
    in
    let collect_entry_bbs =
      aux Cfg.SSA.G.pred Cfg.SSA.G.in_degree
    in
    let collect_exit_bbs =
      aux Cfg.SSA.G.succ Cfg.SSA.G.out_degree
    in
    (collect_entry_bbs, collect_exit_bbs)

  (* Clumsily escape foo.part.1 symbol names *)
  let escape_fname = Str.global_replace (Str.regexp "\\.") "___"

  let nodename prefix af bbid =
    let open Ktype in
    let fname = Function.symbols_to_str af.function_info in
    let fname = escape_fname fname in
    let bbname = Cfg.bbid_to_string (Cfg.SSA.G.V.label bbid) in
    Printf.sprintf "%s_%s_%s" prefix fname bbname

  type accessors = {
    get_af : Ktype.analyzed_func;
    get_bbcmp : Bb.bb_summary -> bbcmp;
    get_bgcolor : string;
  }
  type leftright =
    | Left
    | Right

  let get_accessors subg lr =
    let (af, gbbcmp, bgcol, descr) = match lr with
      | Left ->
        let af = fst (afs subg) in
        (af, includes_bbl, "grey", "left")
      | Right ->
        let af = snd (afs subg) in
        (af, includes_bbr, "antiquewhite2", "right")
    in
    {
      get_af = af;
      get_bbcmp = (fun bbsum ->
          BatOption.get (gbbcmp subg bbsum)
        );
      get_bgcolor = bgcol;
    }

  let dump_ssa af =
    let module CS = Cfg.SSA in
    let g = af.Ktype.cfg in
    let buf = Buffer.create 1000 in
    let ft = Format.formatter_of_buffer buf in
    let pp = new Pp.pp ft in
    let pr = Buffer.add_string buf in
    (fun b ->
       let stmts = CS.get_stmts g b in
       pr(Cfg.bbid_to_string (Cfg.SSA.G.V.label b));
       pr "\n";
       pp#ssa_stmts stmts;
       Format.pp_print_flush ft ();
       let o = Buffer.contents buf in
       Buffer.clear buf;
       o)
  let dump_cfg_edge prefix af =
    let module CS = Cfg.SSA in
    let buf = Buffer.create 1000 in
    let ft = Format.formatter_of_buffer buf in
    let pr = Buffer.add_string buf in
    let el2s = function
      | Some true -> " [label \"t\"];"
      | Some false -> " [label \"f\"];"
      | None -> ";"
    in
    (fun e ->
       let label = CS.G.E.label e in
       let src = CS.G.E.src e in
       let dst = CS.G.E.dst e in
       pr(nodename prefix af src);
       pr " -> ";
       pr(nodename prefix af dst);
       pr(el2s label);
       Format.pp_print_flush ft ();
       let o = Buffer.contents buf in
       Buffer.clear buf;
       o)

  let bb_node_attrs v accs =
    let af = accs.get_af in
    let bbsum = Ktype.v2bb af v in
    try
      let bbcmp = accs.get_bbcmp bbsum in
      match BBCmp.res bbcmp with
      | Exact _ -> "style=filled fillcolor=green"
      | Subset _ -> "style=filled fillcolor=yellow"
      | Superset _ -> "style=filled fillcolor=orange"
      | _ -> ""
    with _ -> ""

  let dump_cfg prefix oc accs =
    let module C = Cfg.SSA in
    let module G = C.G in
    let open Ktype in
    let af = accs.get_af in
    let g = af.cfg in
    let fname = Function.symbols_to_str af.function_info in
    let fname = escape_fname fname in
    Printf.fprintf oc "subgraph cluster_%s_%s {\n" prefix fname;
    Printf.fprintf oc "label=\"%s\";\n" (String.escaped fname);
    Printf.fprintf oc "node [shape=box]\n";
    Printf.fprintf oc "style=filled;\nfillcolor=\"%s\";\n" accs.get_bgcolor;
    G.iter_vertex (fun v ->
        let str = dump_ssa af v in
        let str = String.escaped str in
        let node = nodename prefix af v in
        let extra_attrs = bb_node_attrs v accs in
        Printf.fprintf oc "%s [label=\"%s\" %s];\n" node str extra_attrs) g;
    G.iter_edges_e (fun edge ->
        let str = dump_cfg_edge prefix af edge in
        Printf.fprintf oc "%s\n" str) g;
    Printf.fprintf oc "} /* end subgraph %s */\n" fname

  let dump subg oc =
    dprintf "FRAGDUMP";
    let open Ktype in
    let pref1 = "prog1" in
    let pref2 = "prog2" in
    let af1, af2 = afs subg in

    let dump_pairing bbcmp =
      let bb1, bb2 = BBCmp.bbp bbcmp in
      let v1 = Ktype.bb2v af1 bb1 in
      let v2 = Ktype.bb2v af2 bb2 in
      let n1 = nodename pref1 af1 v1 in
      let n2 = nodename pref2 af2 v2 in
      Printf.fprintf oc "%s -> %s [style=bold constraint=false dir=both];\n" n1 n2
    in
    let pp_vars vs =
      let str = Print.list_to_string ~enclosing:("{", "}") ~sep:", "
          (Ssa_ext.Variable.to_string ~breaks:false) vs
      in
      String.escaped str
    in
    let dump_tf_pairings bbcmp =
      let bb1, bb2 = BBCmp.bbp bbcmp in
      let tfs1 = BatOption.get bb1.Bb.tfs in
      let tfs2 = BatOption.get bb2.Bb.tfs in
      let matchi = BBCmp.match_info bbcmp in
      let mexprs = matchi.matched_direct in
      let missing1 = matchi.missing1 in
      let missing2 = matchi.missing2 in
      let out_asxs = mexprs.out_asxs in
      let iter_over_tfs f outvars tfs =
        List.iter (fun ovar ->
            let module StringMap = BatMap.Make(String) in
            let varname = Ssa_ext.Variable.to_string ovar in
            try
              let tf = StringMap.find varname tfs in
              f tf
            with Not_found -> ()
          ) outvars
      in
      let subgraph_name = Printf.sprintf "%s_%s"
          (Cfg.bbid_to_string bb1.Bb.id) (Cfg.bbid_to_string bb2.Bb.id) in
      let pref1 = Printf.sprintf "%s_%s" pref1 subgraph_name in
      let pref2 = Printf.sprintf "%s_%s" pref2 subgraph_name in
      Printf.fprintf oc "subgraph cluster_%s {\n" subgraph_name;
      Printf.fprintf oc "label=\"%s\"\n" subgraph_name;
      Printf.fprintf oc "style=solid;\n"; (* Ugh this doesn't work *)
      let i = ref 0 in
      Assumptions.fold_left (fun () (outvars1, outvars2) ->
          Printf.fprintf oc "subgraph cluster_%s_asx%d {\n" subgraph_name !i;
          Printf.fprintf oc "style=filled;\n"; (* Ugh this doesn't work *)
          Printf.fprintf oc "fillcolor=yellowgreen;\n"; (* Ugh this doesn't work *)
          Printf.fprintf oc "label=\"%s <-> %s\";\n"
            (pp_vars outvars1) (pp_vars outvars2);
          let pref1 = Printf.sprintf "%s_%d" pref1 !i in
          iter_over_tfs (fun tf ->
              Transfer_function.to_dot oc pref1 ~serial:(!i) tf) outvars1 tfs1;
          i := !i + 1;
          let pref2 = Printf.sprintf "%s_%d" pref2 !i in
          iter_over_tfs (fun tf ->
              Transfer_function.to_dot oc pref2 ~serial:(!i) tf) outvars2 tfs2;
          i := !i + 1;
          Printf.fprintf oc "} /* end subgraph asx%d */\n" !i
        ) () out_asxs;
      let do_missing pref descr tfs =
        Printf.fprintf oc "subgraph cluster_%s_%s {\n" subgraph_name descr;
        Printf.fprintf oc "label=\"%s\";\n" descr;
        List.iter (fun tf ->
            i := !i + 1;
            Printf.fprintf oc "subgraph cluster_%s_%s_%d {\n" subgraph_name descr !i;
            let vn = Ssa_ext.Variable.name tf.Transfer_function.output in
            Printf.fprintf oc "label=\"%s\";\n" vn;
            Transfer_function.to_dot oc pref ~serial:(!i) tf;
            Printf.fprintf oc "} /* end subgraph cluster_%s_%s_%d */\n" subgraph_name descr !i;
          ) tfs;
        Printf.fprintf oc "} /* end subgraph cluster_%s_%s */\n" subgraph_name descr;
      in
      do_missing pref1 "missing1" missing1;
      do_missing pref2 "missing2" missing2;
      Printf.fprintf oc "} /* end subgraph %s */\n" subgraph_name
    in

    Printf.fprintf oc "digraph toplevel {\n";
    let res_class = cfgcmp_res_to_string (res subg) in
    Printf.fprintf oc "label=\"Result classification: %s\"\n" res_class;
    dump_cfg pref1 oc (get_accessors subg Left);
    dump_cfg pref2 oc (get_accessors subg Right);

    List.iter dump_pairing subg.bbcmps;
    List.iter dump_tf_pairings subg.bbcmps;
    Printf.fprintf oc "} /* end toplevel */\n";
end

class bbcmp_stats desc =
  object(self)
    val mutable total = 0
    val mutable partial_match = 0
    val mutable exact_match = 0
    val mutable subset = 0
    val mutable superset = 0
    method get_total = total
    method get_partial_match = partial_match
    method get_exact_match = exact_match
    method get_subset = subset
    method get_superset = superset
    method add_res res =
      total <- total + 1;
      match res with
      | Exact _ -> exact_match <- exact_match + 1
      | Partial _ -> partial_match <- partial_match + 1
      | Subset _ -> subset <- subset + 1
      | Superset _ -> superset <- superset + 1
      | Fail -> ()
    method pp ft =
      let open Format in
      pp_open_hbox ft ();
      fprintf ft "%s\n" desc;
      pp_open_vbox ft 2;
      fprintf ft "\ttotal: %d\n" total;
      fprintf ft "\tpartial: %d\n" partial_match;
      fprintf ft "\tsubset: %d\n" subset;
      fprintf ft "\tsuperset: %d\n" superset;
      fprintf ft "\texact: %d\n" exact_match;
      pp_close_box ft ();
      pp_close_box ft ();
      pp_print_newline ft ();
    method add (stats: bbcmp_stats) =
      total <- total + stats#get_total;
      partial_match <- partial_match + stats#get_partial_match;
      exact_match <- exact_match + stats#get_exact_match;
      subset <- subset + stats#get_subset;
      superset <- superset + stats#get_superset;
      self;
  end

let tf_to_str tf =
  let v = Ssa_ext.Variable.to_string tf.Transfer_function.output in
  let f = Ssa_ext.Expression.to_string tf.Transfer_function.f in
  let n = Ssa_ext.VariableSet.cardinal tf.Transfer_function.inputs in
  Printf.sprintf "<%s>:%s:[ninp=%d]" v f n

let rec domtree_to_sexp af v =
  let open Ktype in
  let imm_dominees = af.dominfo.SsaDom.dom_tree v in
  let this = Sexp.of_string (Cfg.SSA.v2s v) in
  match imm_dominees with
  | [] -> this
  | _ ->
    Sexp.List [this; (Std.sexp_of_list (domtree_to_sexp af) imm_dominees)]

let domtree_to_string af v = Sexp.to_string_hum (domtree_to_sexp af v)

let afs_of_progs_bbs (p1, p2) (bb1, bb2) =
  let (af1, _) = get_bb_ctx p1 bb1 in
  let (af2, _) = get_bb_ctx p2 bb2 in
  (af1, af2)

module BbInsnMemo =
struct
  type k = (Ktype.analyzed_prog * Bb.bb_summary)
  type v = int option
  type priv = unit
  let lookup () (p, bb) =
    try
      let af = Hashtbl.find p.Ktype.pfuncs bb.Bb.bb_fbegin in
      Some (Bb.nr_insns af.Ktype.cfg bb)
    with Not_found ->
      failwith "Failed to get func for BB"
  let finalize _ = ()
  let k_to_string (p, bb) =
    Printf.sprintf "%s:%#Lx:%s" p.Ktype.pname bb.Bb.bb_fbegin
      (Cfg.bbid_to_string bb.Bb.id)
end
module InsnMemo = Memo.MakeSingleMemoizer(BbInsnMemo)

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
    (Policy : CfgMatchingPolicy)
  : AlgoSig
    with type bbcluster_key := Bb_cluster.ClusterHashtbl.key
     and type bbcluster_type := BBMgr.t
= struct
  type t = unit
  exception Edge_mismatch
  exception Edge_assumptions_mismatch
  module Subgraph = MatchingSubgraph(Policy.BBCmp)(Policy)
  module BBCmp = Subgraph.BBCmp
  type subgraph = Subgraph.t
  type prog_summary = (Ktype.analyzed_prog * BBMgr.t)
  type directed_edge = {
    get_neighbor_edges : Cfg.SSA.G.t -> Cfg.SSA.G.V.t -> Cfg.SSA.G.E.t list;
    get_neighbor : Cfg.SSA.G.E.t -> Cfg.SSA.G.V.t;
    get_this : Cfg.SSA.G.E.t -> Cfg.SSA.G.V.t;
    get_our_asxs : matched_exprs -> Assumptions.t;
    get_their_asxs : matched_exprs -> Assumptions.t;
    set_our_asxs : matched_exprs -> Assumptions.t -> matched_exprs;
    set_their_asxs : matched_exprs -> Assumptions.t -> matched_exprs;
  }
  module C = Cfg.SSA
  module G = C.G

  let init () = ()

  let insnmemo_l = InsnMemo.create ()
  let insnmemo_r = InsnMemo.create ()
  let get_insns ~p1 ~p2 ~bb1 ~bb2 =
    match InsnMemo.lookup insnmemo_l (p1, bb1),
          InsnMemo.lookup insnmemo_r (p2, bb2) with
    | Some n1, Some n2 -> Some (n1, n2)
    | _ -> failwith "Some InsnMemoLookup failed?"

  let tf_match assumptions tf tf' =
    let tf_str = tf_to_str tf in
    let tf_str' = tf_to_str tf' in
    let cmp lhs rhs =
      let (nassumptions, res) = Ssa_ext_cmp.chunks_equiv assumptions lhs rhs in
      if res then begin
        dprintf "BBcmp: matched %s with %s" tf_str tf_str';
        dprintf "ASSUMPTIONS: %s" (Assumptions.to_string nassumptions);
        Some (nassumptions, (tf, tf'))
      end else
        None
    in
    dprintf "comparing\n> %s\n> %s" tf_str tf_str';
    let n_inputs = Ssa_ext.VariableSet.cardinal tf.Transfer_function.inputs in
    let n_inputs' = Ssa_ext.VariableSet.cardinal tf'.Transfer_function.inputs in
    if false && (n_inputs <> n_inputs')
    then
      begin
        dprintf "shortcutting comparison";
        None
      end
    else
      cmp tf.Transfer_function.f tf'.Transfer_function.f

  let consolidate_tfs paired_tfs =
    let tfp_to_str (tf, tf') =
      Printf.sprintf "[%s, %s]" (tf_to_str tf) (tf_to_str tf')
    in
    let tfps_to_str tfps = Print.list_to_string ~enclosing:("<", ">") ~sep:"|" tfp_to_str tfps in
    let buckets_to_str bs = Print.list_to_string ~enclosing:("B<", ">B") ~sep:"|B|" tfps_to_str bs in
    (*
      We generate a list of "buckets", each bucket being a list
      of TFs which are equivalent.
    *)
    let consolidate buckets tf_pair =
      (* Note note note: we consolidate TFs of the /same/ BB *)
      let cmp_nonconst tf1 tf2 =
        if 0 <> (Ssa_ext.VariableSet.cardinal tf1.Transfer_function.inputs) then
          (* only look at constant TFs for now *)
          None
        else
          tf_match Assumptions.empty tf1 tf2
      in
      let (tf, tf') = tf_pair in
      (* We only need look at the LHS TFs (i.e. tf, not tf') to
               consolidate. For each bucket, check if tf should be added
               to it. If not, add it to its own bucket *)
      let new_bucket = ref true in
      let buckets' = List.map (fun bucket ->
          let (one, _) = List.hd bucket in
          match cmp_nonconst one tf with
          | Some (_, _) (* XXX: in assumptions *) ->
            new_bucket := false;
            (* XXX: stupid. Need to stop iterating now *)
            (tf_pair :: bucket)
          | None ->
            bucket
        ) buckets in
      match !new_bucket with
      | true -> [tf_pair] :: buckets'
      | false -> buckets'
    in
    let ret = List.fold_left consolidate [] paired_tfs in
    if (List.length ret) <> (List.length paired_tfs) then begin
      dprintf "consolidate_tfs: %d -> %d" (List.length paired_tfs) (List.length ret);
      dprintf "before:\n%s\n" (tfps_to_str paired_tfs);
      dprintf "after:\n%s\n" (buckets_to_str ret);
    end;
    ret

  let find_pairing assumptions tfs tfs' =
    let open Ssa_ext in
    let (in_asxs, paired_tfs, missing1, missing2) =
      Misc.lists_do_match assumptions tfs tfs' tf_match in
    let consolidated_tfs = consolidate_tfs paired_tfs in
    let tf_pairs_to_outv_list_pair tfps =
      let var_pair_list = List.map (fun (tf, tf') ->
          (tf.Transfer_function.output, tf'.Transfer_function.output)) tfps
      in
      BatList.split var_pair_list
    in
    let paired_out_var_buckets =
      List.map tf_pairs_to_outv_list_pair consolidated_tfs in
    let out_asxs = List.fold_left (fun maybe_asxs (var_list1, var_list2) ->
        match maybe_asxs with
        | BatResult.Ok asxs ->
          Assumptions.add_assumption asxs (var_list1, var_list2)
        | BatResult.Bad _ ->
          maybe_asxs)
        (BatResult.Ok Assumptions.empty) paired_out_var_buckets in
    match out_asxs with
    | BatResult.Bad str ->
      dprintf "Inconsistent assumptions: %s" str;
      (Assumptions.empty, Assumptions.empty, [], (tfs, tfs'))
    | BatResult.Ok out_asxs' ->
      (in_asxs, out_asxs', paired_tfs, (missing1, missing2))

  let get_bbaddr bb =
    BatOption.map_default (Printf.sprintf "%#Lx") "synthetic" bb.Bb.bb_saddr

  let sm_of_tf_list tfs =
    List.fold_left (fun sm tf ->
        let key = Ssa_ext.Variable.to_string (tf.Transfer_function.output) in
        StringMap.add key tf sm) StringMap.empty tfs

(*
  let try_against_invisible lr mi ~invisible =
    let msel, stillmsel, ivsel, stillmother, pairedsel, set_missing =
      match lr with
      | `LeftAgainstRightInv ->
        fst, fst, snd, snd, fst, (fun mi nm ->
            {mi with missing1 = nm})
      | `RightAgainstLeftInv ->
        snd, snd, fst, fst, snd, (fun mi nm ->
            {mi with missing2 = nm})
    in
    let missing = (sm_of_tf_list mi.missing1, sm_of_tf_list mi.missing2) in

    let sm2l sm = BatList.of_enum (StringMap.values sm) in
    let in_asxs = mi.matched_direct.in_asxs in
    let (in_asxs, out_asxs', paired_tfs, still_missing) =
      find_pairing in_asxs
        (sm2l (msel missing)) (sm2l (ivsel invisible))
    in
    let out_asxs = mi.matched_direct.out_asxs in
    let out_asxs = match Assumptions.merge_equivs out_asxs out_asxs' with
      | BatResult.Ok asxs ->
        asxs
      | BatResult.Bad str ->
        (* Can this happen? Let's find out! *)
        failwith "Could not merge out asxs!"
    in
    (* The still_missing TFs we get are what we couldn't pair from the
       _invisible_ TFs. To determine what's actually still missing, we
       need to filter out the just-matched TFs from the missing we got
       passed (on the appropriate side of course)
    *)
    let newly_paired = List.map (fun tf_pair -> pairedsel tf_pair) paired_tfs in
    let was_paired tf =
      let open Transfer_function in
      List.exists (fun tf' ->
          Ssa_ext.Variable.equal tf.output tf'.output) newly_paired
    in
    let nmissing = List.filter (fun missing_tf ->
        not (was_paired missing_tf)) (sm2l (msel missing))
    in
    let nrecovered = (StringMap.cardinal (msel missing)) - (List.length nmissing) in
    assert (nrecovered >= 0);

    let mi = set_missing mi nmissing in
    let mexprs = {mi.matched_direct with in_asxs; out_asxs;} in
    let mi = {mi with matched_direct = mexprs} in
    (nrecovered, mi)
*)
  (* Comparing against invisible is basically for similarity. Let's stick with
     equivalence for now. *)
  let try_against_invisible _ mi ~invisible =
    (0, mi)

  let do_compare_on_tfs ~bb1 ~tfs1 ~bb2 ~tfs2=
    (* BB pair comparison Round 1. Find direct equivalences between TFs *)
    let (in_asxs, out_asxs, _, (missing1, missing2)) =
      find_pairing Assumptions.empty
        (BatList.of_enum (StringMap.values tfs1))
        (BatList.of_enum (StringMap.values tfs2)) in
    dprintf "in_asxs[get_ret]: %s" (Assumptions.to_string in_asxs);
    let open Ssa_ext in
    let direct_matches = (StringMap.cardinal tfs1) - (List.length missing1) in
    assert(direct_matches = ((StringMap.cardinal tfs2) - (List.length missing2)));
    if debug () then begin
      Printf.printf "Pairings: %s" (Assumptions.to_string out_asxs);
      Printf.printf "]\n%!";
      Printf.printf "Missing1 (to complete %s): [\n" (Cfg.bbid_to_string bb1.Bb.id);
      List.iter (fun x -> Printf.printf "%s\n" (tf_to_str x)) missing1;
      Printf.printf "]\n%!";
      Printf.printf "Missing2 (to complete %s): [" (Cfg.bbid_to_string bb2.Bb.id);
      List.iter (fun x -> Printf.printf "%s\n" (tf_to_str x)) missing2;
      Printf.printf "]\n%!";
    end;
    let match_info = {
      matched_direct = {in_asxs; out_asxs};
      missing1;
      missing2;
    } in
    let invisible = (bb1.Bb.invisible_tfs, bb2.Bb.invisible_tfs) in
    let recovered1, match_info = try_against_invisible `LeftAgainstRightInv
        match_info ~invisible
    in
    let recovered2, match_info = try_against_invisible `RightAgainstLeftInv
        match_info ~invisible
    in

    let n_exact = direct_matches + List.length missing1 +
                  List.length missing2 in
    let n_matches1 = direct_matches + recovered1 in
    let n_matches2 = direct_matches + recovered2 in
    let n_matches = direct_matches + recovered1 + recovered2 in
    dprintf "n_tfs1: %d, n_tfs2: %d" (StringMap.cardinal tfs1) (StringMap.cardinal tfs2);
    dprintf "direct: %d, exact: %d, matches1: %d, matches2: %d, n_matches: %d"
      direct_matches n_exact n_matches1 n_matches2 n_matches;
    let bbp = (bb1, bb2) in
    if (n_exact = n_matches) then begin
      if 0 = n_matches then begin
        (* Declare them as failed if there are no matches; note that
           we special-case the comparison of two empty BBs and return
           Exact 0.0 for those *)
        BBCmp.create bbp Fail match_info
      end else begin
        BBCmp.create bbp (Exact (float n_matches)) match_info
      end
    end else if n_matches1 >= (StringMap.cardinal tfs2) then begin
      (assert(n_matches2 < (StringMap.cardinal tfs1));
       BBCmp.create bbp (Superset (direct_matches, n_exact)) match_info)
    end else if n_matches2 >= (StringMap.cardinal tfs1) then begin
      (assert(n_matches1 < (StringMap.cardinal tfs2));
       BBCmp.create bbp (Subset (direct_matches, n_exact)) match_info)
    end else if n_matches = 0 then begin
      BBCmp.create bbp Fail match_info
    end else begin
      BBCmp.create bbp (Partial (direct_matches, n_exact)) match_info
    end

  let compare_on_tfs ~bb1 ~bb2 =
    assert ((bb1.Bb.id <> Cfg.BB_Error) && (bb2.Bb.id <> Cfg.BB_Error));
    match bb1.Bb.tfs, bb2.Bb.tfs with
    | Some tfs1, Some tfs2
      when ((StringMap.cardinal tfs1 = 0) &&
            (StringMap.cardinal tfs2 = 0)) ->
      BBCmp.create (bb1, bb2) (Exact 0.) empty_match_info
    | Some tfs1, Some tfs2 ->
      begin
        let b = new Perfacc.bench "compare_two_bbs" in
        let desc = Printf.sprintf "%s vs %s"
            (get_bbaddr bb1) (get_bbaddr bb2)
        in
        b#start desc;
        try
          let ret = do_compare_on_tfs ~bb1 ~tfs1 ~bb2 ~tfs2 in
          b#stop ();
          ret
        with exn ->
          b#stop ();
          raise exn
      end
    | _ ->
      (*
       * If we weren't able to compute even one of the TFs for a BB,
       * .tfs won't be available. If that is the case for exactly one
       * of the BBs, we need to fail the comparison.
       *)
      BBCmp.create (bb1, bb2) Fail empty_match_info

  let compare_two_bbs ?(cfg1=None) bb1 ?(cfg2=None) bb2 =
    dprintf "BBcmp: cmping %s (%s) with %s (%s) %s"
      (Cfg.bbid_to_string bb1.Bb.id) (get_bbaddr bb1)
      (Cfg.bbid_to_string bb2.Bb.id) (get_bbaddr bb2) Print.fo;

    let cmpres = match (bb1.Bb.id, bb2.Bb.id) with
      | Cfg.BB_Error, _
      | _, Cfg.BB_Error ->
        BBCmp.create (bb1, bb2) Fail empty_match_info
      | _ -> compare_on_tfs ~bb1 ~bb2
    in

    dprintf "BBcmp: %s" (BBCmp.to_string cmpres);
    dprintf "%s" Print.fc;
    cmpres

  let e2s e =
    let lab = (G.E.label e) in
    let src, dst = (G.E.src e, G.E.dst e) in
    let str = match lab with
      | Some true -> "T"
      | Some false -> "F"
      | None -> "-"
    in
    Printf.sprintf "%s -%s-> %s" (C.v2s src) str (C.v2s dst)

  let edge_pair_to_edgepair (e1, e2) =
    let e2me e = {Subgraph.src = G.V.label (G.E.src e);
                  Subgraph.dst = G.V.label (G.E.dst e);} in
    (e2me e1, e2me e2)

  let verify_asxs subg cmpres =

    let (af1, af2) = Subgraph.afs subg in
    let connecting_edgepairs graph desc edgef =
      let open Ktype in
      let (nbb1, nbb2) = BBCmp.bbp cmpres in
      let nv1 = bb2v af1 nbb1 in
      let nv2 = bb2v af2 nbb2 in
      let neighbors1 = edgef.get_neighbor_edges af1.cfg nv1 in
      let neighbors2 = edgef.get_neighbor_edges af2.cfg nv2 in
      dprintf "#neighbors1: %d, #neighbors2: %d" (List.length neighbors1)
        (List.length neighbors2);
      let verify_assumptions_along_edge our_asxs new_asxs =
        match Assumptions.simplify_asxs our_asxs new_asxs with
        | BatResult.Bad str as bad ->
          dprintf "Mismatch between in_asxs[BB] and out_asxs[PRED]: %s" str;
          bad
        | BatResult.Ok _ as res -> res
      in
      let verify_assumptions_along_edgepair curr_g current_bbcmp new_bbcmp =
        let update_bbcmp g bbcmp nbbcmp =
          let found = ref false in
          let ret = Subgraph.map_bbcmps g (fun x ->
              if BBCmp.equal x bbcmp then begin
                found := true;
                nbbcmp
              end else
                x
            ) in
          assert(!found);
          ret
        in
        let our_md = (BBCmp.match_info current_bbcmp).matched_direct in
        let their_md = (BBCmp.match_info new_bbcmp).matched_direct in
        let our_asxs = edgef.get_our_asxs our_md in
        let their_asxs = edgef.get_their_asxs their_md in
        match verify_assumptions_along_edge our_asxs their_asxs with
        | BatResult.Bad _ as bad -> bad
        | BatResult.Ok (simple_ours, simple_theirs) ->
          let our_nbb = BBCmp.update_match_info current_bbcmp
              {(BBCmp.match_info current_bbcmp) with
               matched_direct = (edgef.set_our_asxs our_md simple_ours)} in
          let their_nbb = BBCmp.update_match_info new_bbcmp
              {(BBCmp.match_info new_bbcmp) with
               matched_direct = (edgef.set_their_asxs their_md simple_theirs)} in
          let ng = update_bbcmp curr_g current_bbcmp our_nbb in
          let ng' = update_bbcmp ng new_bbcmp their_nbb in
          BatResult.Ok ng'
      in
      (* Try to pair edges. In order to be paired, the labels must be the
         same AND the BBs on the other side of each edge must already be
         paired to each other.
      *)
      let match_directed_edges g e1 e2 =
        dprintf "match_%s_edges: %s with %s" desc (e2s e1) (e2s e2);
        assert((edgef.get_this e1) = nv1);
        assert((edgef.get_this e2) = nv2);
        let lab1, lab2 = (G.E.label e1, G.E.label e2) in
        if lab1 <> lab2 then begin
          dprintf "edgepair (%s, %s) mismatch: labels" (e2s e1) (e2s e2);
          None
        end else begin
          let nbr1, nbr2 = (edgef.get_neighbor e1, edgef.get_neighbor e2) in
          match Subgraph.includes_bbl g (v2bb af1 nbr1) with
          | Some bbcmp1 ->
            let a, b = BBCmp.bbp bbcmp1 in
            if (bb2v af2 b) = nbr2 then begin
              (match verify_assumptions_along_edgepair g cmpres bbcmp1 with
               | BatResult.Ok updated_graph ->
                 (* Assumptions were satisfied along this edge, which
                    means that the BBCmp in/out assumptions where updated
                    accordingly. Use the new Subgraph (with the updated
                    BBCmps) here.
                   *)
                 let ep = edge_pair_to_edgepair (e1, e2) in
                 if Subgraph.includes_any_of_edgep updated_graph ep then
                   None
                 else begin
                   let g_with_edge = Subgraph.add_edgepair updated_graph ep in
                   Some (g_with_edge, (e1, e2))
                 end
               | BatResult.Bad _ ->
                 None)
            end else begin
              (match Subgraph.includes_bbr g (v2bb af2 nbr2) with
               | Some bbcmp2 ->
                 let a', b' = BBCmp.bbp bbcmp2 in
                 dprintf "edgepair (%s, %s) mismatch: L %s is matched with \
                          R %s, R %s is matched with L %s"
                   (e2s e1) (e2s e2)
                   (C.v2s nbr1) (C.v2s (bb2v af2 b))
                   (C.v2s nbr2) (C.v2s (bb2v af1 a'));
                 None
               | None ->
                 dprintf "edgepair (%s, %s) mismatch: L %s is matched \
                          (with %s), R %s isn't"
                   (e2s e1) (e2s e2) (C.v2s nbr1) (C.v2s (bb2v af2 b)) (C.v2s nbr2);
                 None)
            end
          | None ->
            (match Subgraph.includes_bbr g (v2bb af2 nbr2) with
             | Some bbcmp2 ->
               let a', b' = BBCmp.bbp bbcmp2 in
               dprintf "edgepair (%s, %s) mismatch: L %s is not matched, \
                        R %s is (with %s)"
                 (e2s e1) (e2s e2) (C.v2s nbr1) (C.v2s nbr2) (C.v2s (bb2v af2 b'));
               None
             | None ->
               dprintf "edgepair (%s, %s): ignoring as neither %s nor %s \
                        have been visited yet"
                 (e2s e1) (e2s e2) (C.v2s nbr1) (C.v2s nbr2);
               None)
        end
      in
      let (nsubg, edges_to_add, _, _) = Misc.lists_do_match graph
          neighbors1 neighbors2 match_directed_edges
      in
      match edges_to_add with
      | [] -> (false, nsubg)
      | _ -> (true, nsubg)
    in
    dprintf "verify_asxs";
    let get_in_asxs matched_expressions = matched_expressions.in_asxs in
    let get_out_asxs matched_expressions = matched_expressions.out_asxs in
    let set_in_asxs matched_expressions n =
      {matched_expressions with in_asxs = n}
    in
    let set_out_asxs matched_expressions n =
      {matched_expressions with out_asxs = n}
    in

    let in_edge = {
      get_neighbor_edges = G.pred_e;
      get_neighbor = G.E.src;
      get_this = G.E.dst;
      get_our_asxs = get_in_asxs;
      get_their_asxs = get_out_asxs;
      set_our_asxs = set_in_asxs;
      set_their_asxs = set_out_asxs;
    } in
    let successor_edges g v =
      (* Omit BBx -> BBx edges from the returned successors. We only
         want to look at them once, so we just return them in the
         predecessors *)
      let succs = G.succ_e g v in
      List.filter (fun e ->
          (G.E.dst e) <> (G.E.src e)) succs
    in
    let out_edge = {
      get_neighbor_edges = successor_edges;
      get_neighbor = G.E.dst;
      get_this = G.E.src;
      get_our_asxs = get_out_asxs;
      get_their_asxs = get_in_asxs;
      set_our_asxs = set_out_asxs;
      set_their_asxs = set_in_asxs;
    } in
    let (added1, subg') = connecting_edgepairs subg "in" in_edge in
    let (added2, subg'') = connecting_edgepairs subg' "out" out_edge in

    match (added1, added2) with
    | (false, false) ->
      (* Signal the caller that this BB shouldn't be added at all,
         as it would be disconnected from our matched subgraph. Notice,
         this means we can't expand to any BBs that are adjacent to this,
         but we haven't visited yet. At least not through this path.
      *)
      (* We explicitly check that the edge we expand across would match,
         so this should never happen *)
      None (* failwith "internal error" (* would be None *) *)
    | _ ->
      Some subg''

  let try_expand_to_bb_pair ~v1 ~v2 get_edge subg nbr1 nbr2 =
    let (af1, af2) = Subgraph.afs subg in
    let do_cmp () =
      let cfg1 = Some af1.Ktype.cfg in
      let cfg2 = Some af2.Ktype.cfg in
      let cmpres = compare_two_bbs ~cfg1 nbr1 ~cfg2 nbr2 in
      (* The vertex must be added before any edges that reference it,
           so create a modified graph here so that we can add any edges
      *)
      (*
       * XXX: we're being too inflexible here; any BB added will keep
       * alternative pairings from being considered; we want to have
       * the ability to backtrack (as we could easily get e.g. a trivial
       * SUBSET match first (say, for a TF a := b, which is included in
       * a BB with N TFs) and then lose the larger match b/c now we've
       * committed to that pairing. Future work.
       *)
      match Subgraph.add subg cmpres with
      | None -> None
      | Some subg' ->
        begin
          match verify_asxs subg' cmpres with
          | Some nsubg ->
            dprintf "Successfully expanding!";
            Some (nsubg, cmpres)
          | None ->
            dprintf "Could not pair any edges!";
            None
        end
    in

    let edge1 = get_edge af1 nbr1 v1 in
    let edge2 = get_edge af2 nbr2 v2 in
    (* The edge label might be None (fallthrough) or true/false
       depending on the condition. For now, expect that we'll only pair
       predecessor BBs if the condition is actually the same, so the
       label has to be the same for them to be equivalent too *)
    dprintf "ne: %s, nbr2: %s" (Cfg.bbid_to_string nbr1.Bb.id)
      (Cfg.bbid_to_string nbr2.Bb.id);
    if ((G.E.label edge1) = (G.E.label edge2)) &&
       (None = (Subgraph.find_bbp_l subg nbr1.Bb.id)) &&
       (None = (Subgraph.find_bbp_r subg nbr2.Bb.id)) then
      do_cmp ()
    else
      None

  let neighbor_set ~af1 ~af2 ~v1 ~v2 getter =
    let open Ktype in
    let get_nbrs af v = List.map (v2bb af) (getter af.cfg v) in
    let nbrs1 = get_nbrs af1 v1 in
    let nbrs2 = get_nbrs af2 v2 in
    (nbrs1, nbrs2)

  let get_in_edge af nbr v =
    let open Ktype in
    (* in edge: neighbor is src, our BB is dst *)
    try
      G.find_edge af.cfg (bb2v af nbr) v
    with Not_found ->
      let str = Printf.sprintf "Could not find in edge: %s -> %s in func %s"
          (Cfg.bbid_to_string nbr.Bb.id) (Cfg.bbid_to_string (C.G.V.label v))
          (Function.to_string af.function_info) in
      failwith str

  let get_out_edge af nbr v =
    let open Ktype in
    (* out edge: our BB is src, the neighbor is dst *)
    try
      G.find_edge af.cfg v (bb2v af nbr)
    with Not_found ->
      let str = Printf.sprintf "Could not find out edge: %s -> %s in func %s"
          (Cfg.bbid_to_string (C.G.V.label v)) (Cfg.bbid_to_string nbr.Bb.id)
          (Function.to_string af.function_info) in
      failwith str

  let bbp2str (bbl, bbr) =
    Printf.sprintf "(%s, %s)" (Cfg.bbid_to_string bbl) (Cfg.bbid_to_string bbr)

  let sump2bbp (suml, sumr) = (suml.Bb.id, sumr.Bb.id)

  let trim_bbcmp_list subg bbcmps =
    let drop this_bb bbp ~selector ~other =
      if this_bb = (selector bbp) then begin
        dprintf "dropping %s from bbp queue (exists in subgraph)"
          (bbp2str bbp)
      end else begin
        dprintf "dropping %s from bbp queue (%s is already paired to 
                 %s in the subgraph)"
          (bbp2str bbp) (Cfg.bbid_to_string this_bb)
          (Cfg.bbid_to_string (other bbp))
      end;
      false
    in
    let still_valid ~bbl ~bbr =
      let left = match Subgraph.find_bbp_l subg bbl with
        | Some bbcmp -> drop bbl (sump2bbp bbcmp) ~selector:fst ~other:snd
        | None -> true
      in
      if left = false then
        false
      else begin
        match Subgraph.find_bbp_r subg bbr with
        | Some bbcmp -> drop bbr (sump2bbp bbcmp) ~selector:snd ~other:fst
        | None -> true
      end
    in
    let ret = List.filter (fun bbcmp ->
        let (bbl, bbr) = sump2bbp (BBCmp.bbp bbcmp) in
        still_valid ~bbl ~bbr) bbcmps
    in
    dprintf "trim_bbcmp_list: %d -> %d" (List.length bbcmps) (List.length ret);
    ret

  let rec verify_bbcmp_list bbcmps =
    match bbcmps with
    | [] -> ()
    | curr_bbcmp :: tail ->
      let curr_bbp = sump2bbp (BBCmp.bbp curr_bbcmp) in
      let curr_bbl, curr_bbr = curr_bbp in
      (*
       * We just need to verify against the tail; we've already been checked against
       * elements preceding us in the list.
       *)
      List.iter (fun bbcmp ->
          let bbp = sump2bbp (BBCmp.bbp bbcmp) in
          let bbl, bbr = bbp in
          if bbl = curr_bbl then begin
            let str = Printf.sprintf "Two BBCmps with the same bbl in the 
                                          queue: %s and %s"
                (bbp2str curr_bbp) (bbp2str bbp) in
            failwith str
          end;
          if bbr = curr_bbr then begin
            let str = Printf.sprintf "Two BBCmps with the same bbr in the 
                                          queue: %s and %s"
                (bbp2str curr_bbp) (bbp2str bbp) in
            failwith str
          end) tail;
      verify_bbcmp_list tail

  let do_expand_along_cfg nesting_level subg seed_bbcmp =
    let open Ktype in

    let (af1, af2) = Subgraph.afs subg in
    let (bb1, bb2) = BBCmp.bbp seed_bbcmp in
    assert(Subgraph.includes_bbp subg (bb1, bb2) <> None);

    let v1 = bb2v af1 bb1 in
    let v2 = bb2v af2 bb2 in
    dprintf "expand_along_cfg: START (seed: (%s, %s), nesting level: %d) %s%d"
      (Cfg.bbid_to_string bb1.Bb.id) (Cfg.bbid_to_string bb2.Bb.id)
      nesting_level Print.fo (nesting_level + 2);

    let preds1, preds2 = neighbor_set ~af1 ~af2 ~v1 ~v2 G.pred in
    let succs1, succs2 = neighbor_set ~af1 ~af2 ~v1 ~v2 G.succ in
    dprintf "(%d, %d), (%d, %d)" (List.length preds1) (List.length preds2)
      (List.length succs1) (List.length succs2);
    let (subg', _, _, _) = Misc.lists_do_match subg preds1 preds2
        (try_expand_to_bb_pair ~v1 ~v2 get_in_edge) in
    let (nsubg, _, _, _) = Misc.lists_do_match subg' succs1 succs2
        (try_expand_to_bb_pair ~v1 ~v2 get_out_edge) in
    dprintf "expand_along_cfg: DONE (%d) %s%d" (Subgraph.size nsubg) Print.fc
      (nesting_level + 2);
    Subgraph.fpit_assumptions nsubg

  let rec expand_along_cfg nesting_level subg bbcmp_queue =
    let open BatPervasives in
    let bbcmp2str = bbp2str -| sump2bbp -| BBCmp.bbp in
    dprintf "expand_along_cfg: %s" (Print.list_to_string bbcmp2str bbcmp_queue);
    verify_bbcmp_list bbcmp_queue;
    match bbcmp_queue with
    | [] ->
      subg
    | seed_bbcmp :: bbcmp_queue ->
      begin
        match do_expand_along_cfg nesting_level subg seed_bbcmp with
        | None ->
          subg
        | Some nsubg ->
          begin
            let new_bbcmps = Subgraph.diff_bbcmps nsubg subg in
            (* NOTE: we have to trim compared to the /old/ subg *)
            let new_bbcmps = trim_bbcmp_list subg new_bbcmps in
            match new_bbcmps with
            | [] ->
              expand_along_cfg (nesting_level + 1) nsubg bbcmp_queue
            | new_bbcmps ->
              dprintf "Got %d new bbcmps during the last expansion round"
                (List.length new_bbcmps);
              expand_along_cfg (nesting_level + 1) nsubg (new_bbcmps @ bbcmp_queue)
          end
      end

  let polyset_elems set = BatList.of_enum (BatSet.enum set)

  let compare_bbs_with_expansion stats afs bb1 bb2 =
    let cmpres = compare_two_bbs bb1 bb2 in
    stats#add_res (BBCmp.res cmpres);
    match BBCmp.res cmpres with
    | Exact pct ->
      (* We used to not want to expand from an Exact 0. match, but
       * this makes little sense now that we're only using BB_Entry vs
       * BB_Entry as comparison seeds.
       *)
      (*if pct < 0.5 then
          (*
           * Exact 0.0 is a match of two empty BBs. Don't
           * start expanding from such a match
           *)
          None
        else*)
      begin
        let b = new Perfacc.bench "seed_expansion" in
        let desc = Printf.sprintf "BBp %s %s"
            (get_bbaddr bb1) (get_bbaddr bb2)
        in
        b#start desc;
        let do_expansion () =
          let subg = Subgraph.create afs [cmpres] in
          let subg = expand_along_cfg 0 subg [cmpres] in
          Some subg
        in
        try
          begin
            let maybe_subg = do_expansion () in
            ignore(match maybe_subg with
                | None ->
                  b#stop ~features:[0.] ()
                | Some subg ->
                  let n = Subgraph.size subg in
                  b#stop ~features:[float_of_int n] ());
            maybe_subg
          end
        with exn ->
          b#stop ();
          raise exn
      end
    | _ ->
      (* Return an empty result to which we can attach some
       * meta-information (FIsomorphic etc) *)
      Some (Subgraph.create afs [])

  let compare_two_clusters ~entries_only ~p1 ~p2 name1 name2 cl1 cl2 =
    (* Has any of bbl, bbr been already matched in the results so far? *)
    let nbbs1 = BatSet.cardinal cl1 in
    let nbbs2 = BatSet.cardinal cl2 in
    let desc = Printf.sprintf "compare_two_clusters: %s vs %s [%d BBs against %d BBs]"
        name1 name2 nbbs1 nbbs2 in
    let bbentry_only = BatList.filter (fun bb -> bb.Bb.id = Cfg.BB_Entry) in
    dprintf "compare_two_clusters: %s" desc;
    (* We used to try to find sub-matches. Now we only care about full functions, so
     *  only use BB_Entry bbs as seeds *)
    let selector set = match entries_only with
      | true -> bbentry_only (polyset_elems set)
      | false -> polyset_elems set
    in
    let bbpairs = BatList.cartesian_product
        (selector cl1) (selector cl2) in
    let stats = new bbcmp_stats desc in
    let matched_subgraphs, _ =
      List.fold_left (fun (subgs, good_enough) (bb1, bb2) ->
          if good_enough then
            (* We already have the best match we can find, stop comparing *)
            (subgs, good_enough)
          else if not (Policy.accept_as_seed ~bb1 ~bb2) then
            (subgs, good_enough)
          else begin
            let afs = afs_of_progs_bbs (p1, p2) (bb1, bb2) in
            match compare_bbs_with_expansion stats afs bb1 bb2 with
            | None -> (subgs, good_enough)
            | Some subg ->
              (* Print out the result early in case we crash. *)
              dprintf "Found a match: %s\n" (Subgraph.to_string subg);
              (subg :: subgs, Subgraph.good_enough subg)
          end
        ) ([], false) bbpairs
    in
    (matched_subgraphs, stats)

  let massage_results ~p1 ~p2 comparison_results =
    let open Ktype in
    let ft = (Format.std_formatter) in
    dprintf "Progs %s,%s" p1.pname p2.pname;
    let comparison_results = List.map (fun (desc, subgs, stats) ->
        let sorted = List.sort (fun subg1 subg2 ->
            let score g =
              let open Cmpres in
              let cmpres = Subgraph.res g in
              let fuzzy = match cmpres.fuzziness with
                | ExactOnly -> 4.
                | SubsetAndExact
                | SupersetAndExact -> 2.
                | Fuzzy (f, _) -> f
              in
              let overlap = match cmpres.overlap with
                | OverlapTotal n
                | OverlapSubset n
                | OverlapSuperset n -> 100. *. (float n)
                | OverlapPartial (n, d) -> (float n) /. (float d)
              in
              fuzzy +. overlap
            in
            int_of_float ((100_000. *. (score subg2)) -. (100_000. *. (score subg1)))) subgs
        in
        (desc, sorted, stats)) comparison_results
    in
    let print_results (desc, subgs, stats) =
      let name = Bb_cluster.cluster_name desc in
      if debug () then
        (Printf.printf "%d graphs of sizes: [" (List.length subgs);
         (List.iter (fun subg ->
              let res = Subgraph.res subg in
              let str = Cmpres.cfgcmp_res_to_string res in
              Printf.printf "%s %!" str) subgs);
         Printf.printf "]\n%!";
         Printf.printf "Three best matches:\n";
         List.iter (fun x ->
             Printf.printf "%s\n" (Subgraph.to_string x)
           ) subgs;
         Printf.printf "\n%!");
      dprintf "Stats for cluster %s" name;
      stats#pp ft
    in
    let drop_stats (desc, subg, _) = (desc, subg) in
    List.iter print_results comparison_results;
    List.map drop_stats comparison_results

  let partition_clusters_by_key ~p1_clusters ~p2_clusters keys =
    let keys = BatList.of_enum keys in
    let keyed_clusters = List.map (fun k ->
        (k, BBMgr.get_cluster p1_clusters k, BBMgr.get_cluster p2_clusters k))
        keys
    in
    List.partition (fun (_, c1, c2) ->
        match (c1,c2) with
        | Some _, Some _ -> true
        | _ -> false)
        keyed_clusters

  let process_clusters ~entries_only ~p1 ~p2 cluster_pairs =
    let module EP = Embarassingly_parallel in
    let open Ktype in
    let do_two_clusters name ~cl1 ~cl2 () =
      dprintf "Comparing %s::%s vs %s::%s" p1.pname name p2.pname name;
      compare_two_clusters ~entries_only ~p1 ~p2 name name cl1 cl2
    in
    let compare_clusters_with_bench (desc, cl1, cl2) =
      let name = Bb_cluster.cluster_name desc in
      let b = new Perfacc.bench "compare_two_clusters" in
      b#start name;
      let subgs, stats = Misc.finally b#stop (do_two_clusters name ~cl1 ~cl2) () in
      {
        EP.ret = (desc, subgs, stats);
        EP.bench = Marshal.to_string b [Marshal.Closures]
      }
    in
    EP.map_list compare_clusters_with_bench cluster_pairs

  let compare () ?(entries_only=true) (p1, p1_clusters) (p2, p2_clusters) =
    let keys1 = BBMgr.keys p1_clusters in
    let matched_clusters, unmatched_clusters =
      partition_clusters_by_key ~p1_clusters ~p2_clusters keys1
    in
    dprintf "Matched clusters: %i Unmatched clusters: %i" (List.length matched_clusters)
        (List.length unmatched_clusters);
    let cluster_pairs = List.map (fun (k,c1,c2) ->
        (k, BatOption.get c1, BatOption.get c2)) matched_clusters
    in
    let cls_bench = new Perfacc.bench "clusters" in
    cls_bench#start "";
    let comparison_results, ewbs = Misc.finally cls_bench#stop
        (process_clusters ~entries_only ~p1 ~p2) cluster_pairs
    in
    (massage_results ~p1 ~p2 comparison_results, ewbs)
end;; (* module GenericComparator *)
(* vim: set ts=8 sw=2 tw=80 et :*)
