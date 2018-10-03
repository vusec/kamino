module D = Debug.Make(struct let name = "Visibility" and default=`Debug end)
open D

module BBidSet = BatSet.Make(Cfg.BBid)

type t = {
  cfg: Cfg.SSA.G.t;
  (*
   * Hashtable which, for every variable definition, holds the set
   * of BBs in which that definition is visible.
   *)
  visibility : (Var.t, BBidSet.t) BatHashtbl.t;
  uses : (Var.t, BBidSet.t) BatHashtbl.t;
  (*
   * Hashtable which, for every variable definition, holds the set
   * of BBs in which that definition is useful; i.e. a definition is
   * "useful" in BB X iff it is used in X or in a BB that is reachable
   * from X.
   *)
  usefulness : (Var.t, BBidSet.t) BatHashtbl.t;

  def_in_bb : (Var.t, Cfg.bbid) BatHashtbl.t;
}

let bbset_to_str bbset =
  let ids = BBidSet.elements bbset in
  Print.list_to_string ~enclosing:("{", "}") ~sep:(", ") Cfg.bbid_to_string ids

let htab_to_string htab =
  let lines = BatHashtbl.fold (fun var bbset acc ->
    let str = Printf.sprintf "%s: %s" (Pp.var_to_string var)
      (bbset_to_str bbset) in
    str::acc
  ) htab [] in
  Print.list_to_string ~enclosing:("", "") ~sep:("\n") (fun x -> x)
    (List.rev lines)

let to_string vis =
  Printf.sprintf "visibility:\n%s\nusefulness:\n%s\n"
    (htab_to_string vis.visibility)
    (htab_to_string vis.usefulness)

let dump_htab path tab =
    Outdir.with_file_out path (fun oc ->
        output_string oc (htab_to_string tab);
        output_string oc "\n";
        flush oc
      )

let dump_uses_info path ~uses =
  match path with
  | None -> ()
  | Some path ->
    let p = Printf.sprintf "%s/%s" path "uses" in
    dump_htab p uses

let dump_vis_info path ~visibility ~usefulness =
  match path with
  | None -> ()
  | Some path ->
    let pairs = [
      (visibility, "vis");
      (usefulness, "usefulness");
    ] in
    List.iter (fun (tab, name) ->
        let p = Printf.sprintf "%s/%s" path name in
        dump_htab p tab) pairs


let find_last_eax_def cfg =
  let last_eax_def_in_stmts stmts =
    let rstmts = List.rev stmts in
    BatList.Exceptionless.find_map (fun stmt ->
      match stmt with
      | Ssa.Move (var, _, _) -> Some var
      | _ -> None) rstmts
  in
  Cfg_convenience.SSA.walk_bb_successors_inclusive (fun v def ->
    let stmts = Cfg.SSA.get_stmts cfg v in
    match last_eax_def_in_stmts stmts with
    | None -> def
    | Some ndef -> Some ndef) cfg None

module Loopiness =
struct
  type t = (Cfg.bbid, bool) BatHashtbl.t
  let create g = (g, BatHashtbl.create 10)
  (* Determine if a BB is reachable by itself and memoize the result *)
  let part_of_loop (g, htbl) bbid =
    let calc () =
      let this_vertex = Cfg.SSA.find_vertex g bbid in
      Cfg_convenience.SSA.walk_from_bb (fun v acc ->
	let found = (v = this_vertex) in
	acc || found
      ) g false bbid Cfg.SSA.G.succ
    in
    try
      BatHashtbl.find htbl bbid
    with Not_found ->
      let is_part = calc () in
      BatHashtbl.add htbl bbid is_part;
      is_part
end

let initialize ?(keypref=None) cfg =
  dprintf "Calculating visibility information";
  let keypref = BatOption.map (fun p -> p ^ "/visibility") keypref in
  let module C = Cfg.SSA in
  let module G = C.G in
  let module BBidMap = Bb.BBidMap in
  let module Reach = Reachable.SSA in

  let v2bbid = Cfg.SSA.G.V.label in

  (* Given a variable, return the BB of its definition *)
  let bb_for_definition = BatHashtbl.create (G.nb_vertex cfg) in

  (* Given a variable, return the set of BBs its definition is visible in *)
  let visible_bbs_for_definition = BatHashtbl.create (G.nb_vertex cfg) in

  (* See module definition *)
  let loopy = Loopiness.create cfg in

  let get_reachable_set v =
    let reachable_vs = Reach.reachable cfg v in
    (* The result of Reach.reachable always includes v itself! *)
    let reachable_vs =
      match Loopiness.part_of_loop loopy (v2bbid v) with
      | true -> reachable_vs
      | false -> List.filter (fun x -> x <> v) reachable_vs
    in
    let reachable_bbids = List.map v2bbid reachable_vs in
    BBidSet.of_enum (BatList.enum reachable_bbids)
  in
  let populate_definition_tables v =
    let reachable = get_reachable_set v in
    let visitor = object(self)
      inherit Ssa_visitor.nop
      method visit_avar avar =
	BatHashtbl.add bb_for_definition avar (v2bbid v);
	BatHashtbl.add visible_bbs_for_definition avar reachable;
	Type.SkipChildren
    end in
    let stmts = C.get_stmts cfg v in
    ignore(Ssa_visitor.stmts_accept visitor stmts)
  in
  (*
   * This simply populates the uses table exactly as expected.
   * Later on, uses gets reused to store the usefulness information.
   *)
  let populate_uses v uses =
    let bb_rvars =
      let stmts = C.get_stmts cfg v in
      let rvars = ref [] in
      let visitor = object(self)
	inherit Ssa_visitor.nop
	method visit_rvar var =
	  rvars := var :: !rvars;
	  Type.DoChildren
      end
      in
      ignore(Ssa_visitor.stmts_accept visitor stmts);
      !rvars
    in
    let exit_bbs = Cfg_convenience.SSA.get_exit_bbs cfg in
    let exit_bbids = BatList.filter_map (fun v' ->
      let bbid = (v2bbid v') in
      if bbid <> Cfg.BB_Error then
        Some bbid
      else
        None) exit_bbs
    in
    let bb_rvars = match List.mem (v2bbid v) exit_bbids with
      | false -> bb_rvars
      | true ->
	(* Force EAX to be used at BB_Exit *)
        match find_last_eax_def cfg with
        | None ->
          bb_rvars
        | Some eax_def ->
          (try
            ignore (List.find (fun v ->
              Var.equal v eax_def) bb_rvars);
            bb_rvars
          with Not_found ->
            eax_def :: bb_rvars)
    in
    List.iter (fun var ->
      let bbset = BatHashtbl.find_default uses var BBidSet.empty in
      let nbbset = BBidSet.add (v2bbid v) bbset in
      BatHashtbl.replace uses var nbbset
    ) bb_rvars;
    uses
  in
  let determine_usefulness v uses =
    let reachable_set = get_reachable_set v in
    let update_usefulness var =
      (* Which BBs is this vardef used in? *)
      match Misc.bathashtbl_find_option uses var with
      | Some bbset ->
	(* Is there an intersection between the BBs this var is used in
	   and the BBs that are reachable from us?
	*)
	let overlap = BBidSet.inter reachable_set bbset in
	let bb_of_def = match BatHashtbl.Exceptionless.find bb_for_definition var with
	  | Some bbid -> BBidSet.singleton bbid
	  | None -> BBidSet.empty
	in
	(* Do not include the definition BB in the overlap set *)
	let overlap = BBidSet.diff overlap bb_of_def in
	if not (BBidSet.is_empty overlap) then
	  let nbbset = BBidSet.add (v2bbid v) bbset in
	  BatHashtbl.replace uses var nbbset
      | None ->
	failwith "Can't get here?"
    in
    (* For each BB and everyp var referenced in that BB ... *)
    let vars = BatList.of_enum (BatHashtbl.keys uses) in
    List.iter (fun var ->
      try
	(*
	 * ... get the BBs that the variable is visible in
	 * (that we've determined so far) ...
	 *)
	let vis_set = BatHashtbl.find visible_bbs_for_definition var in
	if BBidSet.mem (v2bbid v) vis_set then
	  update_usefulness var
      (* Do not update_usefulness if the current BB is already in vis_set *)
      with Not_found ->
	(* Not a defined var *)
	update_usefulness var
    ) vars;
    uses
  in
  Cfg.SSA.G.iter_vertex populate_definition_tables cfg;
  let uses = Cfg.SSA.G.fold_vertex populate_uses cfg
    (BatHashtbl.create (G.nb_vertex cfg)) in

  dump_uses_info keypref ~uses;

  let usefulness = Cfg.SSA.G.fold_vertex determine_usefulness cfg
    (BatHashtbl.copy uses) in
  let visibility = visible_bbs_for_definition in

  let ret = {cfg = cfg; visibility; uses; usefulness; def_in_bb = bb_for_definition} in
  dump_vis_info keypref ~visibility ~usefulness:uses;
  ret

let var_visible vis var bbid =
  try
    let set = BatHashtbl.find vis.visibility var in
    BBidSet.mem bbid set
  with Not_found -> false

let var_is_external vis var =
  not (BatHashtbl.mem vis.def_in_bb var)

(* Is this var live at the end of its defining BB? *)
let var_is_live_in_defining_bb vis var bbid =
  begin
    match Var.typ var with
    | Type.Reg _ ->
      begin
        match Misc.bathashtbl_find_option vis.def_in_bb var with
        | None ->
          let str = Printf.sprintf "var_is_live_in_defining_bb: no def for %s in %s"
              (Pp.var_to_string var) (Cfg.bbid_to_string bbid) in
          failwith str
        | Some bbid' when bbid' <> bbid ->
          let str = Printf.sprintf
              "var_is_live_in_defining_bb: given %s but %s was defined in %s"
              (Cfg.bbid_to_string bbid) (Cfg.bbid_to_string bbid')
              (Pp.var_to_string var) in
          failwith str
        | _ -> ()
      end
    | _ -> ()
  end;
  let visitor = object
    inherit Ssa_visitor.nop
    val mutable live = None
    method get_live () = live
    method visit_stmt stmt =
      begin
        match live with
        | None ->
          (* We only need to see the last def to decide *)
          begin
            match stmt with
            | Ssa.Move (avar, _, _) ->
              dprintf "About to compare %s to %s"
                (Pp.var_to_string avar)
                (Pp.var_to_string var);
              live <- Some (Var.equal avar var);
            | _ -> ()
          end
        | _ -> ()
      end;
      Type.SkipChildren
  end
  in
  let bbv = Cfg.SSA.find_vertex vis.cfg bbid in
  let stmts = Cfg.SSA.get_stmts vis.cfg bbv in
  ignore(Ssa_visitor.stmts_accept visitor (List.rev stmts));
  match visitor#get_live () with
  | None -> failwith "var_is_live_in_defining_bb: No def in stmts!"
  | Some res -> res

(*
 * Is the variable definition useful in BBx (identified by bbid)? It is
 * iff the variable is used in BBx or any of the BBs reachable from BBx.
*)
let var_useful vis var bbid =
  try
    let set = BatHashtbl.find vis.usefulness var in
    BBidSet.mem bbid set
  with Not_found -> false

(* Determine if a variable is used before its definition in a BB.
   That necessarily means the BB is part of a loop. *)
let exists_use_before_def var stmts =
  let visitor = object(self)
    inherit Ssa_visitor.nop
    val def_seen = ref false
    val use_before_def = ref false
    method saw_definition = !def_seen
    method exists_use_before_def = !use_before_def
    method visit_avar avar =
      if Var.equal avar var then begin
        def_seen := true
      end;
      Type.DoChildren
    method visit_rvar rvar =
      if (Var.equal rvar var) && ((!def_seen) = false) then begin
        use_before_def := true
      end;
      Type.DoChildren
  end in
  Ssa_visitor.stmts_accept visitor stmts;
  assert(visitor#saw_definition);
  visitor#exists_use_before_def

(*
 * Is this definition used in any of the BBs
 * that are reachable from it? If not, it is either dead or
 * used as a temporary in the BB, so should not be part of
 * its outputs.
 *)
let var_def_used vis var (bbid : Cfg.bbid) =
  let bbv = Cfg.SSA.find_vertex vis.cfg bbid in

  (* verify that bbid points to the BB that contains the definition of var.
     Simultaneously see if it's being referenced through a path that includes
     a back edge (i.e. see if there's a use of the variable in its BB that
     counts as a use for visibility purposes, b/c it leaves the BB (i.e. the
     computation is used in a later iteration through this same BB).
  *)
  let stmts = Cfg.SSA.get_stmts vis.cfg bbv in
  let used_before_def_in_definition_bb = exists_use_before_def var stmts in
  let last_stmt = BatList.Exceptionless.last stmts in

  (* XXX: could be checking for a width of 1 bit first but I'm not 100% sure
   * that's always the case so playing it safe.
   *)
  let used_in_cjmp = match last_stmt with
    | Some (Ssa.CJmp (cond, _, _, _)) ->
      begin
        match cond with
        | Ssa.Int _
        | Ssa.Lab _ ->
          false
        | Ssa.Var cvar -> cvar = var
      end
    | _ -> false
  in
  (* If this variable is the condition of a cjmp ending this BB, then it's used *)
  if used_in_cjmp then
    true
  else if (Var.name var = "R_EAX") &&
     ((Cfg.SSA.G.out_degree vis.cfg bbv) = 0) then begin
    (*
     * We go to some length to mark the last definition of EAX as used on
     * any exit BBs. Here, we make sure that a definition of EAX _in_ an
     * exit BB is also going to be considered output. There can be more than
     * one exit BBs, so use out_degree to decide.
     *)
    (*
     * XXX: we should only return true for the last eax definition
     * in an exit BB, otherwise we end up with multiple OUT asxs
     * involving different SSA values of EAX.
     *)
    true
  end else begin
    try
      let set = BatHashtbl.find vis.usefulness var in
      let set = match used_before_def_in_definition_bb with
        | true -> set
        | false -> BBidSet.remove bbid set
      in
      not (BBidSet.is_empty set)
    with Not_found -> false
  end

let var_is_used_exn vis var bbid =
  let uses = BatHashtbl.find vis.uses var in
  BBidSet.mem bbid uses
