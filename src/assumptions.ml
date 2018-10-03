module D = Debug.Make(struct let name = "Assumptions" and default=`NoDebug end)
open D

open Ssa_ext

module AsxTerm =
struct
  type t = Variable.t
  let stringify var = match var with
    | Variable.Var (_, _) ->
      Variable.to_string ~decorators:[] var
    | Variable.VarExp (_, Expression.Load (ary, Value.Int (offset, typ), _, _, _), _) ->
      let ary, ary_id = (match Ssa_ext_convenience.Value.Exceptionless.to_variable ary with
	        | Some v -> (Ssa_ext_convenience.Variable.var v, Ssa_ext_convenience.Variable.id v)
	        | None -> failwith "array is not a variable!")
      in
      let base_reg = Var_convenience.Array.base_reg ary in
      Printf.sprintf "base_%s_off_%Ld_%d" (Var.name base_reg)
	      (Big_int_Z.int64_of_big_int offset)
	      ary_id
    | Variable.VarExp (ary, Expression.Store (_, Value.Int (offset, typ), _, _, _, _), _) ->
      let ary_id = Ssa_ext_convenience.Variable.id var in
      let base_reg = Var_convenience.Array.base_reg ary in
      Printf.sprintf "base_%s_off_%Ld_%d" (Var.name base_reg)
	      (Big_int_Z.int64_of_big_int offset)
	      ary_id
    | Variable.VarExp (_, _, _) ->
      Variable.to_string ~decorators:[NamedNodes] var

  let compare x y =
    let res = String.compare (stringify x) (stringify y) in
(*    dprintf "AsxCompare = %d %s ||vs|| %s\n(%s ||vs|| %s)"
      res
      (Variable.to_string x)
      (Variable.to_string y)
      (stringify x)
      (stringify y);*)
    res

end
module VarSet = BatSet.Make(AsxTerm)
(*
   HACK: This hack fixes issue #18 (https://git.cs.vu.nl/r.vermeulen/kamino/issues/18)

   In the UniqifiedVarSet we swap the compare of VarSet with that of Pervasives.
   During uniqification each variable name is transformed to generate a correct SMT
   formula from the assumption expressions. The VarSet compare function, however,
   expects array names to conform to the specification defined in the
   Var_convenience.Array module. After uniqification this is no longer true resulting
   in invalid array exceptions.
*)
module UniqifiedVarSet = BatSet.Make(struct
                                      type t = Variable.t
                                      let compare = Pervasives.compare
                                    end)

type equiv = (VarSet.t * VarSet.t)
type t = equiv list
type uniq_t = (UniqifiedVarSet.t * UniqifiedVarSet.t) list

type asx = VarSet.t * VarSet.t

type merged = {
  mleft : asx option;
  mright : asx option;
  mcommon : asx;
}

type merge_result =
  | MergeTrivial
  | MergeActual of merged

exception Conflict of string
exception Mismatch of int

let empty = []

let number asxs = List.length asxs

let varname = function
  | Variable.Var (v, _) -> Var.name v
  | _ -> failwith "not a Var"

let varset_to_string = Print.list_to_string ~enclosing:("{", "}") Variable.to_string

let asx_to_string asx =
  let (set1, set2) = asx in
  let str1 = varset_to_string (VarSet.elements set1) in
  let str2 = varset_to_string (VarSet.elements set2) in
  String.concat " <-> " [str1; str2]

let rec normalize assumption_list =
  List.sort compare_two_assumptions assumption_list

and to_string asxs =
  let norm = normalize asxs in
  let lines = List.map asx_to_string norm in
  Print.list_to_string ~enclosing:("[\n", "\n]") ~sep:"\n" (fun x -> x) lines

and sexp_of_asx ?(lr=false) asx =
  let (set1, set2) = asx in
  let open Sexplib in
  let open BatPervasives in
  let regexp = Str.regexp "\\([a-zA-Z0-9_]+\\)_\\([0-9]+\\)" in
  let var_to_sexp pref v =
    let quote str = Printf.sprintf "\"%s\"" str in
    let add_prefix str =
      (*
       * Add a left/right name component so that the test code
       * can normalize IDs properly (see various_test.ml).
       *)
      match lr with
      | false ->
        str
      | true ->
        let repl = Printf.sprintf "\\1%s_\\2" pref in
        Str.global_replace regexp repl str
    in
    try
      v |> Variable.name |> BatString.trim |> quote |> add_prefix |> Sexp.of_string
    with Failure _ ->
      Printf.printf "var is : |%s|" (Variable.to_string v);
      failwith "crapped pants"
  in
  let lhs = Conv.sexp_of_list (var_to_sexp "L") (VarSet.elements set1) in
  let rhs = Conv.sexp_of_list (var_to_sexp "R") (VarSet.elements set2) in
  Sexp.List [lhs; rhs]
and sexp_of_t ?(lr=false) asxs = Sexplib.Conv.sexp_of_list (sexp_of_asx ~lr) (normalize asxs)

and merge_two_equivs asx1 asx2 =
  dprintf "merge_two_equivs: %s with %s" (asx_to_string asx1) (asx_to_string asx2);
  let (f1, s1) = asx1 in
  let (f2, s2) = asx2 in
  let merge_f = VarSet.inter f1 f2 in
  let merge_s = VarSet.inter s1 s2 in
  dprintf "merge_two_equivs: m: %s" (asx_to_string (merge_f, merge_s));
  let cf = VarSet.cardinal merge_f in
  let cs = VarSet.cardinal merge_s in
  if cf <> cs then
    let str = Printf.sprintf "%s <m> %s"
        (asx_to_string asx1)
        (asx_to_string asx2) in
    raise (Conflict str)
  else if 0 = cf then
    MergeTrivial
  else
    let rem1 = (VarSet.diff f1 merge_f, VarSet.diff s1 merge_s) in
    let rem2 = (VarSet.diff f2 merge_f, VarSet.diff s2 merge_s) in
    let common = (merge_f, merge_s) in
    let elide_empty r =
      if VarSet.cardinal (fst r) > 0 then begin
        Some r
      end else begin
        None
      end
    in
    MergeActual {
      mleft = elide_empty rem1;
      mright = elide_empty rem2;
      mcommon = common;
    }

and compare_two_assumptions (a, b) (c, d) =
  let u1 = VarSet.union a b in
  let u2 = VarSet.union c d in
  let ret = VarSet.compare u1 u2 in
(*  dprintf "compare_two_assumptions: %s %s -> %d\n"
    (asx_to_string (a, b)) (asx_to_string (c, d)) ret;*)
  ret

let verify_against_single asxs (a, b) =
  try
    let (left, right) = List.find (fun (vs1, vs2) ->
        VarSet.mem a vs1) asxs in
    if VarSet.mem b right then
      BatResult.Ok ()
    else
      BatResult.Bad (Printf.sprintf "%s is not paired to %s" (varname a) (varname b))
  with Not_found ->
    BatResult.Bad (Printf.sprintf "%s is not included in the assumptions" (varname a))


let compare asxs1' asxs2' =
  let asxs1 = normalize asxs1' in
  let asxs2 = normalize asxs2' in
  try
    dprintf "l: %d, r: %d" (List.length asxs1') (List.length asxs2');
    List.iter2 (fun a b ->
        let cmp = compare_two_assumptions a b in
        if 0 <> cmp then
	        raise (Mismatch cmp)
      ) asxs1 asxs2;
    dprintf "returning 0";
    0
  with
  | Mismatch x -> x
  | Invalid_argument _ ->
    dprintf "List lengths don't match";
    (List.length asxs1) - (List.length asxs2)

(*
let do_merge_equivs_old asxs1 asxs2 =
  let ary_to_str ary =
    let elems = BatDynArray.to_list ary in
    Print.list_to_string ~enclosing:("|", "|") asx_to_string elems
  in
  let drop_dups ary to_be_replaced list =
    let is_member el =
      (*
       * If the element exists in any other position in the array,
       * we don't want to re-add it. However, if it is the element
       * being replaced, don't consider it a duplicate (e.g.
       * {g, x} <-> {h, y} <m> {r} <-> {s} gives
       * the union as the result. So we end up here, trying to
       * replace the array element {g, x} <-> {h, y} with
       * [{g, x} <-> {h, y}; {r} <-> {s}]. If we consider the first
       * element a duplicate, then it's lost.
       *)
      try
	      let _ = List.find (fun x ->
	          if 0 = (compare_two_assumptions x to_be_replaced) then
	            false
	          else
	            0 = (compare_two_assumptions x el)) (BatDynArray.to_list ary)
	      in
	      true
      with Not_found ->
	      false
    in
    List.filter (fun el ->
        not (is_member el)
      ) list
  in
  (*
   * Delete all copies of el in the ary, replace with list
   *)
  let replace_better ary el list =
    dprintf "replace_better: %s el=%s elems=%s" (ary_to_str ary) (asx_to_string el) (to_string list);
    let to_delete = BatDynArray.make 5 in
    (* collect all instances of el *)
    BatDynArray.iteri (fun i x ->
        if 0 = (compare_two_assumptions x el) then
	        BatDynArray.add to_delete i) ary;
    (* when we replace an element, we potentially insert none or
       more than one elements, which invalidates the rest of the
       offsets in to_delete. Keep a counter of size modifications
       in the replacements we've done so far *)
    let plus = ref 0 in (* Note: can be negative *)
    if debug () then
      dprintf "to_delete: %s" (Print.list_to_string (Printf.sprintf "%d") (BatDynArray.to_list to_delete));
    BatDynArray.iter (fun i ->
        dprintf "delete el at %d" (i + !plus);
        BatDynArray.delete ary (i + !plus);
        List.iter (fun el ->
	          dprintf "insert el at %d" (i + !plus);
	          BatDynArray.insert ary (i + !plus) el
          ) (List.rev list);
        plus := !plus + (List.length list) - 1;
      ) to_delete;
    dprintf "replace_better: res = %s" (ary_to_str ary);
    if BatDynArray.empty to_delete then
      None
    else begin
      (* Rewind the index to the earliest deletion; if that index is no longer
       * valid (b/c we just deleted the last element), rewind it to the
       * index of the current last element, so that the algorithm can terminate
       * properly
      *)
      let nidx = min (BatDynArray.get to_delete 0)
	        ((BatDynArray.length ary) - 1) in
      dprintf "IDX RESET: %d" nidx;
      Some nidx
    end
  in
  let idx_err idx ary x f p=
    let str = Printf.sprintf "i out of bounds: %d/%d (%d, func: %s, param: %s)"
        idx (BatDynArray.length ary) x f p in
    failwith str
  in
  let asxs1 = BatDynArray.of_list asxs1 in
  let asxs2 = BatDynArray.of_list asxs2 in
  let i = ref 0 in
  let j = ref 0 in
  while !i < (BatDynArray.length asxs1) do begin
    j := 0;
    while !j < (BatDynArray.length asxs2) do begin
      (* always retrieve asxs1[i] anew, we might modify it *)
      let asx1 =
	      (try
	         BatDynArray.get asxs1 !i
	       with BatDynArray.Invalid_arg (x, f, p) ->
	         idx_err !i asxs1 x f p)
      in
      let asx2 =
	      (try
	         BatDynArray.get asxs2 !j
	       with BatDynArray.Invalid_arg (x, f, p) ->
	         idx_err !j asxs2 x f p)
      in
      dprintf "merge_equivs(%d, %d): %s <m> %s" !i !j (asx_to_string asx1) (asx_to_string asx2);
      dprintf "merge_equivs(%d, %d): %s |-| %s" !i !j (ary_to_str asxs1) (ary_to_str asxs2);
      let m = merge_two_equivs asx1 asx2 in
      let to_be_replaced1 = BatDynArray.get asxs1 !i in
      let to_be_replaced2 = BatDynArray.get asxs2 !j in
      let do_replace ary idx to_be_replaced els =
	      dprintf "do_replace: %s with %s" (asx_to_string to_be_replaced)
	        (ary_to_str (BatDynArray.of_list els));
	      let filtered_els = drop_dups ary to_be_replaced els in
	      if ((List.length filtered_els) = 1) &&
	         ((List.hd filtered_els) = to_be_replaced) then
	        (* This would be a nop but would reset the index,
	           * possibly getting us into an infinite loop.
	           *)
	        ()
	      else
	        match replace_better ary to_be_replaced filtered_els with
	        | Some new_idx -> idx := new_idx
	        | None -> ()
      in
      do_replace asxs1 i to_be_replaced1 m;
      do_replace asxs1 i to_be_replaced2 m;
      do_replace asxs2 j to_be_replaced1 m;
      do_replace asxs2 j to_be_replaced2 m;
      j := !j + 1;
    end done;
    i := !i + 1;
  end done;
  let res1 = BatDynArray.to_list asxs1 in
  let res2 = BatDynArray.to_list asxs2 in
  (* always verify *)
  if true then begin
    dprintf "before normalization: LHS :%s" (to_string res1);
    dprintf "before normalization: RHS :%s" (to_string res2);
    let norm1 = normalize res1 in
    let norm2 = normalize res2 in
    if 0 <> (compare norm1 norm2) then
      let s1 = to_string norm1 in
      let s2 = to_string norm2 in
      Printf.eprintf "--\n%s\ndifferent to\n--\n%s\n" s1 s2;
      failwith "left/right merge results don't match"
  end;
  res1
*)

module VarConstraints = BatMap.Make(AsxTerm)

let vc_to_string (vc : asx list VarConstraints.t) =
  let strs = VarConstraints.fold (fun v asxs acc ->
      (Printf.sprintf "\nvar %s: " (AsxTerm.stringify v) ^
       (to_string asxs)) :: acc) vc [] in
  Print.list_to_string ~enclosing:("VC {", "} VC") (fun x -> x) (List.rev strs)

let vc_add_constraint vc asx =
  let maybe_add_asx_to_var v vc =
    VarConstraints.modify_opt v (fun prev ->
        match prev with
        | None -> Some [asx]
        | Some prev_asxs ->
          begin
            if BatList.mem_cmp compare_two_assumptions asx prev_asxs then begin
              Some (prev_asxs)
            end else begin
              (* XXX: merge *)
              Some (asx :: prev_asxs)
            end
          end
      ) vc
  in
  let (left_vars, _) = asx in
  VarSet.fold maybe_add_asx_to_var left_vars vc

let vc_build_constraints asxs =
  List.fold_left vc_add_constraint VarConstraints.empty asxs

let do_collect_vars sel asxs =
  List.fold_left (fun acc asx ->
      VarSet.union acc (sel asx)
    ) VarSet.empty asxs

let collect_lhs_vars = do_collect_vars fst
let collect_rhs_vars  = do_collect_vars snd

let get_constrained_vars vc =
  let open BatPervasives in
  VarConstraints.keys vc |> VarSet.of_enum

let vc_remove_constraint vc (asx : VarSet.t * VarSet.t) =
  let vars = collect_lhs_vars [asx] in
  VarSet.fold (fun v vc ->
          VarConstraints.modify_opt v (fun value ->
              match value with
              | None ->
                failwith "Internal error: vc_remove_constraint"
              | Some asxs ->
                begin
                  let nval = BatList.remove_if
                      (fun x -> 0 = compare_two_assumptions asx x) asxs
                  in
                  match nval with
                  | [] -> None
                  | _ -> Some nval
                end
            ) vc
        ) vars vc

type merge_state = {
  vc : asx list VarConstraints.t; (* LHS var constraints *)
  pending_rhs_asxs : asx list;
}

type need_restart =
  | AllTrivial of merge_state
  | NeedRestart of merge_state


let merge_state_to_string s =
  Printf.sprintf "{\n\n\tpending: %s\n\tvc: %s\n"
    (to_string  s.pending_rhs_asxs)
    (vc_to_string s.vc)


let rec do_merge_one_asx state left_asx asx =
  match merge_two_equivs left_asx asx with
  | MergeTrivial -> (* Nothing to do; this could happen if left_asx == asx *)
    None
  | MergeActual {mleft; mright; mcommon;} ->
    begin
      let state = {state with vc = vc_remove_constraint state.vc left_asx;} in
      let state = match mleft with
        | None ->
          state
        | Some new_left_asx ->
          {state with pending_rhs_asxs = new_left_asx :: state.pending_rhs_asxs;}
      in
      let state = match mright with
        | None ->
          state
        | Some new_right_asx ->
          {state with pending_rhs_asxs = new_right_asx :: state.pending_rhs_asxs;}
      in
      Some {state with pending_rhs_asxs = mcommon :: state.pending_rhs_asxs;}
        (*       List.fold_left (fun (vars_to_look_at, vc) (asx : asx) -> *)
        (*   let vars = collect_lhs_vars [asx] in *)
        (*   (VarSet.union vars vars_to_look_at, vc_add_constraint vc asx)) *)
        (* (vars_to_look_at, vc) (nasxs : asx list) *)
    end
and merge_while_trivial state asx left_asxs =
  dprintf "merge_while_trivial:\n%s" (merge_state_to_string state);
  match left_asxs with
  | [] ->
    (* Done with the left_asxs for a specific AsxTerm *)
    AllTrivial state
  | left_asx :: rest ->
    begin
      match do_merge_one_asx state left_asx asx with
      | None -> (* trivial, continue *)
        merge_while_trivial state asx rest
      | Some state ->
        dprintf "merge_while_trivial: NeedRestart \n%s" (merge_state_to_string state);
        NeedRestart state
    end
and merge_this_asx_with_asxs_for_var state asx vars_to_look_at =
  dprintf "merge_this_asx_with_asxs_for_var: %s"
    (varset_to_string (VarSet.elements vars_to_look_at));
  if VarSet.is_empty vars_to_look_at then begin
    (* Ok, we successfully merged asx with our left_asxs, now add it to the LHS *)
    dprintf "Exhausted left_asxs, adding asx to the LHS";
    let vc = vc_add_constraint state.vc asx in
    {state with vc}
  end else begin
    let var, vars_to_look_at = VarSet.pop_min vars_to_look_at in
    dprintf "merge_this_asx: looking at var %s" (AsxTerm.stringify var);
    (* Which LHS asxs do we need to merge this asx with? *)
    let asxs =
      try
        VarConstraints.find var state.vc
      with Not_found ->
        failwith "Internal error: no constraints for VarConstraints var"
    in
    match merge_while_trivial state asx asxs with
    | AllTrivial state ->
      merge_this_asx_with_asxs_for_var state asx vars_to_look_at
    | NeedRestart state ->
      dprintf "merge_this_asx_with_asxs_for_var: breaking for restart (%s)"
        (merge_state_to_string state);
      state
  end  
and merge_this_asx state asx =
  dprintf "merge_this_asx:\n%s" (merge_state_to_string state);
  let vars_to_look_at =
    let open BatPervasives in
    let vars1 = VarConstraints.keys state.vc |> VarSet.of_enum in
      let vars2 = collect_lhs_vars [asx] in
    VarSet.inter vars1 vars2
  in
  merge_this_asx_with_asxs_for_var state asx vars_to_look_at
and merge_next_asx state =
  dprintf "merge_next_asx";
  match state.pending_rhs_asxs with
  | [] ->
    state
  | asx :: rest ->
    let state = {state with pending_rhs_asxs = rest;} in
    let state = merge_this_asx state asx in
    merge_next_asx state

let do_merge_equivs asxs1 asxs2 =
  dprintf "do_merge_equivs: %s with %s " (to_string asxs1) (to_string asxs2);
  let var_constraints1 = vc_build_constraints asxs1 in
  let lhs_vars1 = collect_lhs_vars asxs1 in
  if VarConstraints.cardinal var_constraints1 <> VarSet.cardinal lhs_vars1 then begin
    raise (Conflict "Incongruent numbers of vars")
  end;
  let state = {
    vc = var_constraints1;
    pending_rhs_asxs = asxs2;
  } in
  let state = merge_next_asx state in
  let asxs = VarConstraints.fold (fun _ asxs acc -> asxs @ acc) state.vc [] in
  BatList.unique_cmp ~cmp:compare_two_assumptions asxs

let merge_equivs asxs1 asxs2 =
  if 0 = (List.length asxs1) then
    BatResult.Ok asxs2
  else if 0 = (List.length asxs2) then
    BatResult.Ok asxs1
  else begin
    let get_ret () =
      try
        BatResult.Ok (do_merge_equivs asxs1 asxs2)
      with Conflict s -> BatResult.Bad s
    in
    let b = new Perfacc.bench "do_merge_equivs" in
    b#start ((to_string asxs1) ^ (to_string asxs2));
    let stop () =
      let features = [
        float_of_int (number asxs1);
        float_of_int (number asxs2);
      ] in
      b#stop ~features ()
    in
    Misc.finally stop get_ret ()
  end

let simplify_two_asxs asx1 asx2 =
  let drop_empty l = List.filter (fun asx ->
      let (f, s) = asx in
      0 <> VarSet.cardinal f) l
  in
  dprintf "simplify_two_equivs: %s with %s" (asx_to_string asx1) (asx_to_string asx2);
  let (f1, s1) = asx1 in
  let (f2, s2) = asx2 in
  let is_f = VarSet.inter f1 f2 in
  let is_s = VarSet.inter s1 s2 in
  dprintf "merge_two_equivs: intersection: %s" (asx_to_string (is_f, is_s));
  let cf = VarSet.cardinal is_f in
  let cs = VarSet.cardinal is_s in
  if cf <> cs then
    let str = Printf.sprintf "%s <m> %s"
        (asx_to_string asx1)
        (asx_to_string asx2) in
    raise (Conflict str)
  else if 0 = cf then
    (false, [asx1], [asx2])
  else if ((VarSet.cardinal f1) = cf) && ((VarSet.cardinal f2) = cf) then
    (false, [asx1], [asx2])
  else
    let asx1' = (VarSet.diff f1 is_f, VarSet.diff s1 is_s) in
    let asx2' = (VarSet.diff f2 is_f, VarSet.diff s2 is_s) in
    let asxs1'' = drop_empty [asx1'; (is_f, is_s)] in
    let asxs2'' = drop_empty [asx2'; (is_f, is_s)] in
    dprintf "simplify_two_equivs: changed: %s and %s"
      (to_string asxs1'') (to_string asxs2'');
    assert((0 <> compare [asx1] asxs1'') ||
	         (0 <> compare [asx2] asxs2''));
    (true, asxs1'', asxs2'')

let do_simplify_asxs asxs1 asxs2 =
  let ary1 = BatDynArray.of_list asxs1 in
  let ary2 = BatDynArray.of_list asxs2 in
  let modified = ref true in
  while !modified do begin
    modified := false;
    let nassumptions1 = ref empty in
    let nassumptions2 = ref empty in
    dprintf "do_simplify_asxs: loop head %d x %d"
      (BatDynArray.length ary1)
      (BatDynArray.length ary2);
    (for i = 0 to (BatDynArray.length ary1) -1 do begin
        let asx1 = BatDynArray.get ary1 i in
        for j = 0 to (BatDynArray.length ary2) - 1 do begin
	        let asx2 = BatDynArray.get ary2 j in
	        let (changed, m1, m2) = simplify_two_asxs asx1 asx2 in
	        dprintf "simplify_asxs: (%s, %s)"
	          (to_string m1) (to_string m2);
	        match (merge_equivs !nassumptions1 m1, merge_equivs !nassumptions2 m2) with
	        | (BatResult.Ok nasxs1, BatResult.Ok nasxs2) ->
	          dprintf "simplify_asxs: done with merge";
	          nassumptions1 := nasxs1;
	          nassumptions2 := nasxs2;
	          modified := !modified || changed;
	        | (BatResult.Bad str, _)
	        | (_, BatResult.Bad str) ->
	          raise (Conflict str)
        end done;
      end done;

     dprintf "do_simplify_asxs: loop tail";
     BatDynArray.clear ary1;
     BatDynArray.clear ary2;
     List.iter (fun asx ->
         BatDynArray.add ary1 asx) !nassumptions1;
     List.iter (fun asx ->
         BatDynArray.add ary2 asx) !nassumptions2)

  end done;
  (BatDynArray.to_list ary1, BatDynArray.to_list ary2)

let simplify_asxs asxs1 asxs2 =
  dprintf "simplify_asxs";
  let l1 = List.length asxs1 in
  let l2 = List.length asxs2 in
  if (l1 = 0) || (l2 = 0) then
    BatResult.Ok (asxs1, asxs2)
  else begin
    let get_ret () =
      try
        let (m1, m2) = do_simplify_asxs asxs1 asxs2 in
        BatResult.Ok (m1, m2)
      with Conflict str -> BatResult.Bad str
    in
    let b = new Perfacc.bench "do_simplify_asxs" in
    b#start ((to_string asxs1) ^ (to_string asxs2));
    let stop () =
      let features = [
        float_of_int (number asxs1);
        float_of_int (number asxs2);
      ] in
      b#stop ~features ()
    in
    Misc.finally stop get_ret ()
  end

let fold_left f acc asxs =
  List.fold_left (fun acc asx ->
    let elems1, elems2 =
      (VarSet.elements (fst asx),
       VarSet.elements (snd asx))
    in
    f acc (elems1, elems2)
  ) acc asxs

exception Encountered_TMem of Var.t
exception Encountered_phi of Ssa_ext.Variable.t

let unpack_ary var =
  let module C = Ssa_ext_convenience in
  let module VcArray = Var_convenience.Array in
  match var with
  | Variable.Var (_, _) ->
    var
  | Variable.VarExp (_, Expression.Load (ary, _, _, _, _), _)
  | Variable.VarExp (_, Expression.Store (ary, _, _, _, _, _), _) ->
    let ary = match C.Value.Exceptionless.to_variable ary with
      | Some v -> v
      | None -> failwith "array is not a variable!"
    in
    let ary_var = C.Variable.var ary in
    if not (VcArray.is_array ary_var) then begin
      let str = Printf.sprintf "Not an array: %s"
        (Ssa_ext.Variable.to_string ary)
      in
      dprintf "%s" str;
      raise (Encountered_TMem ary_var)
    end;
    ary
  | Variable.VarExp (_, Expression.Phi _, _) ->
    (*
     * XXX: We should be able to handle that by returning a list of
     * variables, but it would complicate the callers too (are the
     * arrays in the phi all heap? All stack? Mixed? Oh shit. It might
     * even need aux assumptions...
     * This is not something that's in the path towards non-trivial
     * results, so cop out for now. If and when we get actual results,
     * we can deal with this case too.
     *)
    raise (Encountered_phi var)
  | Variable.VarExp (_, _, _) ->
    let v = Variable.to_string ~decorators:[NamedNodes] var in
    let str = Printf.sprintf "Can't unpack %s" v in
    failwith str

let set_of_elems elems =
  let enum = BatList.enum elems in
  VarSet.of_enum enum

let of_desc assumption_list =
  List.map (fun (elems1, elems2) ->
      assert((List.length elems1) = (List.length elems2));
      assert(0 < (List.length elems1));
      let set1 = set_of_elems elems1 in
      let set2 = set_of_elems elems2 in
      (set1, set2)) assumption_list

type asxterm_class =
| AsxTermReg
| AsxTermStack
| AsxTermGlobal
| AsxTermHeap of  Interval.Big_int.t

let asxterm_class_to_str = function
  | AsxTermReg ->
    "AsxTermReg"
  | AsxTermStack ->
    "AsxTermStack"
  | AsxTermGlobal ->
    "AsxTermGlobal"
  | AsxTermHeap bounds ->
    Printf.sprintf "AsxTermHeap %s" (Interval.Big_int.to_string bounds)

let stack_vs_heap asxs lhs rhs =
  let module VcArray = Var_convenience.Array in
  let concat_buckets (a, b) =
    match a, b with
    | Some els_a, Some els_b ->
      List.append els_a els_b
    | Some els, None
    | None, Some els ->
      els
    | None, None ->
      []
  in
  let get_nonobservable htbl =
    (Misc.bathashtbl_find_option htbl AsxTermReg,
     Misc.bathashtbl_find_option htbl AsxTermStack)
  in
  let get_global htbl =
    match Misc.bathashtbl_find_option htbl AsxTermGlobal with
    | Some globals -> globals
    | None -> []
  in
  let add_sets lvars rvars asxs =
    let lset = set_of_elems lvars in
    let rset = set_of_elems rvars in
    match (VarSet.cardinal lset) = (VarSet.cardinal rset) with
    | true when (VarSet.cardinal lset) > 0->
      merge_equivs asxs [(lset, rset)]
    | true -> (* empty assumptions *)
      BatResult.Ok asxs
    | false ->
      let str = Printf.sprintf "Cardinality mismatch" in
      BatResult.Bad str
  in
  let do_nonobservable lbuckets rbuckets asxs =
    let l_nonobs = concat_buckets (get_nonobservable lbuckets) in
    let r_nonobs = concat_buckets (get_nonobservable rbuckets) in
    add_sets l_nonobs r_nonobs asxs
  in
  let do_global lbuckets rbuckets asxs =
    let l_global = get_global lbuckets in
    let r_global = get_global rbuckets in
    add_sets l_global r_global asxs
  in
  let do_heap lbuckets rbuckets asxs =
    let get_heap htbl =
      BatHashtbl.fold (fun k v acc ->
        match k with
        | AsxTermReg
        | AsxTermStack
        | AsxTermGlobal -> acc
        | AsxTermHeap bounds -> bounds :: acc) htbl []
    in
    let lookup_bounds htbl bounds =
      try
        BatHashtbl.find htbl (AsxTermHeap bounds)
      with Not_found -> failwith "Internal error getting bounds"
    in
    let to_baseregs arys =
      let module VcArray = Var_convenience.Array in
      List.map (fun ary ->
        let ary = Ssa_ext_convenience.Variable.var ary in
        assert(VcArray.is_array ary);
        Ssa_ext.of_var (VcArray.base_reg ary)) arys
    in
    let do_match () left_bounds right_bounds =
      match left_bounds = right_bounds with
      | true -> Some ((), (left_bounds, right_bounds))
      | false -> None
    in
    let explain ~pairs ~unmatched_l ~unmatched_r =
      let ppair (lb, rb) =
        Printf.sprintf "(%s, %s)" (Interval.Big_int.to_string lb)
          (Interval.Big_int.to_string rb)
      in
      let psingle = Interval.Big_int.to_string in
      let mstr = Print.list_to_string ppair pairs in
      let lstr = Print.list_to_string psingle unmatched_l in
      let rstr = Print.list_to_string psingle unmatched_r in
      let str = Printf.sprintf "Remaining terms when matching \
          heap arrays;\nmatched: %s\nunmatched LHS: %s\nunmatched \
          RHS: %s" mstr lstr rstr
      in
      (*
       * String might get truncated when printed as an exception;
       * dump it to our debug output too.
       *)
      dprintf "%s" str;
      str
    in
    let l_heap = get_heap lbuckets in
    let r_heap = get_heap rbuckets in
    let (), pairs, unmatched_l, unmatched_r =
      Misc.lists_do_match () l_heap r_heap do_match
    in
    if ((List.length unmatched_l) > 0) ||
      ((List.length unmatched_r) > 0) then begin
        let str = explain ~pairs ~unmatched_l ~unmatched_r in
        BatResult.Bad str
      end else begin
    (*
     * Offsets for heap arrays must match. If there's a cardinality
     * mismatch between left/right for a certain class, those
     * assumptions are unsatisfiable. This is checked by add_sets,
     * when we add the arrays.
     *
     * XXX: This handling of the basereg assumptions is *incomplete*.
     * Consider:
     *
     * 1. {ary_esi_f0t3_1, ary_edx_f0t3_1} <-> {ary_edi_f0t3_1', ary_ecx_f0t3_1'}
     * 2. {ary_esi_f4t7_2} <-> {ary_edi_f4t7_2'}
     *
     * Here, for the first assumption, we also add {esi, edx} <-> {edi, ecx}.
     * But, for the second assumption we add {esi} <-> {edi}. This forces
     * {edx} <-> {ecx} in the assumptions BUT this will not resolve 1.
     *
     * To do that we need to either
     * a) Have a separate pass every time we end an assumption, where
     * we try to manually simplify the assumptions arrays based on the
     * register assumptions we have
     * b) Encode auxilially assumptions of the form:
     * {esi, ary_esi_f0t3_1} <-> {edi, ary_edi_f0t3_1'}
     * {esi, ary_esi_f0t3_1} <-> {ecx, ary_ecx_f0t3_1'}
     * {edx, ary_edx_f0t3_1} <-> {edi, ary_edi_f0t3_1'}
     * {edx, ary_edx_f0t3_1} <-> {ecx, ary_ecx_f0t3_1'}
     * This seems more general BUT it needs to be encoded in the
     * assumptions type, which would spill ALL over the file
     * AND it would multiply the number of calls to the assumptions
     * simplification code, which is pretty slow to begin with.
     * Nevermind any debugging, since I don't have a PoC for it yet,
     * except on paper. On the other hand, it's something we need for
     * TF consolidation as well :/
     *)
        let open BatResult.Infix in
        List.fold_left (fun asxs (left_bounds, right_bounds) ->
          let lterms = lookup_bounds lbuckets left_bounds in
          let rterms = lookup_bounds rbuckets right_bounds in
          (* The terms are VarExps, get at the array in the Expression *)
          let lbregs = to_baseregs (List.map unpack_ary lterms) in
          let rbregs = to_baseregs (List.map unpack_ary rterms) in
          asxs >>= (add_sets lterms rterms) >>= (add_sets lbregs rbregs)
        ) (BatResult.Ok asxs) pairs
      end
  in
  let classify var =
    (*
     * Extract the array from the VarExp, if this is a Load or Store.
     * Unfortunately, Validation (at least) depends on us having the
     * VarExp in the assumptions, so we can't just List.map unpack.
     *)
    let var = unpack_ary var in
    let var = Ssa_ext_convenience.Variable.var var in
    if VcArray.is_array var then begin
      let basereg = VcArray.base_reg var in
      if Karch.X86.is_stack_reg basereg then
        AsxTermStack
      else if Var.compare basereg Var_convenience.Array.global_array_base = 0 then
        AsxTermGlobal
      else begin
        let bounds = VcArray.bounds var in
        (*
         * XXX: blue sky
         * NOTE: This will fail to match heap arrays where there's
         * even one access that causes the bounds to differ. This is
         * probably suboptimal, in that, if a function is inlined then
         * the containing function might also be addressing things
         * through a pointer. This should allow for subset/superset
         * relationships, but it's too complicated for now.
         *)
        AsxTermHeap bounds
      end
    end else
      AsxTermReg
  in
  let pbuckets htbl =
    BatHashtbl.iter (fun tclass vars ->
      let class_str = asxterm_class_to_str tclass in
      let v_str = Print.list_to_string Ssa_ext.Variable.to_string vars in
      dprintf "%s: %s" class_str v_str) htbl
  in
  try
    let lbuckets = Misc.npartition classify lhs in
    let rbuckets = Misc.npartition classify rhs in
    dprintf "lbuckets";
    pbuckets lbuckets;
    dprintf "rbuckets";
    pbuckets rbuckets;
    let open BatResult.Infix in
    (do_nonobservable lbuckets rbuckets asxs) >>=
    (do_heap lbuckets rbuckets) >>=
    (do_global lbuckets rbuckets)
  with
  | Encountered_TMem var->
    BatResult.Bad (Pp.var_to_string var)
  | Encountered_phi var ->
    BatResult.Bad (Variable.to_string var)

let add_assumption asxs (lhs, rhs) =
  let set1 = set_of_elems lhs in
  let set2 = set_of_elems rhs in
  dprintf "Classifying terms for assumption %s" (asx_to_string (set1, set2));
  dprintf "((existing assumptions: %s))" (to_string asxs);
  (*
   * Verify that the assumption sets are of the same cardinality.
   * Note that using List.length above is not enough, as two
   * elements could compare the same.
   *)
  assert((VarSet.cardinal set1) = (VarSet.cardinal set2));
  stack_vs_heap asxs lhs rhs

let filter_vis asxs vis_left vis_right (bbid_l, bbid_r) =
  let module SEC = Ssa_ext_convenience in
  List.filter (fun (vs1, vs2) ->
      let lhs = BatList.filter (fun var ->
        let var' = SEC.Variable.var var in
        let visible_or_external =
          ((Visibility.var_visible vis_left var' bbid_l)
           || (Visibility.var_is_external vis_left var')) in
        let useful = (Visibility.var_useful vis_left var' bbid_l) in
        dprintf "%s is visible/external %b and useful %b"
          (Ssa_ext.Variable.to_string var) visible_or_external useful;
        visible_or_external && useful
        ) (BatList.of_enum (VarSet.enum vs1)) in
      let rhs = BatList.filter (fun var ->
        let var' = SEC.Variable.var var in
        let visible_or_external = ((Visibility.var_visible vis_right var' bbid_r)
           || (Visibility.var_is_external vis_right var')) in
        let useful = (Visibility.var_useful vis_right var' bbid_r) in
        dprintf "%s is visible/external %b and useful %b"
          (Ssa_ext.Variable.to_string var) visible_or_external useful;
        visible_or_external && useful
        ) (BatList.of_enum (VarSet.enum vs2)) in
      (*
        If both the LHS and RHS contains a visible and useful term, we keep it
        for propagation. This serves the following two purposes:
        1. Validation expects fragment inputs to be available as assumption terms
           on the edge of the fragment. This is not the case if the fragment input
           usage is control-flow dependend. Consider the following example:

                                   +---------+
                                   |  BB 1   |
                                   +---------+
                             -------/       \-------
                    +-------/-+                   +-\-------+
                    |  BB 2   |                   |  BB 3   |
                    +---------+                   +---------+
                             \-------       -------/
                                   +-\-----/-+
                                   |  BB 4   |
                                   +---------+

           If BB 1 contains R_EDI as an input, but assigns a new value to R_EDI
           in BB 2, then BB 4 contains the phi with both R_EDIs as parameters.
           In the case of an open matched assumption, {...} <-> {R_EDI, R_EDI'}
           with R_EDI' being the definition in BB 2, we used to *not* propagate
           this IN assumption to BB 1 because R_EDI' is neither visible nor
           usable in BB 1. Note however, that R_EDI is both visible and usable.
           Not having an fragment input in the IN assumptions of a fragment
           causes validation to see an unexpected input and therefore fails the
           validation. By propagating IN assumptions if both the LHS and RHS
           contain terms that are both visible and usable this is no longer an
           issue.
        2. The goal of propagating assumptions is to catch discrepancy as fast
           as possible. Having fragments inputs in the fragments IN assumptions
           adds to this goal, because it still contains terms (namely the fragment's
           inputs) that can signal an inconsistent assumption.
           Consider the previous CFG. If we matched a similar fragment and have
           the IN assumption {R_EDI, ...} <-> {R_ESI, ...} at BB 4 with both
           R_EDI & R_ESI being inputs to the /current/ fragment and '...' being
           control-flow dependend definitions in either BB 2 or BB 3, then we can
           detect an inconsistency if a predecessor of BB 1 has the OUT assumption
           {R_EDI} <-> {X} with X != R_ESI or {Y} <-> {R_ESI} with Y != R_EDI.
      *)

      if (List.length lhs) > 0 && (List.length rhs) > 0
        then true
        else false) asxs

let to_formula assumptions =
  let open_to_possible_closed (lhs, rhs) =
    let rec fac ?(acc=1) n =
      if n = 0 then acc
      else fac ~acc:(n * acc) (n - 1)
    in
    assert((UniqifiedVarSet.cardinal lhs) = (UniqifiedVarSet.cardinal rhs));
    if (UniqifiedVarSet.cardinal lhs) = 1 then [[(UniqifiedVarSet.choose lhs, UniqifiedVarSet.choose rhs)]]
    else List.fold_left (fun acc l ->
        (List.fold_left2 (fun acc e e' ->
             acc @ [(e, e')]
           ) [] (UniqifiedVarSet.elements lhs) l) :: acc
      ) [] (Misc.permutations (UniqifiedVarSet.elements rhs))
  in
  let assumption_to_formula asx =
    let module C = Ssa_ext_convenience in
    List.fold_left (fun form asx ->
        Ast.exp_or form (List.fold_left (fun form' (lhs, rhs) ->
            match C.Variable.is_expression lhs, C.Variable.is_expression rhs with
            | false, false ->
                Ast.exp_and form' (Ast.exp_eq (Ast.Var (C.Variable.var lhs))
                                     (Ast.Var (C.Variable.var rhs)))
            | false, true ->
              begin
                match C.Variable.to_expression rhs with
                | Ssa_ext.Expression.Load _ as exp ->
                  Ast.exp_and form' (Ast.exp_eq (Ast.Var (C.Variable.var lhs))
                                       (Memory2array.coerce_exp (C.Expression.to_ast exp)))
                | _ -> failwith "Unexpected expression in an assumption"
              end
            | true, false ->
              begin
                match C.Variable.to_expression lhs with
                | Ssa_ext.Expression.Load _ as exp ->
                  Ast.exp_and form' (Ast.exp_eq (Memory2array.coerce_exp (C.Expression.to_ast exp))
                                    (Ast.Var (C.Variable.var rhs)))
                | _ -> failwith "Unexpected expression in an assumption"
              end
            | true, true ->
              begin
                match C.Variable.to_expression lhs, C.Variable.to_expression rhs with
                | Ssa_ext.Expression.Load _ , Ssa_ext.Expression.Load _ as exp ->
                  Ast.exp_and form' (Ast.exp_eq (Memory2array.coerce_exp (C.Expression.to_ast (fst exp)))
                                       (Memory2array.coerce_exp (C.Expression.to_ast (snd exp))))
                | _ -> failwith "Unexpected expression in an assumption"
              end
          ) Ast.exp_true asx)
      ) Ast.exp_false (open_to_possible_closed asx)
  in
  List.fold_left (fun acc assumption ->
      Ast.exp_and assumption acc
    ) Ast.exp_true (List.map assumption_to_formula assumptions)

let relevant_vars asxs =
  List.fold_left (fun (lhs, rhs) (lhs', rhs') ->
      let to_vs vs = VarSet.fold (fun v acc ->
          Var.VarSet.add (Ssa_ext_convenience.Variable.var v) acc) vs Var.VarSet.empty
      in
      let lhs'' = to_vs lhs' in
      let rhs'' = to_vs rhs' in
      (Var.VarSet.union lhs lhs'', Var.VarSet.union rhs rhs'')) (Var.VarSet.empty, Var.VarSet.empty) asxs

let uniqify_asxs asxs =
  let module C = Ssa_ext_convenience in
  let l_mapping = BatHashtbl.create (2 * (List.length asxs)) in
  let r_mapping = BatHashtbl.create (2 * (List.length asxs)) in
  (* XXX This not the right place to normalize, but the most convenient ATM.
     This normalization is STP specific, since free variables cannot contain the
     charachter '-'.
     This should actually be solved by the solver in the BAP framework.
  *)
  let normalize_name name =
    Str.global_replace (Str.regexp "[-:]") "_" name
  in
  let rec uniqify_var mapping suffix = function
    | Ssa_ext.Variable.Var _ as v ->
      let v' = C.Variable.create ~attrs:(C.Variable.attrs v)
        ((normalize_name (C.Variable.name v)) ^ suffix) (C.Variable.typ v) in
        BatHashtbl.add mapping v v';
        v'
    | Ssa_ext.Variable.VarExp _ as v ->
      C.Variable.with_expression (uniqify_var mapping suffix
                                    (C.Variable.without_expression v))
        (uniqify_exp mapping suffix (C.Variable.to_expression v))
  and uniqify_val mapping suffix = function
    | Ssa_ext.Value.Var v -> Ssa_ext.Value.Var (uniqify_var mapping suffix v)
    | Ssa_ext.Value.Int _ as i -> i
    | Ssa_ext.Value.Lab _ as l -> l
  and uniqify_exp mapping suffix = function
    | Ssa_ext.Expression.Load (mem, idx, edn, t, attrs) ->
      Ssa_ext.Expression.Load ((uniqify_val mapping suffix mem),
                               (uniqify_val mapping suffix idx),
                               edn, t, attrs)
    | _ -> failwith "Cannot uniqify expression that is not a load!"
  in
  (List.fold_left (fun acc (lhs, rhs) ->
      let aux mapping suffix terms =
        (* At this point we switch to a different type since the VarSet
           element type compare cannot properly handle the uniqified
           variable names. In particular the array names.
         *)
        let terms' = UniqifiedVarSet.of_enum (VarSet.enum terms) in
        UniqifiedVarSet.map (fun term ->
            uniqify_var mapping suffix term
          ) terms' in
      let lhs' = aux l_mapping "_L" lhs in
      let rhs' = aux r_mapping "_R" rhs in
      (lhs', rhs') :: acc
   ) [] asxs, l_mapping, r_mapping)
