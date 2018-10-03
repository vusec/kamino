module D = Debug.Make(struct let name = "Transfer_function" and default=`Debug end)
open D

module V = Ssa_ext_visitor
module C = Ssa_ext_convenience
module VS = Ssa_ext.VariableSet
module VH = Ssa_ext.VariableHash
module VC = Var_convenience

open BatPervasives

type t = {
  inputs: Ssa_ext.VariableSet.t;
  f: Ssa_ext.Expression.t;
  output: Ssa_ext.Variable.t
}

exception Incomputable of string
exception Irreducible of string

let base_reg_for_ary ary =
  let trim_id varname =
    let re = Str.regexp "\\(.*\\)_[0-9]+" in
    Str.replace_first re "\\1" varname
  in
  let open Ssa_ext in
  match ary with
  | Variable.Var (var, _)
  | Variable.VarExp(var, Expression.Store _, _) ->
    VC.Array.base_reg var
  | Variable.VarExp(_, Expression.Phi(vs), _) ->
    assert((List.length vs) > 1);
    let tmplv = List.hd vs in
    let tmpl = trim_id (Variable.name tmplv) in
    (try
      let mismatch = BatList.find_map (fun var ->
        let name = trim_id (Variable.name var) in
        if 0 <> (String.compare tmpl name) then
	  Some name
        else
	  None) (List.tl vs)
      in
      dprintf "%s != %s" tmpl mismatch;
      failwith "array phi mismatch"
    with Not_found ->
      VC.Array.base_reg (C.Variable.var tmplv))
  | Variable.VarExp (_, e, _) ->
    dprintf "Error expr: %s" (Expression.to_string e);
    failwith "can we get here?"

module Predicates =
struct
  let may_alias_with_store outputs mem =
    dprintf "may_alias_with_store: %s" (Ssa_ext.Value.to_string ~decorators:[Ssa_ext.NamedNodes] mem);
    let expr_contains_a_store_to_mem expr found =
      if found then true
      else
        begin
          match expr with
          | Ssa_ext.Expression.Store (mem, _, _, _, _,_) ->
            not (C.Variable.is_array (C.Value.to_variable mem))
          | _ -> false
        end
    in
    let expr_contains_a_store expr found =
      if found then true
      else
        begin
          match expr with
          | Ssa_ext.Expression.Store _ -> true
          | _ -> false
        end
    in
    let contains_a_store ary =
      match C.Variable.Exceptionless.to_expression ary with
      | Some expr ->
        let ret = C.Expression.fold expr_contains_a_store expr false in
        dprintf "contains_a_store: %b" ret;
        ret
      | None ->
        dprintf "contains_a_store: false";
        false
    in
    let store_to_mem_in_outputs =
      VS.fold (fun out acc ->
          if acc then acc
          else
            begin
              dprintf "store_to_mem_in_outputs: looking at %s"
                (Ssa_ext.Variable.to_string out);
              let expr = C.Variable.to_expression out in
              C.Expression.fold expr_contains_a_store_to_mem expr false
            end
        ) outputs false
    in
    let stores_to_array_in_outputs =
      VS.fold (fun out acc->
          let rec collect_bases expr acc =
            match expr with
            | Ssa_ext.Expression.Store (mem, _, _, _, _, _) ->
              let mem' = C.Value.to_variable mem in
              if C.Variable.is_array mem'
              then
                begin
                  let base_reg = base_reg_for_ary mem' in
                  if C.Variable.is_expression mem'
                  then
                    collect_bases (C.Variable.to_expression mem') (VC.VS.add base_reg acc)
                  else
                    VC.VS.add base_reg acc
                end
              else acc
            | _ -> acc
          in
          let expr = C.Variable.to_expression out in
          C.Expression.fold collect_bases expr acc
        ) outputs VC.VS.empty
    in
    let mem' = C.Value.to_variable mem in
    match C.Variable.typ mem' with
    (* In case of memory, all the previous memory operations are sub-expression.
       Therefore we can look for a store in the sub-expression to determine a
       may-alias.
       If none is found, we have to look for an array store in the currently computed
       output variables.
    *)
    | Type.TMem _ ->
      dprintf "may_alias_with_store: TMem";
      contains_a_store mem' || (VC.VS.is_empty stores_to_array_in_outputs) = false
    | Type.Array _ ->
(*
      (* At this point we assume that stores/loads are collapsed if possible.
         This means that if we encounter a store as a sub-expression,
         it must overlap with the load.
         However, unlike the memory case, arrays do not contain *all* memory operations
         as sub-expressions.
         Therefore we must look at the current computed outputs and look for a store to
         an array with a different base register to determine a may-alias.
      *)
      let base_reg = base_reg_for_ary mem' in
      dprintf "store_to_mem_in_outputs: %b" store_to_mem_in_outputs;
      contains_a_store mem'
      || (VC.VS.exists (fun reg -> reg != base_reg ) stores_to_array_in_outputs)
      || store_to_mem_in_outputs
*)
      dprintf "may_alias_with_store: Array";
      store_to_mem_in_outputs
    | Type.Reg _ -> failwith "This shouldn't happen!"
end

let compute_for_bb stmts =
  let visitor = object(self)
    inherit V.rnop

    val mutable outputs = VS.empty
    val defs = VH.create 8

    method get_outputs () = outputs
    method get_defs () = defs

    method visit_stmt = function
      | Ssa_ext.Statement.Move (var, exp, attrs) as s->
	      dprintf "Visiting stmt %s" (Ssa_ext.Statement.to_string s);
        let output = C.Variable.with_expression var exp in
	      dprintf "Registering def for %s" (Ssa_ext.Variable.to_string
					                                  ~decorators:[Ssa_ext.NamedNodes] output);
        outputs <- VS.add output outputs;
        VH.add defs var exp;
        V.DoParent
      | _ -> V.DoParent

    method visit_exp exp =
      dprintf "Visiting exp %s" (Ssa_ext.Expression.to_string exp);
      match exp with
      | Ssa_ext.Expression.Load (value, _, _, typ, _)
      | Ssa_ext.Expression.Store (value, _, _, _, typ, _) ->
(*        if Predicates.may_alias_with_store outputs value
        then raise (Incomputable "Irreducible store and load sequence")
        else*) V.DoParent
      | _ -> V.DoParent

    method visit_rvar rvar =
      (* Forward substitute definitions *)
      (* This was previously implemented using BatHashtbl.find_option and pattern matching.
         However, the freaking implentation of find_option in batteries part of BAP 0.6 is broken
         (i.e., mem returns true while find_option return None :S *)
      if VH.mem defs rvar
      then
        begin
          let def = VH.find defs rvar in
          dprintf "Forward substituting %s with %s" (Ssa_ext.Variable.to_string rvar)
            (Ssa_ext.Expression.to_string def);
          V.ChangeTo
            (C.Variable.with_expression rvar def)
        end
      else
        V.DoParent
  end
  in
  let () = ignore(V.stmts_accept visitor stmts) in
  let outputs = visitor#get_outputs () in
  let inputs_for_output output =
    let (||) = VS.union in
    let vl2vs l = VS.of_enum (BatList.enum l) in
    let rec aux acc var =
      if C.Variable.is_expression var
      then
        let exp = C.Variable.to_expression var in
        (* Note that phis can contain inputs, so also capture the expression variables*)
        let vals,_,_,_,_,_,phi_vars,_,_ = Ssa_ext.Expression.getargs exp in
        let vals_with_var = List.filter C.Value.is_variable vals in
        let vars = List.map C.Value.to_variable vals_with_var in
        (* Take the union to account for the inputs in phis *)
        let vars' = (vl2vs vars) || (vl2vs phi_vars) in
        let exps, inputs = VS.partition C.Variable.is_expression vars' in
        if VS.is_empty exps
        then acc || inputs
        else acc || inputs || (VS.fold (fun e acc -> aux acc e) exps VS.empty)
      else VS.singleton var
    in
    aux VS.empty output
  in
  let rec apply_filters vars = function
    | [] -> vars
    | h :: t -> VS.filter h (apply_filters vars t) in
  let remove_killed vs stmts =
    let vs = BatList.of_enum (VS.enum vs) in
    let stmt_avar = function
      | Ssa_ext.Statement.Move (avar, _, _) ->
        Some avar
      | _ ->
        None
    in
    let has_var_idx v l =
      let id = C.Variable.id v in
      List.exists (fun var ->
        (C.Variable.id var) = id) l
    in
    let remove v l =
      let id = C.Variable.id v in
      List.filter (fun var ->
        (C.Variable.id var) <> id) l
    in
    let module SS = BatSet.Make(String) in
    let seen = SS.empty in
    let (_, nvs) = List.fold_left (fun (seen, set) s ->
      match stmt_avar s with
      | None ->
        (seen, set)
      | Some avar when Ssa_ext_convenience.Variable.is_temp avar ->
        (* Calculations of temps are always live as far as we are concerned;
         * rely on the visibility/usefulness module to simply drop the TF
         * if something's not used later on.
         *)
        (seen, set)
      | Some avar->
        let n = Ssa_ext_convenience.Variable.name avar in
        (match SS.mem n seen with
        | false ->
          let nseen = SS.add n seen in
          dprintf "adding %s to seen" n;
          (nseen, set)
        | true ->
          assert (has_var_idx avar vs);
          let nset = remove avar set in
          dprintf "removing %s as seen" (Ssa_ext.Variable.to_string avar);
          (seen, nset))) (seen, vs) (List.rev stmts)
    in
    VS.of_enum (BatList.enum nvs)
  in
  let filter_outputs outputs =
    apply_filters
      outputs []
  in
  let get_tf_and_var output =
    let open Ssa_ext in
    match output with
    | Variable.VarExp(ary, Expression.Store(_, Value.Int _, (Value.Var var as value), _, _, _), _) ->
      (match C.Variable.Exceptionless.to_expression var with
      | Some e -> (C.Variable.of_var ary, e)
      | None -> (C.Variable.of_var ary, C.Expression.of_value value))
    | Variable.VarExp(ary, Expression.Store(_, Value.Int _, value, _, _, _), _) ->
      (C.Variable.of_var ary, Ssa_ext_convenience.Expression.of_value value)
    | _ -> (C.Variable.without_expression output, C.Variable.to_expression output)
  in
  (* This used to try and only keep the 'last' definition of a variable,
   * but was totally broken when it came to temps, as it was using the
   * name of the variable (hence it thought that all temp definitions
   * were definitions of the same location and would drop each but the
   * last one. Rely on our usefulness calculations in visibility.ml
   * instead, this is vestigial code.
  *)
(*  let outputs = remove_killed outputs stmts in *)
  BatList.of_enum (BatEnum.map (fun output ->
    let outvar, tf = get_tf_and_var output in
      {
        inputs = inputs_for_output output;
        f = Tf_norm.normalize tf;
        output = outvar
      }
      (* XXX: stale? Every store is consider output, so join the live outputs with the stores *)
    ) (VS.enum (VS.union (filter_outputs outputs) (VS.filter C.Variable.is_mem outputs))))

let to_string tf =
  Printf.sprintf "%s = f[%d -> 1]%s\n\twith TF := %s" (Ssa_ext.Variable.to_string tf.output)
    (VS.cardinal tf.inputs)
    (Print.enum_to_string ~enclosing:("(\n", "\n)") ~sep:",\n" Ssa_ext.Variable.to_string (VS.enum tf.inputs))
    (Ssa_ext.Expression.to_string ~decorators:[Ssa_ext.NamedNodes] tf.f)

let sexp_of_t tf =
  let open Sexplib in
  Sexp.List [
    Sexp.Atom "TF";
    Sexp.Atom (String.escaped (Ssa_ext.Variable.name tf.output));
    Ssa_ext.Expression.sexp_of_t tf.f;]

let dump ?oc tfs =
  let output = Print.enum_to_string ~enclosing:("","") ~sep:"\n\n"
    to_string tfs in
  match oc with
  | None -> dprintf "%s" output
  | Some oc -> Pervasives.output_string oc output

let to_dot oc pref ?(serial=0) tf =
  Ssa_ext.Expression.to_dot oc pref ~serial tf.f
