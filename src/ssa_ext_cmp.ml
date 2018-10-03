module D = Debug.Make(struct let name = "Ssa_ext_cmp" and default=`NoDebug end)
open D

open Ssa_ext

type valtype =
| VTVal of Value.t
| VTVars of Variable.t list

(*
 * This takes a function to reach into arg and get the boxing type
 * (if any) and then to unbox something of the same type as arg.
 * If the unboxing fails, it just returns arg.
 *)
let rec maybe_unbox_thusly unboxer1 unboxer2 unboxer3 arg =
  let (>>=) = BatOption.Monad.bind in
  let fin = (((Some arg) >>= unboxer1) >>= unboxer2) >>= unboxer3 in
  match fin with
  | Some narg ->
    (*
     * See if we can further unbox the thing we just unboxed.
     * This is pretty paranoid and I don't expect it'll happen in
     * practice, but let's be future-compatible here, it's easy.
     *)
    maybe_unbox_thusly unboxer1 unboxer2 unboxer3 narg
  | None -> arg

let maybe_unbox_pair unboxer1 unboxer2 unboxer3 (arg1, arg2) =
  let mut = maybe_unbox_thusly unboxer1 unboxer2 unboxer3 in
  (mut arg1, mut arg2)

let unbox_passthrough arg = Some arg

let extend_assumption ass (vs1, vs2) =
  let extend_single ass (v1, v2) =
    match ass with
    | Some (l1, l2) ->
      if (List.mem v1 l1) <> (List.mem v2 l2) then
        failwith "incompatible assumtions: just bail XXX: FIXME";
      Some (v1::l1, v2::l2)
    | None -> Some ([v1], [v2])
  in
  try
    List.fold_left (fun running p ->
      extend_single running p
    ) ass (List.combine vs1 vs2)
  with Invalid_argument _ ->
    let p = Print.list_to_string (Ssa_ext.Variable.to_string ~breaks:false) in
    dprintf "vs1: %d, vs2: %d" (List.length vs1) (List.length vs2);
    dprintf "vs1: %s\nvs2: %s" (p vs1) (p vs2);
    failwith "list length mismatch (internal error)"

let load_phi_to_load_vars = function
  | Expression.Load(Value.Var (Variable.VarExp (var, Expression.Phi vs, attrs)),
                               idx, e, typ, ldattrs) ->
    vs
  | _ -> failwith "internal error: not a Load(phi())"

let rec cmp_exprs (assumptions : Assumptions.t) ?running_assumption:(rass=None) e1 e2 =
  dprintf "cmp_exprs: %s\n--- vs ---\n%s" (Ssa_ext.Expression.to_string e1) (Ssa_ext.Expression.to_string e2);
  dprintf "assumptions: %s" (Assumptions.to_string assumptions);

  (*
   * Peek into the expressions. If any one of them holds a value, which
   * holds an expression, we want to shortcut that and look at the
   * doubly-boxed expression right away. This matters a lot when
   * we have Expression.SomeOp vs Expression.Val.Var.VarExp.SomeOp
   *)
  let e1, e2 = maybe_unbox_pair
    Ssa_ext_convenience.Expression.Exceptionless.to_value
    Ssa_ext_convenience.Value.Exceptionless.to_expression
    unbox_passthrough
    (e1, e2)
  in
  let binop_is op e =
    match e with
    | Expression.BinOp (op', _, _) -> op = op'
    | _ -> failwith "Not a binop"
  in
  let unop_is op e =
    match e with
    | Expression.UnOp (op', _) -> op = op'
    | _ -> failwith "Not a unop"
  in
  let cast_is ct t e =
    match e with
    | Expression.Cast (ct', t', _) ->
      (ct = ct') && (t = t')
    | _ -> failwith "Not a cast"
  in
  let try_pairing asxs val11 val12 val21 val22 =
    dprintf "try_pairing: fst pair";
    let (nasxs, ret) = cmp_vals asxs val11 val21 in
    match ret with
    | false -> (asxs, false)
    | true ->
      dprintf "try_pairing: snd pair";
      cmp_vals nasxs val12 val22
  in
  let try_both asxs val11 val12 val21 val22 =
    dprintf "try_both";
    let res = try_pairing asxs val11 val12 val21 val22 in
    match res with
    | (_, true) ->
      dprintf "try_both: first pairing: true";
      res
    | (_, false) ->
      dprintf "try_both: trying second pairing";
      let (nasxs, matched) = try_pairing asxs val11 val12 val22 val21 in
      dprintf "try_both: second pairing: %b" matched;
      (nasxs, matched)
  in
  let retpair_to_res (asxs, ret) =
    match ret with
    | true -> BatResult.Ok asxs
    | false -> BatResult.Bad "assumptions mismatch"
  in
  let do_phis assumptions e1 e2 =
    dprintf "do_phis";
    match (e1, e2) with
    | (Expression.Phi v1s, Expression.Phi v2s) ->
      if (List.length v1s) <> (List.length v2s) then
	(assumptions, false)
      else
	(match Assumptions.add_assumption assumptions (v1s, v2s) with
	| BatResult.Ok nasxs -> (nasxs, true)
	| BatResult.Bad _ -> (assumptions, false))
    | _ -> failwith "You can only pheed me phis"
  in
  let cmp_load assumptions e1 e2 =
    dprintf "cmp_load";
    match (e1, e2) with
    | Expression.Load (Value.Var (Variable.Var (_, _) as ary1), idx1, e1, typ1, _),
      Expression.Load (Value.Var (Variable.Var (_, _) as ary2), idx2, e2, typ2, _) when typ1 = typ2 ->
      assert (e1 = e2);
      dprintf "Ld(ary) vs Ld(ary)";
      begin
        match Assumptions.add_assumption assumptions ([ary1], [ary2]) with
        | BatResult.Ok nasxs -> cmp_vals nasxs idx1 idx2
        | BatResult.Bad _ -> (assumptions, false)
      end
    | Expression.Load (Value.Var (Variable.VarExp (_, (Expression.Phi _ as phi1), _)), idx1, e1, typ1, _),
      Expression.Load (Value.Var (Variable.VarExp (_, (Expression.Phi _ as phi2), _)), idx2, e2, typ2, _)
      when e1 = e2 && typ1 = typ2 ->
      dprintf "Ld(phi()) vs Ld(phi())";
      begin
        match do_phis assumptions phi1 phi2 with
        | (nasxs, true) -> cmp_vals nasxs idx1 idx2
        | (asxs, false) as ret -> ret
      end
    | _ -> (assumptions, false)
  in
  let do_cmp_store asxs ~idx1 ~val1 ~idx2 ~val2 =
      begin
        match cmp_vals asxs idx1 idx2 with
        | (asxs, false) as ret -> ret
        | (nasxs, true) ->
          begin
            cmp_vals nasxs val1 val2
          end
      end
  in
  let cmp_store assumptions e1 e2 =
    dprintf "cmp_store";
    match (e1, e2) with
    | Expression.Store (Value.Var (Variable.Var (_, _) as ary1), idx1, val1, e1, typ1, _),
      Expression.Store (Value.Var (Variable.Var (_, _) as ary2), idx2, val2, e2, typ2, _)
      when typ1 = typ2 && e1 = e2 ->
      dprintf "St(ary) vs St(ary)";
      begin
        match Assumptions.add_assumption assumptions ([ary1], [ary2]) with
        | BatResult.Bad _ -> (assumptions, false)
        | BatResult.Ok nasxs ->
          do_cmp_store nasxs ~idx1 ~val1 ~idx2 ~val2
      end
    | Expression.Store (Value.Var (Variable.VarExp (_, (Expression.Phi _ as phi1), _)), idx1, val1, e1, typ1, _),
      Expression.Store (Value.Var (Variable.VarExp (_, (Expression.Phi _ as phi2), _)), idx2, val2, e2, typ2, _)
      when e1 = e2 && typ1 = typ2 ->
      begin
        match do_phis assumptions phi1 phi2 with
        | (asxs, false) as ret -> ret
        | (nasxs, true) -> do_cmp_store nasxs ~idx1 ~val1 ~idx2 ~val2
      end
    | _ -> (assumptions, false)
  in
  let cmp_unop assumptions e1 e2 =
    match (e1, e2) with
    | (Expression.UnOp (_, val1), Expression.UnOp (_, val2)) ->
      cmp_vals assumptions val1 val2
    | _ -> failwith "internal error"
  in
  let cmp_ite assumptions vals1 vals2 =
    BatList.fold_left2 (fun acc val1 val2 ->
      let (acc_asxs, so_far) = acc in
      match so_far with
      | false -> acc (* pass on the fail bucket *)
      | true -> cmp_vals acc_asxs val1 val2
    ) (assumptions, true) vals1 vals2
  in
  let cmp_cast assumptions e1 e2 =
    match (e1, e2) with
    | (Expression.Cast (_, _, val1), Expression.Cast (_, _, val2)) ->
      cmp_vals assumptions val1 val2
    | _ -> failwith "internal error"
  in
  let cmp_extract assumptions e1 e2 =
    match (e1, e2) with
    | (Expression.Extract (_, _, val1), Expression.Extract (_, _, val2)) ->
      cmp_vals assumptions val1 val2
    | _ -> failwith "internal error"
  in
  let cmp_binop_non_commutative assumptions e1 e2 =
    let val11, val12 = match e1 with
      | Expression.BinOp (_, v1, v2) -> (v1, v2)
      | _ -> failwith "internal error"
    in
    let val21, val22 = match e2 with
      | Expression.BinOp (_, v1, v2) -> (v1, v2)
      | _ -> failwith "internal error"
    in
    try_pairing assumptions val11 val12 val21 val22
  in
  let cmp_binop_commutative asxs running_assumption this_op e1 e2 =
    dprintf "cmp_binop_commutative";
    let should_recurse val1 val2 =
      match (val1, val2) with
      | (Value.Var (Variable.VarExp (_, Expression.BinOp (op1, _, _), _)),
	 Value.Var (Variable.VarExp (_, Expression.BinOp (op2, _, _), _))) when
	  ((op1 = op2) && (op1 = this_op)) ->
	(* XXX: does this ever match? *)
	true
      | _ ->
	false
    in
    let do_all_vars rass vs11 vs12 vs21 vs22 =
      dprintf "do_all_vars";
      let vs_left = List.append vs11 vs12 in
      let vs_right = List.append vs21 vs22 in
      if (List.length vs_left) = (List.length vs_right) then begin
        let ass' = extend_assumption rass (vs_left, vs_right) in
        (match ass' with
        | Some ass'' ->
	  Assumptions.add_assumption asxs ass''
        | None -> failwith "can't happen")
      end else
        BatResult.Bad "free variables mismatch"
    in
    let classify value =
      let is_store exp =
	match exp with
	| Expression.Store _ -> true
	| _ -> false
      in
      let unbox = function
	| Value.Var v -> v
	| _ -> failwith "internal error"
      in
      let ret = match value with
        | Value.Var (Variable.Var (_, _)) ->
          VTVars [(unbox value)]
        | Value.Var
            (Variable.VarExp
               (_, ((Expression.Load
                      (Value.Var
                         (Variable.VarExp (_, Expression.Phi _, _)),
                       Value.Int (_, _), _, _, _)) as e), _)) ->
          let vs = load_phi_to_load_vars e in
          VTVars vs
        (* XXX: we don't differentiate betweeen loads/stores *)
        | Value.Var (Variable.VarExp (_, Expression.Load(Value.Var ary, _, _, _, _), _)) ->
          VTVars [ary]
        | Value.Var (Variable.VarExp (_, e, _)) when is_store e ->
          failwith "can't get here";
        | Value.Var (Variable.VarExp (_, Expression.Phi (vs), _)) ->
          VTVars vs
        | _ ->
          VTVal value
      in
      match ret with
      | VTVars _ as vtvars ->
        dprintf "classify: VTVars";
        vtvars
      | VTVal _ as vtval ->
        dprintf "classify: VTVal";
        vtval
    in
    let val11, val12 = match e1 with
      | Expression.BinOp (_, v1, v2) -> (v1, v2)
      | _ -> failwith "internal error"
    in
    let val21, val22 = match e2 with
      | Expression.BinOp (_, v1, v2) -> (v1, v2)
      | _ -> failwith "internal error"
    in
    let val11, val12 = maybe_unbox_pair
      Ssa_ext_convenience.Value.Exceptionless.to_expression
      Ssa_ext_convenience.Expression.Exceptionless.to_value
      unbox_passthrough
      (val11, val12)
    in
    let val21, val22 = maybe_unbox_pair
      Ssa_ext_convenience.Value.Exceptionless.to_expression
      Ssa_ext_convenience.Expression.Exceptionless.to_value
      unbox_passthrough
      (val21, val22)
    in
    let types = (classify val11, classify val12, classify val21, classify val22) in
    let res = match types with
      | (VTVars vs11, VTVars vs12, VTVars vs21, VTVars vs22) ->
	(match do_all_vars running_assumption vs11 vs12 vs21 vs22 with
        | BatResult.Ok nasxs as ok ->
          dprintf "do_all_vars: match!";
          ok
        | BatResult.Bad msg as err ->
          dprintf "do_all_vars: mismatch: %s" msg;
          err)

      | (VTVars vs1, VTVal val1, VTVal val2, VTVars vs2)
      | (VTVal val1, VTVars vs1, VTVal val2, VTVars vs2)
      | (VTVal val1, VTVars vs1, VTVars vs2, VTVal val2)
      | (VTVars vs1, VTVal val1, VTVars vs2, VTVal val2) ->
        if (List.length vs1) = (List.length vs2) then begin
	  let ass' = extend_assumption running_assumption (vs1, vs2) in
	  if should_recurse val1 val2 then begin
	    (* the assumption remains running *)
	    let rp = cmp_vals asxs ~running_assumption:ass' val1 val2 in
	    retpair_to_res rp
	  end else begin
	    (match ass' with
	    | Some ass'' ->
	      (match Assumptions.add_assumption asxs ass'' with
	      | BatResult.Ok asxs' ->
	        let rp = cmp_vals asxs' val1 val2 in
	        retpair_to_res rp
	      | BatResult.Bad _ as bad -> bad)
	    | None -> failwith "can't happen")
	  end
        end else
          BatResult.Bad "free variables mismatch2"
      | _ ->
	let nasxs = (match running_assumption with
	| Some rass ->
	  (match Assumptions.add_assumption asxs rass with
	  | BatResult.Ok nasxs -> nasxs
	  | BatResult.Bad _ -> asxs)
	| None -> asxs) in
	retpair_to_res (try_both nasxs val11 val12 val21 val22)
    in
    match res with
    | BatResult.Ok nasxs -> (nasxs, true)
    | BatResult.Bad _ -> (asxs, false)
  in
  let cmp_different_exprs e1 e2 =
    let module LH =             (* Local helpers *)
    struct
      module Ary = Var_convenience.Array
      module C = Ssa_ext_convenience

      let unpack_var = function
        | Value.Var (Variable.Var (v,_)) -> v
        | _ -> failwith "Failed to unpack Var.t from Ssa_Ext.Value!"
      let is_zero v =
        let open Big_int_convenience in
        match v with
        | Value.Int (bi, _) when bi ==% bi0 -> true
        | Value.Int _ -> false
        | _ -> failwith "Invalid Ssa_ext.Value for is_zero!"
      let is_esp_based ary =
        let open Ary in
        is_array ary && Var.name (base_reg ary) = "R_ESP"
      let bounds_size ary =
        let open Ary in
        let open Big_int_Z in
        let open Big_int_convenience in
        let bounds = bounds ary in
        match Interval.Big_int.begin_ bounds,
              Interval.Big_int.end_ bounds with
        | Some lb, Some ub ->
          let diff = ub -% lb in
          int_of_big_int (succ_big_int diff)
        | _ -> failwith "Cannot determine bounds of array!"
      let has_expected_bounds ary size =
        Type.Reg ((bounds_size ary)*8) = size
      let has_pos_lb ary =
        let open Big_int_convenience in
        let open Ary in
        match Interval.Big_int.begin_ (bounds ary) with
        | Some lb -> bi0 <=% lb
        | None -> failwith "Cannot determine lb of array bounds!"
      let is_arg_load =  function
        | Expression.Load (ary, idx, edn, size, _)
          when is_esp_based (unpack_var ary)
            && is_zero idx
            && has_pos_lb (unpack_var ary)
            && has_expected_bounds (unpack_var ary) size-> true
        | _ -> false
    end in
    dprintf "cmp_different_exprs";
    match (e1, e2) with
    | Expression.Val (Value.Int (i1, t1)), e
    | e, Expression.Val (Value.Int (i1, t1)) ->
      dprintf "Int vs Expression";
      (*
       * XXX: this works for toplevel expressions, but if they're further
       * down, we need to add the enclosing Variables to the assumptions
       * and, at this point in the call stack, we don't have that information
       * at hand...
       *)
      let (>>=) = BatOption.Monad.bind in
      let unbox_int_of_value = function
          | Ssa_ext.Value.Int (i, t) -> Some (i, t)
          | _ -> None
      in
      let try_value_int e =
        ((Some e) >>= Ssa_ext_convenience.Expression.Exceptionless.to_value) >>=
          unbox_int_of_value
      in
      let try_store_int = function
        | Expression.Store (_, _, data, _, _, _) ->
          unbox_int_of_value data
        | _ -> None
      in
      List.fold_left (fun (assumptions, matched) func ->
        match matched with
        | true -> (assumptions, true)
        | false ->
          (match func e with
          | None ->
            (assumptions, false)
          | Some (i2, t2) ->
            (assumptions, (Big_int_convenience.(==%) i1 i2) && (t1 = t2))))
        (assumptions, false) [try_value_int; try_store_int]
    | Expression.Phi vs, (Expression.Load(Value.Var
                                            (Variable.VarExp (_, Expression.Phi _, _)),
                                          _, _, _, _) as e) ->
      let vs' = load_phi_to_load_vars e in
      if (List.length vs) = (List.length vs') then begin
        dprintf "Rewriting phi() vs Load(phi(), )";
        (match Assumptions.add_assumption assumptions (vs, vs') with
         | BatResult.Ok nasxs -> (nasxs, true)
         | BatResult.Bad _ -> (assumptions, false))
      end else
        (assumptions, false)
    | (Expression.Load(Value.Var (Variable.VarExp
                                    (_, Expression.Phi _, _)),
                      _, _, _, _) as e), Expression.Phi vs ->
      let vs' = load_phi_to_load_vars e in
      if (List.length vs) = (List.length vs') then begin
        dprintf "Rewriting phi() vs Load(phi(), )";
        (match Assumptions.add_assumption assumptions (vs', vs) with
        | BatResult.Ok nasxs -> (nasxs, true)
        | BatResult.Bad _ -> (assumptions, false))
      end else
        (assumptions, false)
    | Expression.Load (ary,_,_,_,_) as l, Expression.Val (Value.Var v)
      when LH.is_arg_load l -> begin
        let ary = Ssa_ext_convenience.Value.to_variable ary in
        match Assumptions.add_assumption assumptions ([ary], [v]) with
        | BatResult.Ok nasxs -> (nasxs, true)
        | BatResult.Bad _ -> (assumptions, false)
      end
    | Expression.Val (Value.Var v), (Expression.Load (ary,_,_,_,_) as l)
      when LH.is_arg_load l -> begin
        let ary = Ssa_ext_convenience.Value.to_variable ary in
        match Assumptions.add_assumption assumptions ([v], [ary]) with
        | BatResult.Ok nasxs -> (nasxs, true)
        | BatResult.Bad _ -> (assumptions, false)
      end
    (* XXX: Store *)
    | _ ->
      dprintf "num1: %d, num2: %d" (num_exp e1) (num_exp e2);
      (assumptions, false)
  in
  match (num_exp e1) <> (num_exp e2) with
  | true ->
    cmp_different_exprs e1 e2
  | false ->
    (match e1 with
    | Expression.Unknown (_, _) ->
      (assumptions, false)
    | Expression.Phi _ ->
      do_phis assumptions e1 e2
    (* XXX: Currently this is guarded by cmp_vals, but we have to deal with loads and stores! *)
    | Expression.Load _ ->
      (*
       * AFAICT, we can only get here for toplevel loads; otherwise, this
       * would have been handled in cmp_vals. Assert that this is so.
      *)
      assert (rass = None);
      cmp_load assumptions e1 e2
    | Expression.Store _ ->
      cmp_store assumptions e1 e2
    | Expression.Val val1 ->
      (match e2 with
      | Expression.Val val2 -> cmp_vals assumptions val1 val2
      | _ -> failwith "can't happen")
    | Expression.BinOp (op1, _, _) ->
      dprintf "binops";
      if binop_is op1 e2 then begin
	if binop_is_commutative op1 then
	  cmp_binop_commutative assumptions rass op1 e1 e2
	else
	  cmp_binop_non_commutative assumptions e1 e2
      end else
	(assumptions, false)
    | Expression.UnOp (op1, _) ->
      if unop_is op1 e2 then
	cmp_unop assumptions e1 e2
      else
	(assumptions, false)

    | Expression.Ite (val11, val12, val13) ->
      (match e2 with
      | Expression.Ite (val21, val22, val23) ->
	cmp_ite assumptions [val11; val12; val13] [val21; val22; val23]
      | _ ->
	(assumptions, false))

    | Expression.Cast (cast_type, typ, _) ->
      if cast_is cast_type typ  e2 then
	cmp_cast assumptions e1 e2
      else
	(assumptions, false)

    | Expression.Concat (val11, val12) ->
      (match e2 with
      | Expression.Concat (val21, val22) ->
	try_pairing assumptions val11 val12 val21 val22
      | _ -> (assumptions, false))

    | Expression.Extract (h1, l1, val1) ->
      (match e2 with
      | Expression.Extract (h2, l2, val2) ->
	if (h1 = h2) && (l1 = l2) then
	  cmp_extract assumptions e1 e2
	else
	  (assumptions, false)
      | _ -> (assumptions, false)))

and cmp_vars assumptions ?running_assumption:(rass=None) _var1 _var2 =
  let can_pair ~var ~ary =
    let open Big_int_Z in
    let ary_size = Var_convenience.Array.size (Ssa_ext_convenience.Variable.var ary) in
    let var_size = big_int_of_int (Typecheck.bytes_of_width (Ssa_ext_convenience.Variable.typ var)) in
    compare_big_int var_size ary_size = 0
  in
  dprintf "cmp_vars: %s\n--- vs ---\n%s" (Ssa_ext.Variable.to_string _var1) (Ssa_ext.Variable.to_string _var2);
  let _var1, _var2 = maybe_unbox_pair
    Ssa_ext_convenience.Variable.Exceptionless.to_expression
    Ssa_ext_convenience.Expression.Exceptionless.to_value
    Ssa_ext_convenience.Value.Exceptionless.to_variable
    (_var1, _var2)
  in
  let add_assumption v1 v2 =
    match Assumptions.add_assumption assumptions ([v1], [v2]) with
    | BatResult.Ok asxs -> (asxs, true)
    | BatResult.Bad _ -> (assumptions, false)
  in
  match (_var1, _var2) with
  | (Variable.Var (_, _), Variable.Var (_, _)) ->
    (match extend_assumption rass ([_var1], [_var2]) with
    | Some asx ->
      (match Assumptions.add_assumption assumptions asx with
      | BatResult.Ok nasxs -> (nasxs, true)
      | BatResult.Bad _ -> (assumptions, false))
    | None -> (assumptions, false))

  (* Can only match a Var against a VarExp if the VarExp is a load/store *)
  | (Variable.Var (_, _), Variable.VarExp (_, Expression.Load(Value.Var ary, _, _, typ, _), _))
    when Ssa_ext_convenience.Variable.typ _var1 = typ && can_pair ~var:_var1 ~ary ->
    add_assumption _var1 ary
  | (Variable.VarExp (_, Expression.Load(Value.Var ary, _, _, typ, _), _), Variable.Var (_, _))
    when Ssa_ext_convenience.Variable.typ _var2 = typ && can_pair ~var:_var2 ~ary ->
    add_assumption ary _var2

  | (Variable.Var (_, _), Variable.VarExp (_, _, _)) ->
    (assumptions, false)
  | (Variable.VarExp (_, _, _), Variable.Var (_, _)) ->
    (assumptions, false)

  | (Variable.VarExp (_, e1, _), Variable.VarExp (_, e2, _)) ->
    cmp_exprs assumptions ~running_assumption:rass e1 e2

and cmp_vals assumptions ?running_assumption:(rass=None) val1 val2 =
  dprintf "cmp_vals: %s\n--- vs ---\n%s" (Ssa_ext.Value.to_string val1) (Ssa_ext.Value.to_string val2);
  (*
   * If a val holds a variable, which is a VarExp, and the attached
   * expression holds a val, just look at the inner val here. This
   * is analogous to the cmp_exprs case except here I've no idea if
   * this can actually happen -- aggelos.
   *)
  let val1, val2 = maybe_unbox_pair
    Ssa_ext_convenience.Value.Exceptionless.to_expression
    Ssa_ext_convenience.Expression.Exceptionless.to_value
    unbox_passthrough
    (val1, val2)
  in

  match (val1, val2) with
  | (Value.Int(i1, t1), Value.Int(i2, t2)) ->
    (assumptions, (Big_int_convenience.(==%) i1 i2) && (t1 = t2))
  | (Value.Lab l1, Value.Lab l2) -> failwith "dunno what to do with labs"
  | (Value.Var var1, Value.Var var2) -> cmp_vars assumptions ~running_assumption:rass var1 var2
  | _ -> (assumptions, false)

let chunks_equiv assumptions e1 e2 =
  let b = new Perfacc.bench "compare_two_tfs" in
  b#start (Printf.sprintf "%s ||| %s" (Expression.to_string e1) (Expression.to_string e2));
  try
    let (nasxs, success) = cmp_exprs assumptions e1 e2 in
    let features =
      if success then begin
        [
          float_of_int (Assumptions.number assumptions);
          float_of_int (Assumptions.number nasxs);
        ]
      end else
        []
    in
    b#stop ~features ();
    (nasxs, success)
  with exn ->
    b#stop ();
    raise exn
