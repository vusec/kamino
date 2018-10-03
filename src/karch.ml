(** This module contains architecture specific functions *)

open BatPervasives

module X86 =
struct
  module C = Ssa_ext_convenience

  let cflow_relevant_flags defs stmts =
    let last_stmt = BatList.last stmts in
    let is_bitreg v = (C.Variable.typ v) = (Type.Reg 1) in
    let is_flag v = (is_bitreg v) && (not (C.Variable.is_temp v)) in
    let rec get_flags defs v =
      match is_flag v with
      | true -> [C.Variable.name v]
      | false ->
        try
          let exp = Ssa_ext.VariableHash.find defs v in
          match exp with
          | Ssa_ext.Expression.Val (Ssa_ext.Value.Var v) when is_flag v ->
            [C.Variable.name v]
          | Ssa_ext.Expression.UnOp _
          | Ssa_ext.Expression.BinOp _ ->
            let (values,_,_,_,_,_,_,_,_) = Ssa_ext.Expression.getargs exp in
            let variables = List.map
                C.Value.to_variable
                (List.filter C.Value.is_variable values)
            in
            List.fold_left (fun acc var ->
                acc @ (get_flags defs var)) [] variables
          | _ -> []
        with Not_found -> []
    in
    match last_stmt with
    | Ssa_ext.Statement.CJmp (cond,_,_,_) when C.Value.is_variable cond ->
      let v = C.Value.to_variable cond in
      get_flags defs v
    | _ -> []

  let is_stack_reg var = (Var.name var) = "R_ESP"

  let filter_vars_if_well_behaved well_behaved vars =
    match well_behaved with
    | true -> List.filter (fun v -> not (is_stack_reg v)) vars
    | false -> vars

end
