(**
    Helper functions for extended static assignment form.
    @author Remco Vermeulen
 *)

open Ssa_ext

let reg_1  = Type.Reg 1
let reg_8  = Type.Reg 8
let reg_16 = Type.Reg 16
let reg_32 = Type.Reg 32
let reg_64 = Type.Reg 64
let reg_128  = Type.Reg 128
let reg_256  = Type.Reg 256

(** Creates a new variable of the given type *)
let new_var ?(attrs=[]) name typ = Variable.Var (Var.newvar name typ, attrs)
(* XXX: Have to take the size of the expression into consideration *)
let tmp_var_from_exp e = Variable.VarExp (Var.newvar "temp" reg_32, e, [])

(** Helper for creating Move expression *)
let move ?(attrs=[]) value exp = Statement.Move (value,exp,attrs)

module Variable =
struct
  let create ?(attrs=[]) name typ =
    Variable.Var ((Var.newvar name typ), attrs)

  let id = function
    | Variable.Var (Var.V(id,_,_),_)
    | Variable.VarExp (Var.V(id,_,_),_,_) -> id

  let typ = function
    | Variable.Var (Var.V(_,_,typ),_)
    | Variable.VarExp (Var.V(_,_,typ),_,_) -> typ

  let name = function
    | Variable.Var (Var.V(_,name,_),_)
    | Variable.VarExp (Var.V(_,name,_),_,_) -> name

  let attrs = function
    | Variable.Var (_,attrs)
    | Variable.VarExp (_,_,attrs) -> attrs

  let var = function
    | Variable.Var (v,_)
    | Variable.VarExp(v,_,_) -> v

  let of_var ?(attrs=[]) v =
    Variable.Var (v,attrs)

  let is_temp var =
    let has_prefix s ~prefix =
      let length_prefix = String.length prefix in
      try Str.string_before s length_prefix = prefix
      with Invalid_argument _ -> false in
    let name = name var in
    name = "temp" || name = "tempmem" || name = "T_ra" || name = "tempval" ||
	name = "T_phi" || name = "T_origCOUNT" || name = "T_origDEST"
        || has_prefix name ~prefix:"T_t" || has_prefix name ~prefix:"T_vrg"

  let is_mem var =
    let name = name var in
    name = "mem" || name = "mem_array" || name = "tempmem" || name = "loadnorm"

  let is_bool v = (typ v) = (Type.Reg 1)

  let is_array v = match (typ v) with
    | Type.Reg _ | Type.TMem _ -> false
    | Type.Array _ -> true

  let to_expression = function
    | Variable.VarExp (_,exp,_) -> exp
    | _ -> raise Not_found

  let without_expression = function
    | Ssa_ext.Variable.Var _ as v -> v
    | Ssa_ext.Variable.VarExp (v,_,attrs) -> Ssa_ext.Variable.Var (v,attrs)

  let is_expression = function
    | Ssa_ext.Variable.VarExp _ -> true
    | Ssa_ext.Variable.Var _ -> false

  let with_expression var exp =
    match var with
    | (Ssa_ext.Variable.Var (v, attrs)) ->
      Ssa_ext.Variable.VarExp (v, exp, attrs)
    | Ssa_ext.Variable.VarExp _ -> failwith "Variable already contains an expression!"

  module Exceptionless = struct
    let to_expression = function
      | Variable.VarExp (_,exp,_) -> Some exp
      | _ -> None
  end
end

module Value =
struct
  let is_integer = function
    | Ssa_ext.Value.Int _ -> true
    | _ -> false

  let is_label = function
    | Ssa_ext.Value.Lab _ -> true
    | _ -> false

  let is_variable = function
    | Ssa_ext.Value.Var _ -> true
    | _ -> false

  let to_variable = function
    | Ssa_ext.Value.Var v -> v
    | _ -> raise Not_found

  let of_variable var =
    Ssa_ext.Value.Var var

  let to_expression v=
    Variable.to_expression (to_variable v)

  module Exceptionless = struct
    let to_variable = function
      | Ssa_ext.Value.Var v -> Some v
      | _ -> None

    let to_expression v =
      match to_variable v with
      | Some var -> Variable.Exceptionless.to_expression var
      | None -> None
  end

  let to_ast = function
    | Ssa_ext.Value.Int (bi, typ) -> Ast.Int (bi,typ)
    | Ssa_ext.Value.Var v -> Ast.Var (Variable.var v)
    | Ssa_ext.Value.Lab s -> Ast.Lab s
end

module Expression =
struct
  let to_value = function
    | Ssa_ext.Expression.Val v -> v
    | _ -> raise Not_found

  let of_value v =
    Ssa_ext.Expression.Val v

  let rec fold f exp acc =
    let fold_exp_in_var v acc =
      match Variable.Exceptionless.to_expression v with
      | Some exp' -> fold f exp' acc
      | None -> acc
    in
    let fold_exp_in_val v acc =
      match v with
      | Ssa_ext.Value.Int _ -> acc
      | Ssa_ext.Value.Var v' -> fold_exp_in_var v' acc
      | Ssa_ext.Value.Lab _ -> acc
    in
    let vals,_,_,_,_,_,_,_,_ = Ssa_ext.Expression.getargs exp in
    List.fold_left (fun acc v -> fold_exp_in_val v acc) (f exp acc) vals

  module Exceptionless = struct
    let to_value = function
      | Ssa_ext.Expression.Val v -> Some v
      | _ -> None
  end

  let to_ast = function
    | Ssa_ext.Expression.Load (mem, idx, endian, t, _) ->
      Ast.Load (Value.to_ast mem, Value.to_ast idx, Value.to_ast endian, t)
    | _ -> failwith "Hit an unimplemented conversion from extended SSA to AST!"
end

(* vim: set ts=8 sw=2 tw=80 et :*)
