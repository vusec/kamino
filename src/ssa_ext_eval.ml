(**
    Evaluation of extended ssa instructions.
    @author Remco Vermeulen
*)

module D = Debug.Make(struct let name = "SsaExtEval" and default=`NoDebug end)
open D

module VH = Var.VarHash
(** Module that provides a mapping of an address to a byte. *)
module AddressMap = Map.Make(Int64)

type eval_val = Symbolic of Ssa_ext.Expression.t | Concrete of Big_int_Z.big_int * Type.typ

let is_symbolic = function
  | Symbolic _ -> true
  | _ -> false

let is_true_val = function
  | Symbolic _ -> failwith "Symbolic evaluation of true is not implemented!"
  | Concrete (v, typ) -> Big_int_convenience.bi_is_one v

let symbolic_to_value = function
  | Symbolic (Ssa_ext.Expression.Val v) -> v
  | _ -> failwith "Cannot convert symbolic value to a value!"

let concrete_value = function
  | Concrete (i,t) -> (i,t)
  | _ -> failwith "Trying to concretize symbolic value!"

type ('delta, 'formula) ctx = {
  path: 'formula;
  delta: 'delta;
  sigma: (Type.addr, Ssa_ext.Statement.t) Hashtbl.t;
  lambda: (Type.label, Type.addr) Hashtbl.t;
  pc: Type.addr
}

(** Interface for a memory model. *)
module type MemoryLookupSig =
sig
  (** Memory lookup type *)
  type t

  (** Create a new lookup table *)
  val create : unit -> t

  (** Lookup the value of a variable *)
  val lookup_var : t -> Ssa_ext.Variable.t -> eval_val
  (** Update the value of a variable *)
  val update_var : t -> Ssa_ext.Variable.t -> eval_val -> t

  (** Lookup the value at a memory address *)
  val lookup_mem : t -> eval_val -> eval_val -> eval_val -> Type.typ -> eval_val
  (** Update the value at a memory address *)
  val update_mem : t -> eval_val -> eval_val -> eval_val -> eval_val -> t
end

(** Interface for an expression evaluator. *)
module type EvaluatorSig =
sig
  (** Type of the context used during the evaluation *)
  type t

  (** Initialize evaluator *)
  val create : unit -> t

  (** Evaluate an extended ssa stmt *)
  val eval_stmt : t -> Ssa_ext.Statement.t -> t list
end

module type FormulaSig =
sig
  type t

  val add_to_formula : t -> Ssa_ext.Expression.t -> t

  val true_formula : t

  val formula : t -> t
end

(** Functor building an implementation of an evaluator given a memory model *)
module Make (MemoryLookup : MemoryLookupSig) (Formula : FormulaSig)
  : EvaluatorSig
    with type t = (MemoryLookup.t, Formula.t) ctx
= struct
  type t = (MemoryLookup.t, Formula.t) ctx

  let create ()  =
    let path = Formula.true_formula in
    let delta = MemoryLookup.create () in
    let sigma : (Type.addr, Ssa_ext.Statement.t) Hashtbl.t = Hashtbl.create 16 in
    let lambda : (Type.label, Type.addr) Hashtbl.t = Hashtbl.create 16 in
    let pc = Int64.zero in
    {path=path; delta=delta; sigma=sigma; lambda=lambda; pc=pc}

  (** Evaluation of extended ssa definitions *)
  let rec eval_var delta = function
    | Ssa_ext.Variable.Var _ as var -> MemoryLookup.lookup_var delta var
    | Ssa_ext.Variable.VarExp (_,e,_) -> eval_exp delta e
  (** Evaluation of extended ssa values *)
  and eval_val delta = function
    | Ssa_ext.Value.Int (i, t) -> Concrete (i,t)
    | Ssa_ext.Value.Var v -> eval_var delta v
    | Ssa_ext.Value.Lab _ -> failwith "Trying to evaluate a label!"
  (** Evaluation of extended ssa expressions *)
  and eval_exp delta = function
    | Ssa_ext.Expression.Load (arr, idx, endian, typ, _) ->
      let arr = eval_val delta arr in
      let idx = eval_val delta idx in
      let endian = eval_val delta endian in
      MemoryLookup.lookup_mem delta arr idx endian typ
    | Ssa_ext.Expression.Store (arr, idx, value, endian, typ, _) ->
      let arr = eval_val delta arr in
      let idx = eval_val delta idx in
      let value = eval_val delta value in
      let endian = eval_val delta endian in
      let () = ignore(MemoryLookup.update_mem delta arr idx value endian) in
      MemoryLookup.lookup_mem delta arr idx endian typ
    | Ssa_ext.Expression.Ite (cond, v2, v3) ->
      if is_true_val (eval_val delta cond)
      then (eval_val delta v2)
      else (eval_val delta v3)
    | Ssa_ext.Expression.Extract (i1, i2, value) ->
      let value = eval_val delta value in
      if is_symbolic value
      then Symbolic (Ssa_ext.Expression.Extract(i1,i2, symbolic_to_value value))
      else let (v,t) = (Arithmetic.extract i1 i2 (concrete_value value))
        in Concrete (v,t)
    | Ssa_ext.Expression.Concat (v1, v2) ->
      let v1 = eval_val delta v1 in
      let v2 = eval_val delta v2 in
      if (is_symbolic v1) || (is_symbolic v2)
      then Symbolic (Ssa_ext.Expression.Concat (symbolic_to_value v1, symbolic_to_value v2))
      else let (v,t) = (Arithmetic.concat (concrete_value v1) (concrete_value v2)) in
        Concrete (v,t)
    | Ssa_ext.Expression.BinOp (t, v1, v2) ->
      let v1 = eval_val delta v1 in
      let v2 = eval_val delta v2 in
      if (is_symbolic v1) || (is_symbolic v2)
      then Symbolic (Ssa_ext.Expression.BinOp (t,(symbolic_to_value v1),(symbolic_to_value v2)))
      else let (v,t) = Arithmetic.binop t (concrete_value v1) (concrete_value v2) in
        Concrete (v,t)
    | Ssa_ext.Expression.UnOp (t, v) ->
      let v = eval_val delta v in
      if is_symbolic v
      then Symbolic (Ssa_ext.Expression.UnOp (t, (symbolic_to_value v)))
      else let (v,t) = Arithmetic.unop t (concrete_value v) in
        Concrete (v,t)
    | Ssa_ext.Expression.Val v -> eval_val delta v
    | Ssa_ext.Expression.Cast (c, t, v) ->
      let v = eval_val delta v in
      if is_symbolic v
      then Symbolic (Ssa_ext.Expression.Cast (c, t, symbolic_to_value v))
      else let (v,t) = Arithmetic.cast c (concrete_value v) t in
        Concrete (v,t)
    | Ssa_ext.Expression.Unknown (s, t) -> failwith "Trying to evaluate an unknown!"
    (* We take the first value from the list, therefore the evaluation is
     * insensitive to control flow.*)
    | Ssa_ext.Expression.Phi l -> eval_var delta (List.hd l)
  and eval_stmt ctx stmt =
    let next_pc = Int64.succ ctx.pc in
    match stmt with
    | Ssa_ext.Statement.Move (var, exp, attrs) ->
      (match var with
       | Ssa_ext.Variable.Var (v,_) ->
         let () = ignore(MemoryLookup.update_var ctx.delta var (eval_exp ctx.delta exp))
         in
         [{ctx with pc = next_pc}]
       | Ssa_ext.Variable.VarExp _ -> failwith "Cannot assign variable to an expression!")
    | _ -> let err =
      Printf.sprintf "Evaluation of stmt %s not implemented!"
		    (Ssa_ext.Statement.to_string stmt)
      in failwith err

end

(** Implementation of a memory model that randomly initializes unitialized variables and memory *)
module RandomInitializedMemoryLookup : MemoryLookupSig
  with type t = ((Ssa_ext.Variable.t,(Big_int_Z.big_int * Type.typ)) Hashtbl.t  * (Big_int_Z.big_int * Type.typ) AddressMap.t) ref
= struct
  (** Type of the memory model *)
  type t = ((Ssa_ext.Variable.t,(Big_int_Z.big_int * Type.typ)) Hashtbl.t  * (Big_int_Z.big_int * Type.typ) AddressMap.t) ref

  (** Type of the values stored in variables and memory *)
  type value = Big_int_Z.big_int * Type.typ

  (** Helper function that returns the size of a type in bits *)
  let rec size_of_type_in_bits = function
    | Type.Reg i -> i
    | Type.TMem typ -> size_of_type_in_bits typ
    | Type.Array _ -> failwith "Cannot determine size of array type!"

  (** Helper function that returns the size of a type in bytes *)
  let size_of_type_in_bytes typ = (size_of_type_in_bits typ) / 8

  (** Helper function that generates a new value of a given type *)
  let new_value_of_type typ =
    (Big_int_convenience_ext.random (size_of_type_in_bits typ), typ)

  (** Helper function that generates a new value for a given variable *)
  let new_value = function
    | Ssa_ext.Variable.Var (Var.V (_,_,typ),_)
    | Ssa_ext.Variable.VarExp (Var.V (_,_,typ),_,_) -> new_value_of_type typ

  (** Initializing a new instance of the memory model  *)
  let create () = ref (Hashtbl.create 1024, AddressMap.empty)

  (** Returns the value of a variable or initializes it with a random variable when unitialized *)
  let lookup_var {contents=(variables, _)} var =
    if Hashtbl.mem variables var
    then let (v,t) = Hashtbl.find variables var in Concrete (v,t)
    else
      let (v,t) = new_value var in
      let () = Hashtbl.add variables var (v,t) in
      Concrete (v,t)

  (** Updates the value of a variable, or initializes an unitialized variable with the given value *)
  let update_var {contents=(variables, memory)} var = function
    | Concrete(v,t) ->
      if Hashtbl.mem variables var
      then Hashtbl.replace variables var (v,t)
      else Hashtbl.add variables var (v,t);
      {contents=(variables, memory)}
    | _ -> failwith "Trying to update variable with symbolic value!"

  (** Returns the value of a given type at the given address or initializes it with a random variable when unitialized *)
  let lookup_mem delta arr idx endian typ =
    if (is_symbolic arr) || (is_symbolic idx) || (is_symbolic endian)
    then failwith "Trying to do a concrete lookup with symbolic values"
    else
      match delta with
        {contents=(variables, memory)} ->
        (match endian with
         | Concrete (bi, Type.Reg 1) when Big_int_convenience.bi_is_zero bi ->
           let lookup_byte addr =
             if AddressMap.mem addr memory then AddressMap.find addr memory
             (* If not yet mapped, map a random initialized byte. *)
             else let new_byte = new_value_of_type typ in
               let () = delta := (variables, AddressMap.add addr new_byte memory) in
               new_byte
           in
           let result = ref Big_int_Z.zero_big_int in
           let (addr,_) = concrete_value idx in
           let addr = Big_int_Z.int64_of_big_int addr in
           for pos=0 to ((size_of_type_in_bytes typ) - 1)
           do
             let (byte, typ_of_byte) = lookup_byte (Int64.add addr (Int64.of_int pos))  in
             let () = assert(typ_of_byte = (Type.Reg 8)) in
             let shifted_byte = Big_int_Z.shift_left_big_int byte (pos*8) in
             result := Big_int_Z.or_big_int !result shifted_byte
           done;
           Concrete (!result, typ)
         | Concrete (bi, Type.Reg 1) when Big_int_convenience.bi_is_one bi ->
           failwith "Big-endian memory lookup is not implemented!"
         | _ -> failwith "Invalid endianess for memory lookup!" )

  (** Updates the value at a given address, or initializes an unitialized value with the given value *)
  let update_mem delta arr idx value endian =
    if (is_symbolic arr) || (is_symbolic idx) || (is_symbolic value) || (is_symbolic endian)
    then failwith "Trying to do a concrete memory update with symbolic values"
    else
      match !delta with
        (variables, memory) -> match endian with
        | Concrete (bi, reg_1) when Big_int_convenience.bi_is_zero bi ->
          let (addr,_) = concrete_value idx in
          let addr = Big_int_Z.int64_of_big_int addr in
          let (value,typ) = concrete_value value in
          for pos=0 to ((size_of_type_in_bytes typ))
          do
            let shifted_value = Big_int_Z.shift_right_big_int value (pos*8) in
            let byte = (Big_int_Z.extract_big_int shifted_value 0 8, Type.Reg 8) in
            delta := (variables, AddressMap.add
                        (Int64.add addr (Int64.of_int pos)) byte memory)
          done;
          delta
        | Concrete (bi, reg_1) when Big_int_convenience.bi_is_one bi ->
          failwith "Big-endian memory update is not implemented!"
        | _ -> failwith "Invalid endianess for memory update!"

end

module NullFormula : FormulaSig
  with type t = Ssa_ext.Expression.t
= struct
  type t = Ssa_ext.Expression.t

  let add_to_formula formula addition =
    let formula = Ssa_ext.Value.Var (Ssa_ext.Variable.VarExp (Var.newvar "old_formula" Ssa_ext_convenience.reg_32,formula, [])) in
    let addition = Ssa_ext.Value.Var (Ssa_ext.Variable.VarExp (Var.newvar "addition" Ssa_ext_convenience.reg_32, addition, [])) in
    Ssa_ext.Expression.BinOp (Type.AND, formula, addition)

  let true_formula = Ssa_ext.Expression.Val (Ssa_ext.Value.Int (Big_int_convenience.bi1 , Ssa_ext_convenience.reg_1))

  let formula f = f
end

module EspInitializedMemoryLookup : MemoryLookupSig
  with type t = ((Ssa_ext.Variable.t,(Big_int_Z.big_int * Type.typ)) Hashtbl.t  * (Big_int_Z.big_int * Type.typ) AddressMap.t) ref
= struct
  (** Type of the memory model *)
  type t = ((Ssa_ext.Variable.t,(Big_int_Z.big_int * Type.typ)) Hashtbl.t  * (Big_int_Z.big_int * Type.typ) AddressMap.t) ref

  (** Type of the values stored in variables and memory *)
  type value = Big_int_Z.big_int * Type.typ

  let is_esp var = (Ssa_ext_convenience.Variable.name var) = "R_ESP"

  (** Initializing a new instance of the memory model  *)
  let create () = ref (Hashtbl.create 1, AddressMap.empty)

  (** Returns the value of a variable or initializes it if it is the first
   * encounted esp *)
  let lookup_var {contents=(variables, _)} var =
    if Hashtbl.mem variables var
    then let (v,t) = Hashtbl.find variables var in Concrete (v,t)
    else
      (match is_esp var with
       | true -> dprintf "Zero-initializing esp.";
         let zero = (Big_int_convenience.bi0, Ssa_ext_convenience.reg_32) in
         Hashtbl.add variables var zero;
         Concrete (fst zero, snd zero)
       | false -> failwith (Printf.sprintf "Unexpected lookup of unitialized variable '%s' !"
                              (Ssa_ext_convenience.Variable.name var)))

  (** Updates the value of a variable, or initializes an unitialized variable with the given value *)
  let update_var {contents=(variables, memory)} var = function
    | Concrete(v,t) ->
      if Hashtbl.mem variables var
      then Hashtbl.replace variables var (v,t)
      else Hashtbl.add variables var (v,t);
      {contents=(variables, memory)}
    | _ -> failwith "Trying to update variable with symbolic value!"
  let lookup_mem delta arr idx endian typ =
    failwith "Unexpected memory lookup!"
  let update_mem delta arr idx value endian =
    failwith "Unexpected memory update!"

end

(** Implementation of an evaluator with the random initialized memory model *)
module RandomEvaluator = Make(RandomInitializedMemoryLookup)(NullFormula)
module EspEvaluator = Make(EspInitializedMemoryLookup)(NullFormula)
(* vim: set ts=8 sw=2 tw=80 et : *)
