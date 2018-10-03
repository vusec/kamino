module D = Debug.Make(struct let name = "TF norm" and default=`Debug end)
open D

module L = Ssa_ext
module C = Ssa_ext_convenience
module Var = L.Variable
module Val = L.Value
module Exp = L.Expression
module T = Type
module R = Rewrite.Ssa_ext.ExpRule

module Helpers = struct
  let val_of_exp exp =
    let var = C.tmp_var_from_exp exp in
    C.Value.of_variable var

  let (~@) = val_of_exp

  let low v = Exp.Cast (T.CAST_LOW, T.Reg 8, Val.Var v)
  let extend v = Exp.Cast (T.CAST_SIGNED, T.Reg 32, v)
  let rshift v w = Exp.BinOp (T.RSHIFT, v, Val.Int (Big_int_convenience.biconst w, T.Reg 32))
end

let check_high_bit_in_lsb =
  let open Big_int_convenience in
  let open Helpers in
  R.create "check_high_bit_in_lsb"
    ~description:"Replace check of high bit in lsb with more idiomatic BIL using casts and shifts."
    (fun e -> match e with
    | Exp.BinOp (T.AND, Val.Var (Var.VarExp (_, Exp.BinOp
      (T.RSHIFT, Val.Var v, Val.Int (width, _)),_)), Val.Int (mask, _))
        when width ==% bi7 && mask ==% bi1 ->
       rshift ~@ (extend ~@ (low v)) 0x1f
    | _ -> e)

let adding_negative =
  let open Big_int_Z in
  let open Big_int_convenience in
  let open Helpers in
  R.create "adding_negative"
    ~description:"X + -Y -> X - Y"
    (function
    | Exp.BinOp (T.PLUS, v, Val.Var (Var.VarExp (_, Exp.UnOp
      (T.NEG, v'),_))) ->
       Exp.BinOp (T.MINUS, v, v')
    | Exp.BinOp (T.PLUS, v, Val.Int (i, t)) as e ->
       let i' = Arithmetic.to_sbig_int (i,t) in
       if i' <% bi0 then begin
         let abs = Arithmetic.to_big_int (abs_big_int i', t) in
         Exp.BinOp (T.MINUS, v, Val.Int(abs, t))
       end else e
    | _ as e -> e)

let left_assoc_minus_to_plus =
  let open Helpers in
  R.create "left_associative_minus_to_plus"
    ~description:"(X - Y) - Z -> X - (Y + Z)"
    (function
    | Exp.BinOp (T.MINUS,
                 Val.Var (Var.VarExp (_,
                                      Exp.BinOp (T.MINUS, x, y), _)), z) ->
       let sum = Exp.BinOp (T.PLUS, y, z) in
       Exp.BinOp (T.MINUS, x, ~@ sum)
    | _ as e -> e
    )

(* Yes, this actually happens despite SCCVN's efforts *)
let identity =
  let open Helpers in
  let open Big_int_convenience in
  R.create "identity"
    ~description:"e.g., X + 0 -> X"
    (function
    | Exp.BinOp (op, Val.Int (bi,t), Val.Int (bi',t')) ->
       let i,t = Arithmetic.binop op (bi,t) (bi',t') in
       Exp.Val (Val.Int (i,t))
    | Exp.BinOp (T.PLUS, Val.Int (bi, typ), value) when bi_is_zero bi -> Exp.Val value
    | Exp.BinOp (T.PLUS, value, Val.Int (bi, typ)) when bi_is_zero bi -> Exp.Val value
    | Exp.BinOp (T.MINUS, value, Val.Int (bi, _)) when bi_is_zero bi ->
       Exp.Val value
    | _ as e -> e)

let simplify_is_zero_padding =
  let open Helpers in
  let open Big_int_convenience in
  R.create "simplify 'is_zero' padding"
    ~description:"(== 0:t1 (pad t1 y:t2)) -> (== 0:t2 y)"
    (function
    | Exp.BinOp (T.EQ,
             Val.Var (Var.VarExp (_, (Exp.Cast (T.CAST_UNSIGNED, _, Val.Var v)), _)),
             Val.Int (bi, _))
    | Exp.BinOp (T.EQ,
             Val.Int (bi, _),
             Val.Var (Var.VarExp (_, (Exp.Cast (T.CAST_UNSIGNED, _, Val.Var v)), _)))
        when bi_is_zero bi ->
        Exp.BinOp (T.EQ, Val.Int (bi0, C.Variable.typ v), Val.Var v)
    | _ as e -> e)

let simplify_nested_is_zero =
  let open Helpers in
  let open Big_int_convenience in
  R.create "simplify nested 'is_zero'"
    ~description:"(== 0:u8 (== 0:t x)) -> not (== 0:t x)"
    (function
    | Exp.BinOp (T.EQ,
             Val.Int (bi1, T.Reg 8),
             Val.Var (Var.VarExp (_, e, _) as ve))
    | Exp.BinOp (T.EQ,
             Val.Var (Var.VarExp (_, e, _) as ve),
             Val.Int (bi1, T.Reg 8)) as exp
        when bi_is_zero bi1 ->
      begin
        match e with
        | Exp.BinOp (T.EQ,
                 Val.Int (bi2, t),
                 _)
        | Exp.BinOp (T.EQ,
                 _,
                 Val.Int (bi2, t))
            when bi_is_zero bi2 ->
          Exp.UnOp (T.NOT, Val.Var ve)
        | _ -> exp
      end
    | _ as e -> e
    )

let pointless_zero_extending =
  let open Helpers in
  let open Big_int_convenience in
  R.create "pointless zero extending"
    ~description:"(low:u8 (pad:u32 Load:u8)) -> Load:u8"
    (function
    | Exp.Cast (T.CAST_LOW, T.Reg 8, Val.Var (Var.VarExp (_, Exp.Cast
      (T.CAST_UNSIGNED, _, Val.Var (Var.VarExp(_, (Exp.Load(_,_,_,T.Reg 8,_)
        as ld),_))), _)))
      -> ld
    | _ as e -> e
    )

let pointless_concat =
  let open Helpers in
  let open Big_int_convenience in
  R.create "pointless concat"
    ~description:"(low:u8 (concat (extract 31 8 X:u32) (Y:u8))) -> Y:u8"
    (function
    | Exp.Cast (T.CAST_LOW,
                T.Reg 8,
                Val.Var (Var.VarExp (_, Exp.Concat (
                  Val.Var (Var.VarExp (_, Exp.Extract (h, l, _),_)),
                  Val.Var (Var.VarExp (_, e,_))
                ), _)) ) when h = (biconst 31) && l = bi8 ->
       e
    | _ as e -> e
    )

let unpack_varexp =
  R.create "unpack varexps"
    ~description:"Unpack inner expression"
    (function
    | Exp.Val (Val.Var (Var.VarExp (_, e, _))) -> e
    | _ as e -> e
    )

let unpack_val =
  R.create "unpack val"
    ~description:"Unpack inner vals"
    (function
    | Exp.BinOp (op, Val.Var (Var.VarExp (_,Exp.Val v, _)), v' )
    | Exp.BinOp (op, v, Val.Var (Var.VarExp (_,Exp.Val v', _)) ) ->
       Exp.BinOp (op, v, v')
    | Exp.UnOp (op, Val.Var (Var.VarExp (_,Exp.Val v,_))) ->
       Exp.UnOp (op, v)
    | _ as e -> e
    )

let pointless_low =
  let open Helpers in
  let open Big_int_convenience in
  R.create "pointless low"
    ~description:"(low:u8 X:u8) -> X:u8"
    (function
    | Exp.Cast (T.CAST_LOW,
                T.Reg 8,
                Val.Var (
                  Var.VarExp (_,(Exp.BinOp (T.EQ, Val.Int (_,T.Reg 8), _) as e),_))) -> e
    | _ as e -> e
    )

let norm_subtract_then_zero_compare =
  let open Big_int_convenience in
  R.create "subtract then zero compare"
    ~description:"(0:uX == (A:uX - B:uX) -> A:uX == B:uX"
    (function
      | Exp.BinOp (T.EQ,
                   Val.Int (bi, int_type),
                   Val.Var (Var.VarExp (_, Exp.BinOp (T.MINUS, a, b), _)))
      | Exp.BinOp (T.EQ,
                   Val.Var (Var.VarExp (_, Exp.BinOp (T.MINUS, a, b), _)),
                   Val.Int (bi, int_type)) when bi ==% bi0 ->
        (* Convert to EQ, which is commutative *)
        Exp.BinOp (T.EQ, a, b)
      | _ as e -> e)

let norm_xor_minus_one =
  R.create "xor with -1"
    ~description:"(a:X ^ -1:X) -> ~a"
    (function
      | Exp.BinOp (T.XOR,
                   Val.Int (bi, int_type),
                   Val.Var var)
      | Exp.BinOp (T.XOR,
                   Val.Var var,
                   Val.Int (bi, int_type))
        when Misc.type_width_equal
            (Ssa_ext_convenience.Variable.typ var) int_type ->
        Exp.UnOp (T.NOT, Val.Var var)
      | _ as e -> e)

let norm_low_then_pad =
  R.create "low then pad"
    ~description:"pad uY (low:uX a:uY) -> a:uY & (-i:bits(uY))"
    (function
    | Exp.Cast
        (T.CAST_UNSIGNED,
         T.Reg large_bits,
         Val.Var (
           Var.VarExp (_,
                       Exp.Cast (T.CAST_LOW, T.Reg small_bits, value),
                       _)
         )
        ) when small_bits <= large_bits ->
      let open Big_int_convenience in
      let ones = (bi1 <<% small_bits) -% bi1 in
      Exp.BinOp (T.AND,
                 value,
                 Val.Int (ones, T.Reg large_bits))
    | e -> e)

let all = [
  unpack_varexp;
  unpack_val;
  check_high_bit_in_lsb;
  adding_negative;
  left_assoc_minus_to_plus;
  identity;
  simplify_is_zero_padding;
  simplify_nested_is_zero;
  pointless_zero_extending;
  pointless_concat;
  pointless_low;
  norm_subtract_then_zero_compare;
  norm_xor_minus_one;
  norm_low_then_pad;
]

let normalize exp = Rewrite.Ssa_ext_exp_rewriter.rewrite all exp
