(**
    Unit tests for the ssa_ext_eval module.
    @author Remco Vermeulen
 *)

open OUnit
open Ssa_ext
open Ssa_ext_convenience
open Ssa_ext_eval

let arithmetic_identity_with_random_initialization op reverse_op identity =
        let evaluator = RandomEvaluator.create () in
        let x = Value.of_variable (Variable.create "x" reg_32) in
        let y = Value.of_variable (Variable.create "y" reg_32) in
        let z = Variable.create "z" reg_32 in
        let stmt = move z (Ssa_ext.Expression.BinOp (op,x,y)) in
        let _ = RandomEvaluator.eval_stmt evaluator stmt in
        let z' = Value.of_variable z in
        let stmt = move z ( Ssa_ext.Expression.BinOp (reverse_op, z', z')) in
        match RandomEvaluator.eval_stmt evaluator stmt with
        | [] -> failwith "Concrete execution didn't return a context!"
        | h::t when t <> [] -> failwith "Concrete execution returned multiple contexts!"
        | h::t -> let delta = h.delta in
                  assert_equal (identity, reg_32) (Hashtbl.find (fst !delta) z )

let plus_minus_identity_with_random_initialization () =
    arithmetic_identity_with_random_initialization Type.PLUS Type.MINUS
    Big_int_Z.zero_big_int

let times_divide_identity_with_random_initialization () =
    arithmetic_identity_with_random_initialization Type.TIMES Type.DIVIDE
    Big_int_Z.unit_big_int

let fixture = "Test Extended SSA Evaluation" >:::
[
    "Test plus/minus identity with random initialization" >::
        plus_minus_identity_with_random_initialization ;
    "Test times/divide identity with random initialization" >::
        times_divide_identity_with_random_initialization
]

let _ = run_test_tt_main fixture
