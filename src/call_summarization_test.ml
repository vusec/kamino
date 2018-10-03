module D = Debug.Make(struct let name = "Call_summarization_test" and default=`Debug end)
open D

open Mock.Definitions
open Mock.Helpers

(* dump (Function_info, Function_summary) pairs *)
let dump_func_summaries =
  let dump (fi, sum) =
    let fname = Function_info.name fi in
    let sexp = Side_effect.Function_summary.sexp_of_t sum in
    dprintf "summary(%s): %s" fname(Sexplib.Sexp.to_string_hum sexp)
  in
  List.iter dump

let strcmp = Misc.strcmp "summary"

let compare_summaries ~calculated ~desired =
  let compare_for (this_name, this_sum) =
    try
      let stringize sum =
        let open Sexplib in
        let sexp = Side_effect.Function_summary.sexp_of_t sum in
        (* drop the name *)
        let sexp = match sexp with
          | Sexp.Atom _
          | Sexp.List [] ->
            failwith "unexpected sexp"
          | Sexp.List (_::tail) ->
            Sexp.List tail
        in
        Sexp.to_string_hum sexp
      in
      let _, calced_sum = List.find (fun (fi, sum) ->
        let fname = Function_info.name fi in
        String.compare fname this_name = 0) calculated
      in
      let this_str = stringize this_sum in
      let calced_str = stringize calced_sum in
      match strcmp ~expected:this_str ~got:calced_str with
      | BatResult.Ok () as ok ->
        dprintf "Verified summary for %s" this_name;
        ok
      | BatResult.Bad _ as bad ->
        dprintf "Failed to verify summary for %s" this_name;
        bad
    with Not_found ->
      dprintf "No calculated summary for %s!" this_name;
      failwith "Something went terribly wrong"
  in
  List.fold_left
    (fun acc p -> BatResult.bind acc (fun () -> compare_for p))
      (BatResult.Ok ()) desired

let simple_test =
  let simple_prog = new Mock.mock_program "simple_prog" in
  ignore(object
    inherit Mock.mock_func simple_prog "f0"
    method cfg =
      let local_bytes = 0 in
      let stmts = [
        gen_prologue local_bytes;
        gen_call "f1";
        gen_call "f4";
        [Ast.Move(eax, imm0, [])];
        gen_retn local_bytes;
      ] in
      let stmts = List.concat stmts in
      Mock.build_single_bb_graph stmts
  end);

  ignore(object
    inherit Mock.mock_func simple_prog "f1"
    method cfg =
      let local_bytes = 4 in
      let prologue = gen_prologue local_bytes in
      let stmts = [
        (* push $1 *)
        [
          Ast.Move (esp, Ast.BinOp (Type.MINUS, Ast.Var esp, imm4), []);
          Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm1, Ast.exp_false,
                                  Type.Reg 32), []);
        ];
        gen_call "f2";
        gen_call "f3";
        (* add $4, %esp ; cleanup arguments of the call *)
        [
          Ast.Move (esp, Ast.BinOp (Type.PLUS, Ast.Var esp, imm4), []);
          Ast.Move(eax, imm0, []);
        ];
      ] in
      let stmts = List.concat stmts in
      let epilogue = gen_retn local_bytes in
      let stmts = prologue @ stmts @ epilogue in
      Mock.build_single_bb_graph stmts
  end);

  ignore(object
    inherit Mock.mock_func simple_prog "f2"
    method cfg =
      let local_bytes = 0 in
      let temp = Disasm_temp.nt "t" Ast.reg_32 in
      let stmts = [
        gen_prologue local_bytes;
        [
          Ast.Move(mem, Ast.Store (Ast.Var mem,
                                   Ast.Int (Big_int_Z.big_int_of_int 0x7f, Type.Reg 32),
                                   imm4,
                                   Ast.exp_false,
                                   Type.Reg 32), [];);
          Ast.Move(mem, Ast.Store (Ast.Var mem,
                                   Ast.Int (Big_int_Z.big_int_of_int 0x10, Type.Reg 32),
                                   imm4,
                                   Ast.exp_false,
                                   Type.Reg 32), [];);
          Ast.Move(temp, Ast.BinOp (Type.PLUS, Ast.Var esp, imm4), []);
          Ast.Move(eax, Ast.Load (Ast.Var mem, Ast.Var temp, Ast.exp_false,
                                  Type.Reg 32), [];);
        ];
        gen_retn local_bytes;
      ] in
      let stmts = List.concat stmts in
      Mock.build_single_bb_graph stmts
  end);
  ignore(object
    inherit Mock.mock_func simple_prog "f3"
    method cfg =
      let local_bytes = 0 in
      let temp = Disasm_temp.nt "t" Ast.reg_32 in
      let stmts = [
        gen_prologue local_bytes;
        [
          Ast.Move(temp, Ast.BinOp (Type.PLUS, Ast.Var esp, imm4), []);
          Ast.Move(mem, Ast.Store (Ast.Var mem,
                                   Ast.Int (Big_int_Z.big_int_of_int 0x7f, Type.Reg 32),
                                   imm4,
                                   Ast.exp_false,
                                   Type.Reg 32), [];);
          Ast.Move(eax, Ast.Load (Ast.Var mem, Ast.Var temp, Ast.exp_false,
                                  Type.Reg 32), [];);
        ];
        gen_retn local_bytes;
      ] in
      let stmts = List.concat stmts in
      Mock.build_single_bb_graph stmts
  end);

  ignore(object
    inherit Mock.mock_func simple_prog "f4"
    method cfg =
      let local_bytes = 0 in
      let stmts = [
        gen_prologue local_bytes;
        [Ast.Move (mem, Ast.Store (Ast.Var mem, Ast.Var ecx, imm0,
                                   Ast.exp_false, Type.Reg 32), [])];
        gen_retn local_bytes;
      ] in
      let stmts = List.concat stmts in
      Mock.build_single_bb_graph stmts
  end);
object
  method name = "simple_test"
  method program = simple_prog
  method verify summaries =
    let desired =
      let open Side_effect.Function_summary in
      let open Interval in
      [
        ("f0", {
          name = "f0";
          killlist = [
            KillAllStoresAndGlobals;
            KillReg eax;
            KillReg ecx;
            KillReg edx;
          ];});
        ("f1", {
          name = "f1";
          killlist = [
            KillGlobal (Address_interval.create (Int64.of_int 0x7f)
                          (Int64.of_int (0x7f + 3)));
            (* XXX: what's up with this CDECL assumption? *)
            KillReg eax;
            KillReg ecx;
            KillReg edx;
            KillGlobal (Address_interval.create (Int64.of_int 0x10)
                          (Int64.of_int (0x10 + 3)));
          ];});
        ("f2", {
          name = "f2";
          killlist = [
            KillGlobal (Address_interval.create (Int64.of_int 0x7f)
                          (Int64.of_int (0x7f + 3)));
            KillReg eax;
            KillReg ecx;
            KillReg edx;
            KillGlobal (Address_interval.create (Int64.of_int 0x10)
                          (Int64.of_int (0x10 + 3)));
          ];});
        ("f3", {
          name = "f3";
          killlist = [
            KillGlobal (Address_interval.create (Int64.of_int 0x7f)
                          (Int64.of_int (0x7f + 3)));
            KillReg eax;
            KillReg ecx;
            KillReg edx;
          ];});
        ("f4", {
          name = "f4";
          killlist = [
            KillAllStoresAndGlobals;
            KillReg eax;
            KillReg ecx;
            KillReg edx;
          ];});
      ]
    in
    match compare_summaries ~calculated:summaries ~desired with
    | BatResult.Ok () -> ()
    | BatResult.Bad diff ->
      dprintf "Summaries differ:\n%s" diff;
      failwith "Incorrect summaries"
end

let testcases = [simple_test]

let run_testcase tc =
  dprintf "START TEST: %s %s1" tc#name Print.fo;
  let prog = tc#program in
  let cg = prog#cg in
  let open Analysis_pass in
  let open Bb_cluster in
  (*
   * TBD: don't care, not used, export the functions we need
   * outside the functor.
   *)
  let classifier = "ByFunc" in
  let module BBMgr = (val (Bb_cluster.bbclustermanagerfactory classifier) : BBClusterManagerSig) in
  let module Summarizer = Summary.Algo in
  let keypref = Some "call_summarization" in
  let (state, cg) = Summarizer.handle_ast_callgraph Asmir.arch_i386 ~keypref cg in
  let (_, cg) = Summarizer.handle_astcfg_callgraph state ~keypref cg in
  let cg, calc_summary = Side_effect.calculate_function_summaries cg in
  let func_summaries = Analysis_pass.fold_vertex (fun fi acc ->
    dprintf "about to calc_summary for %s" (Function_info.name fi);
    let sum = calc_summary fi in
    (fi, sum) :: acc) cg []
  in
  dprintf "Final callgraph:";
  Callgraph.dump_call_graph cg stdout;
  tc#verify func_summaries;
  dprintf "END TEST: %s %s1" tc#name Print.fc;
  ()

let () =
  Printexc.record_backtrace true;
  Outdir.set_outdir "deleteme-call-summarization";
  List.iter run_testcase testcases

