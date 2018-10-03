module D = Debug.Make(struct let name = "Reachable_loads_test" and default=`Debug end)
open D

open Mock.Definitions
open Mock.Helpers

let label_map ast_cfg str =
  snd (Mock.Helpers.label_map ast_cfg str)

let simple_test =
  let prog = new Mock.mock_program "prog" in
  let funcs = [
  object
    inherit Mock.mock_func prog "f1"
    val prologue_bytes = 8
    method cfg =
      let stmts_entry = List.concat [
        gen_prologue prologue_bytes;
        push_int (7, 4);
        [
          Ast.Label (Type.Name "entry", []);
          Ast.Move (eax, Ast.Load (Ast.Var mem, Ast.Var esp, Ast.exp_false,
                                   Type.Reg 32), []);
          Ast.Move(zf, Ast.BinOp(Type.EQ, Ast.Var eax, imm0), []);
          Ast.CJmp(Ast.BinOp(Type.EQ, Ast.Var zf, flag0), Ast.Lab "bbl",
                  Ast.Lab "bbr", []);
        ];
      ] in
      let stmts_bbl = List.concat [
        [
          Ast.Label (Type.Name "bbl", []);
          Ast.Label (Type.Name "bbl_before_loads", []);
          Ast.Move (eax, Ast.Load (Ast.Var mem, Ast.Var esp, Ast.exp_false,
                                   Type.Reg 32), []);
          Ast.Label (Type.Name "bbl_in_between_loads", []);
          Ast.Move (ecx, Ast.Load (Ast.Var mem, Ast.Var eax, Ast.exp_false,
                                   Type.Reg 32), []);
          Ast.Label (Type.Name "bbl_after_loads", []);
          Ast.Move (ecx, Ast.BinOp (Type.PLUS, Ast.Var ecx, Ast.Var eax), []);
          Ast.Jmp (Ast.Lab "done", []);
        ];
      ] in
      let global1 = Ast.Int (Big_int_Z.big_int_of_int 0x987654, Type.Reg 32) in
      let stmts_bbr = List.concat [
        [
          Ast.Label (Type.Name "bbr", []);
          Ast.Move (eax, Ast.Load (Ast.Var mem, global1, Ast.exp_false,
                                   Type.Reg 32), []);
          Ast.Move (ecx, Ast.Load (Ast.Var mem, Ast.Var eax, Ast.exp_false,
                                   Type.Reg 32), []);
          Ast.Move (ecx, Ast.BinOp (Type.PLUS, Ast.Var ecx, Ast.Var eax), []);
          Ast.Jmp (Ast.Lab "done", []);
        ];
      ] in
      let stmts_done = [
        Ast.Label (Type.Name "done", []);
        (* Make sure the BB isn't empty, so we have an address *)
        Ast.Move (eax, Ast.Var ecx, []);
      ] in
      let module C = Cfg.AST in
      let open Open_cfg_ast in
      let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
      let g = C.set_stmts g entry stmts_entry in
      let (g, bbl) = C.create_vertex g stmts_bbl in
      let (g, bbr) = C.create_vertex g stmts_bbr in
      let (g, bbdone) = C.create_vertex g stmts_done in
      let g = C.add_edge_e g (C.G.E.create entry (Some true) bbl) in
      let g = C.add_edge_e g (C.G.E.create entry (Some false) bbr) in
      let g = C.add_edge_e g (C.G.E.create bbl None bbdone) in
      let g = C.add_edge_e g (C.G.E.create bbr None bbdone) in
      g
    method verify cfg =
      let bb_rloads_in = Side_effect.compute_reachable_loads cfg in
      (*
       * XXX: this should be actually looking at the returned loads,
       * not just counting them.
       *)
      let expected = [
        ("entry", 5);
        ("bbl_before_loads", 2);
        ("bbl_in_between_loads", 1);
        ("bbl_after_loads", 0);
      ] in
      let labmap = label_map cfg in
      List.iter (fun (lab, exp_len) ->
        let (bbid, offset) = labmap lab in
        let rloads = Side_effect.reachable_loads_at bb_rloads_in cfg bbid offset in
        let str = Side_effect.reachable_load_set_to_string rloads in
        dprintf "Reachable loads at %s: %s" lab str;
        let nloads = Side_effect.Reachable_load_set.cardinal rloads in
        if  nloads <> exp_len then begin
          Printf.eprintf "Expected %d reachable loads, but got %d"
            exp_len nloads
        end
      ) expected;
  end;
  ] in
object
  method name = "simple_test"
  method program = prog
  method verify cg =
    let is_sym sym mf =
      String.compare mf#name sym = 0
    in
    Callgraph.Callgraph.iter_vertex (fun fi ->
      let syms = Function_info.symbols fi in
      let fsym = match syms with
        | [sym] -> sym
        | [] -> "" (* Normally, Indirect *)
        | _ ->
          let str = Printf.sprintf "Expected exactly one symbol, got %s"
              (Function_info.symbols_to_str fi)
          in
          failwith str
      in
      match BatList.Exceptionless.find (is_sym fsym) funcs with
      | None ->
        ()
      | Some mfunc ->
        let cfg =
          try
            BatOption.get (Function_info.astcfg fi)
          with Not_found ->
            failwith "Whaaa? No astcfg?"
        in
        mfunc#verify cfg) cg
end

let testcases = [
  simple_test;
]

let run_testcase tc =
  dprintf "START TEST: %s %s1" tc#name Print.fo;
  let prog = tc#program in
  dprintf "got program";
  let cg = prog#cg in
  dprintf "got cg";
  let open Analysis_pass in
  let open Bb_cluster in
  (*
   * TBD: don't care, not used, export the functions we need
   * outside the functor.
   *)
  let classifier = "ByFunc" in
  let module BBMgr = (val (Bb_cluster.bbclustermanagerfactory classifier) : BBClusterManagerSig) in
  let module Summarizer = Summary.Algo in
  let keypref = Some tc#name in
  dprintf "About to handle_ast_cg";
  let (state, cg) = Summarizer.handle_ast_callgraph Asmir.arch_i386 ~keypref cg in
  dprintf "About to handle_astcfg_cg";
  let (_, cg) = Summarizer.handle_astcfg_callgraph state ~keypref cg in
  tc#verify cg;
  dprintf "END TEST: %s %s1" tc#name Print.fc

let () =  
  Printexc.record_backtrace true;
  Embarassingly_parallel.set_debug true;
  Outdir.set_outdir "deleteme-reachable-loads-test";
  List.iter run_testcase testcases
