module D = Debug.Make(struct let name = "Prde_test" and default=`Debug end)
open D

open Mock.Definitions
open Mock.Helpers

let label_map ast_cfg str =
  snd (Mock.Helpers.label_map ast_cfg str)

let simple_ite_no_prd =
  let prog = new Mock.mock_program "prog" in
  let funcs =
    [
    object
      inherit Mock.mock_func prog "func"
      method cfg =
        let stmts_entry = List.concat [
          [Ast.Label (Type.Name "entry", []);];
          gen_prologue 4;
          [
          Ast.Move (eax, Ast.Load (Ast.Var mem,
                                   Ast.BinOp(Type.PLUS, Ast.Var ebp, imm4),
                                   Ast.exp_false, Type.Reg 32), []);
          Ast.Move (ebx, Ast.Load (Ast.Var mem,
                                   Ast.BinOp(Type.PLUS, Ast.Var ebp, imm8),
                                   Ast.exp_false, Type.Reg 32), []);
          Ast.Move(zf, Ast.BinOp(Type.EQ, Ast.Var ebx, imm1), []);
          Ast.CJmp(Ast.BinOp(Type.EQ, Ast.Var zf, flag0), Ast.Lab "bbl",
                  Ast.Lab "bbr", []);
          ]
        ] in
        let stmts_bbl = [
          Ast.Label (Type.Name "bbl", []);
          Ast.Move (ecx, Ast.BinOp(Type.PLUS, Ast.Var eax, imm1), []);
          Ast.Jmp (Ast.Lab "done", []);
        ] in
        let stmts_bbr = [
          Ast.Label (Type.Name "bbr", []);
          Ast.Move (ecx, imm1, []);
          Ast.Jmp (Ast.Lab "done", []);
        ] in
        let stmts_done = List.concat [
          [
            Ast.Label (Type.Name "done", []);
            Ast.Move (eax, Ast.Var ecx, []);
          ];
          gen_retn 4;
        ]
        in
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
        Graph_dump.output_ssa stderr cfg;
        if Cfg.SSA.G.nb_vertex cfg <> 4 then
          failwith "Unexpected number of BB, which means incorrect prde!"
    end;
    ] in
object
  method name = "simple_ite_no_prd"
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
         (* Catch when the test function is marked confusing! *)
         if fsym <> "" then
          failwith (Printf.sprintf "Whoops, cannot find function %s"
                      fsym)
            else ()
      | Some mfunc ->
         let cfg =
           try
             BatOption.get (Function_info.ssacfg fi)
           with Not_found ->
             failwith "Whaaa? No ssacfg?"
         in
         mfunc#verify cfg) cg
end

let simple_ite =
  let prog = new Mock.mock_program "prog" in
  let funcs =
    [
    object
      inherit Mock.mock_func prog "func"
      method cfg =
        let stmts_entry = List.concat [
          [Ast.Label (Type.Name "entry", []);];
          gen_prologue 4;
          [
          (* Use a binop to circumvent SCCVN *)
          Ast.Move (eax, Ast.BinOp(Type.PLUS, Ast.Var ecx, Ast.Var edx), []);
          Ast.Move (ebx, Ast.Load (Ast.Var mem,
                                   Ast.BinOp(Type.PLUS, Ast.Var ebp, imm8),
                                   Ast.exp_false, Type.Reg 32), []);
          Ast.Move(zf, Ast.BinOp(Type.EQ, Ast.Var ebx, imm1), []);
          Ast.CJmp(Ast.BinOp(Type.EQ, Ast.Var zf, flag0), Ast.Lab "bbl",
                  Ast.Lab "bbr", []);
          ]
        ] in
        let stmts_bbl = [
          Ast.Label (Type.Name "bbl", []);
          Ast.Move (ecx, Ast.BinOp(Type.PLUS, Ast.Var eax, imm1), []);
          Ast.Jmp (Ast.Lab "done", []);
        ] in
        let stmts_bbr = [
          Ast.Label (Type.Name "bbr", []);
          Ast.Move (ecx, imm1, []);
          Ast.Jmp (Ast.Lab "done", []);
        ] in
        let stmts_done = List.concat [
          [
            Ast.Label (Type.Name "done", []);
            Ast.Move (eax, Ast.Var ecx, []);
          ];
          gen_retn 4;
        ]
        in
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
        Graph_dump.output_ssa stderr cfg;
        let entry = Cfg.SSA.find_vertex cfg Cfg.BB_Entry in
        List.iter (fun succ_e ->
          if Cfg.SSA.G.E.label succ_e = (Some true) then begin
            let dst = Cfg.SSA.G.E.dst succ_e in
            let succs = Cfg.SSA.G.succ cfg dst in
            if List.length succs = 1 then begin
              let stmts = Cfg.SSA.get_stmts cfg dst in
              List.iter (fun stmt ->
                match stmt with
                | Ssa.Label _ -> ()
                | Ssa.Move (var, _,_) when (Var.name var = "R_EAX") -> ()
                | _ -> failwith
                   (Printf.sprintf "Unexpected stmt %s as redundant definition!" (Pp.ssa_stmt_to_string stmt))
              ) stmts;
            end else
              failwith "Expected a fall-through BB containing the redundant definition!"
          end
        ) (Cfg.SSA.G.succ_e cfg entry)
    end;
    ] in
object
  method name = "simple_ite"
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
         (* Catch when the test function is marked confusing! *)
         if fsym <> "" then
          failwith (Printf.sprintf "Whoops, cannot find function %s"
                      fsym)
            else ()
      | Some mfunc ->
         let cfg =
           try
             BatOption.get (Function_info.ssacfg fi)
           with Not_found ->
             failwith "Whaaa? No ssacfg?"
         in
         mfunc#verify cfg) cg
end

let testcases = [
  simple_ite_no_prd;
  simple_ite;
]

(* Umm, why is this duplicated here? XXX *)
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
  let state, cg = Summarizer.handle_ast_callgraph Asmir.arch_i386
  ~keypref cg in
  let state, cg = Summarizer.handle_astcfg_callgraph state ~keypref cg
  in
  let _, cg = process_ssa_pipeline
    (* TBD: Dumping should be made conditional on a cli option *)
    ~func_filter:(fun _ -> true) ~keypref state cg
    (List.map make_pass [
        `StartSsa;
        `ComputeDataDependencies;
        `NormalizeCjmps;
	`BapSsaSimplifications1;
        `SimplifySsaCfg;
        `ComputeDataDependencies;
        `ComputeFunctionInputs;
        `RewriteLoadStores;
	`BapSsaSimplifications2;
        (* Recalculate data dependencies, RewriteLoadStores changes definitions *)
        `ComputeDataDependencies;
        `ComputeCollapsibleLoads;
        `RemoveNoreturnEdges; (* needs to come before MarkEaxLiveout *)
	`MarkEaxLiveout;
	`PhiPropagationPass;
        `MarkStoresLiveout; (* needs to come before DeadCodeElimination *)
        (* XXX: DCE & BB_Error don't play well together *)
	`DeadCodeElimination;
        `PartialRedundantDefinitionElimination;
      ]) in
  tc#verify cg;
  dprintf "END TEST: %s %s1" tc#name Print.fc

let () =
  Printexc.record_backtrace true;
  Embarassingly_parallel.set_debug true;
  Outdir.set_outdir "deleteme-prde-test";
  List.iter run_testcase testcases
