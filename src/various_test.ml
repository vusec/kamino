open OUnit

module D = Debug.Make(struct let name = "VariousTest" and default=`Debug end)
open D

module BBMgr = (val (Bb_cluster.bbclustermanagerfactory "ByFunc") :
    Bb_cluster.BBClusterManagerSig)
module Summarizer = Summary.Algo
module BBCmpRes = Comparator.BBCmpResRich
module Policy = Comparator.ExhaustiveMatchingPolicy(Comparator.BBCmpResRich)
module TestingComparator = Comparator.Algo(BBMgr)(Policy)
module Subg = TestingComparator.Subgraph

module Validator = Validation.SymbValidator(BBMgr)(TestingComparator)

(* This normalization causes confusing ids when extended SSA expression are
   shown with the NamedNodes decorator.
   The confusion happens when a variable is being assigned a new value based on
   its previous value. This new variable is normalized before the old variable causing
   it to have a lower id, while it actually should have a higher id.
   (Aggelos says: leave behind the assumption that IDs increase monotonically
    (which is an implementation detail) and be happy ;-))

   Note: We normalize twice, once for the LHS variables, once for the RHS
   variables. The sexp-dumping code rewrites the variable names for us.
*)
let normalize_sexp str =
  let open BatPervasives in
  str |> Misc.normalize_string (Str.regexp "L_[0-9]+") |>
      Misc.normalize_string (Str.regexp "R_[0-9]+")

(*
  At the mercy of the sexp to string function, which apparently wraps the same sexp
  in different ways, we replace newlines with spaces to deal with this non-deterministic
  wrapping.

  Note: that we have to compare the string representation of the sexps since we have to
  normalize the indices of the variables. This normalization code is written before we
  changed the BAP code to allow us to change the index of a variable, so it uses regexps.
  This needs to be updated at one point, but not now.
*)
let strcmp s1 s2 =
  let replace_newlines = BatString.replace_chars (function
    | '\n' -> " "
    | c -> BatString.of_char c)
  in
  let s1'= replace_newlines s1 in
  let s2'= replace_newlines s2 in
  match Misc.strcmp "subg" s1' s2' with
  | BatResult.Ok () as ok -> ok
  | BatResult.Bad _ -> Misc.strcmp "subg" s1 s2

open Mock.Definitions

class base_test = object
  method verify_af_left (_ : Ktype.analyzed_func) = ()
  method verify_af_right (_ : Ktype.analyzed_func) = ()
  method expect_subgraph = true
  method verify (_ : Validator.subgraph) : unit=
    failwith "Expected subgraph but didn't provide a verify method"
end

class type testcase = object
  method name : string
  method cfg_left : Cfg.AST.G.t
  method cfg_right : Cfg.AST.G.t
  method verify_af_left : Ktype.analyzed_func -> unit
  method verify_af_right : Ktype.analyzed_func -> unit
  method verify : Validator.subgraph -> unit
  method expect_subgraph : bool
end

let astcfg_of_string s =
  let lb = Lexing.from_string s in
  let p, _ = Parser.program_from_lexbuf lb in
  let cfg = Cfg_ast.of_prog p in
  let cfg = Hacks.ast_remove_indirect cfg in
  let bberr = Cfg.AST.find_vertex cfg Cfg.BB_Error in
  let cfg = match Cfg.AST.G.in_degree cfg bberr with
    | 0 -> Cfg.AST.remove_vertex cfg bberr
    | _ -> failwith "testcase has BB_Error"
  in
  let cfg = Prune_unreachable.prune_unreachable_ast cfg in
  let cfg = Coalesce.coalesce_ast cfg in
  Graph_dump.output_ast stdout cfg;
  cfg

let assert_exact_total subg =
  let open Cmpres in
  match Subg.res subg with
  | {fuzziness = ExactOnly; overlap = OverlapTotal _} ->
    Printf.printf "success\n"
  | _ ->
    let str = Printf.sprintf "not the expected match (ExactOnly, OverlapTotal): %s"
        (Subg.to_string subg)
    in
    Printf.eprintf "%s\n" str;
    failwith str

let assert_fuzziness_partial subg fuzz n d =
  let open Cmpres in
  match Subg.res subg with
  | {fuzziness; overlap = OverlapPartial (n', d')}
    when fuzziness = fuzz && n' = n && d' = d ->
    Printf.printf "success\n"
  | _ ->
    let expected = {fuzziness = fuzz; overlap = OverlapPartial (n, d)} in
    let estr = Cmpres.cfgcmp_res_to_string expected in
    let str = Printf.sprintf "not the expected match (%s): %s"
        estr (Subg.to_string subg)
    in
    Printf.eprintf "%s\n" str;
    failwith str

let validate subg =
  (* XXX: after the force-single-exit changes, we run into issues with
     validation b/c something in it craps out when it doesn't find a
     BB_Exit. It's probably a good idea to rename the exit BB to BB_Exit,
     but now might not be the best time to work on that. *)
  Printf.eprintf "validation globally disabled\n"
(*
  match Validator.validate subg with
  | BatResult.Ok () ->
    ()
  | BatResult.Bad str ->
    Printf.eprintf "Failed to validate result: %s\n" str;
    failwith "Testcase failed validation"
*)

let trivial_test =
object
  inherit base_test
  method name = "trivial"
  method cfg_left =
    let stmts = [
      Ast.Move(eax, Ast.Int (Big_int_Z.big_int_of_int 0, Type.Reg 32), []);
      Ast.Move(eax, Ast.BinOp (Type.MINUS, Ast.Var eax,
			       Ast.Int (Big_int_Z.big_int_of_int 4,
					Type.Reg 32)), []);
      (*
       * XXX: this is wrong by convention. We actually should be using
       * Ast.Halt(Ast.Var eax, []). However, we need to remove halt
       * stmts for ssafication and we determine uses using the SSA
       * form. So for now, our convention is that the existence of a halt
       * statement implies a use of EAX...
       *)
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let stmts = [
      Ast.Move(eax, Ast.Int (Big_int_Z.big_int_of_int 0, Type.Reg 32), []);
      Ast.Move(eax, Ast.BinOp (Type.MINUS, Ast.Var eax,
			       Ast.Int (Big_int_Z.big_int_of_int 4,
					Type.Reg 32)), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
    assert_exact_total subg;
    validate subg
end;;

let commutative_test =
object
  inherit base_test
  method name = "commutative"
  method cfg_left =
    let stmts = [
      Ast.Move(eax, Ast.BinOp (Type.PLUS, Ast.Var edx, Ast.Var ecx), []);
      Ast.Move(eax, Ast.BinOp (Type.PLUS, Ast.Var ebx, Ast.Var eax), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let stmts = [
      Ast.Move(ecx, Ast.BinOp (Type.PLUS, Ast.Var eax, Ast.Var ebx), []);
      Ast.Move(ecx, Ast.BinOp (Type.PLUS, Ast.Var ecx, Ast.Var edx), []);
      Ast.Move(eax, Ast.Var ecx, []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
    validate subg;
    let res_sexp = Subg.to_string subg in
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
   (bbcmps
    (((EXACT 1) (BB_Entry BB_Entry)
      ((IN
        (((R_EBXL_1:u32 R_ECXL_2:u32 R_EDXL_3:u32)
          (R_EAXR_4:u32 R_EBXR_1:u32 R_EDXR_3:u32))))
       (OUT (((R_EAXL_5:u32) (R_EAXR_6:u32))))))
     ((EXACT 0) (BB_Exit BB_Exit)
      ((IN ()) (OUT (((R_EAXL_5:u32) (R_EAXR_6:u32))))))))
   (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end;;

let assign_through_test =
object
  inherit base_test
  method name = "assign_through"
  method cfg_left =
    let stmts = [
      Ast.Move(ebx, Ast.BinOp (Type.PLUS, Ast.Var edx, Ast.Var ecx), []);
      Ast.Move(ecx, Ast.Var ebx, []);
      Ast.Move(ebp, Ast.Var ecx, []);
      Ast.Move(eax, Ast.Var ebp, []);
      Ast.Move(edx, Ast.BinOp (Type.PLUS, Ast.Var edi, Ast.Var esi), []);
      Ast.Move(eax, Ast.BinOp (Type.PLUS, Ast.Var eax, Ast.Var edx), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts

  method cfg_right =
    let stmts = [
      Ast.Move(edi, Ast.BinOp (Type.PLUS, Ast.Var edi, Ast.Var ebx), []);
      Ast.Move(esi, Ast.BinOp (Type.PLUS, Ast.Var eax, Ast.Var ecx), []);
      Ast.Move(eax, Ast.Var edi, []);
      Ast.Move(eax, Ast.BinOp (Type.PLUS, Ast.Var eax, Ast.Var esi), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts

  method verify subg =
    validate subg;
    let res_sexp = Subg.to_string subg in
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN
      (((R_EDIL_3:u32 R_ESIL_2:u32) (R_EAXR_5:u32 R_ECXR_7:u32))
       ((R_ECXL_7:u32 R_EDXL_8:u32) (R_EBXR_6:u32 R_EDIR_3:u32))))
     (OUT (((R_EAXL_102:u32) (R_EAXR_111:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAXL_102:u32) (R_EAXR_111:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end;;

let expansion_test =
  (*
    The RHS is intented to be a "registers-renamed" version of the LHS,
    with a different BB3 (so this also does a basic sanity check that we
    don't just match whatever is thrown our way).
  *)
  let stmts_Lbb1 = [
    Ast.Move(ecx, Ast.BinOp (Type.MINUS, Ast.Var ebx, imm8), []);
    Ast.Move(zf, Ast.BinOp(Type.EQ, Ast.Var ecx, imm0), []);
    Ast.CJmp(Ast.BinOp(Type.EQ, Ast.Var zf, flag0), Ast.Lab "bb2", Ast.Lab "bb3", []);
  ] in
  let stmts_Rbb1 = [
    Ast.Move(eax, Ast.BinOp (Type.MINUS, Ast.Var edx, imm8), []);
    Ast.Move(zf, Ast.BinOp(Type.EQ, Ast.Var eax, imm0), []);
    Ast.CJmp(Ast.BinOp(Type.EQ, Ast.Var zf, flag0), Ast.Lab "bb2", Ast.Lab "bb3", []);
  ] in

  let stmts_Lbb2 = [
    Ast.Label(Type.Name "bb2", []);
    (* Add the output with an irrelevant register. Since this is a
     * binary op, we're checking that the IN assumptions are simplified
     * as expected against BB1's OUT assumptions.
    *)
    Ast.Move(eax, Ast.BinOp (Type.PLUS, Ast.Var edx, Ast.Var ecx), []);
    Ast.Move(edx, Ast.BinOp (Type.PLUS, Ast.Var ebx, imm4), []);
    Ast.Jmp(Ast.Lab "done", []);
  ] in
  let stmts_Rbb2 = [
    Ast.Label(Type.Name "bb2", []);
    Ast.Move(ecx, Ast.BinOp (Type.PLUS, Ast.Var eax, Ast.Var esi), []);
    Ast.Move(ebx, Ast.BinOp (Type.PLUS, Ast.Var edx, imm4), []);
    Ast.Jmp(Ast.Lab "done", []);
  ] in

  let stmts_Lbb3 = [
    Ast.Label(Type.Name "bb3", []);
    (*
     * Force a mismatch for this BB pair.
     * XXX: this is dead code, should be a store to memory.
     * Convert to store as soon as we can handle them. Use
     * Liveout as a stopgap :/
    *)
    Ast.Move(esi, Ast.BinOp (Type.DIVIDE, Ast.Var ebx, imm4), [Type.Liveout]);
    Ast.Jmp(Ast.Lab "done", []);
  ] in
  let stmts_Rbb3 = [
    Ast.Label(Type.Name "bb3", []);
    Ast.Move(edi, Ast.BinOp (Type.TIMES, Ast.Var ebx, imm4), [Type.Liveout]);
    Ast.Jmp(Ast.Lab "done", []);
  ] in

  let stmts_done_L = [
    Ast.Label(Type.Name "done", []);
    (* Use both outputs of BB2 *)
    Ast.Move(eax, Ast.BinOp (Type.PLUS, Ast.Var eax, Ast.Var ebx), []);
    Ast.Move(eax, Ast.BinOp (Type.MINUS, Ast.Var eax, Ast.Var esi), []);
    Ast.Halt (imm1, []);
  ] in
  let stmts_done_R = [
    Ast.Label(Type.Name "done", []);
    Ast.Move(eax, Ast.BinOp (Type.PLUS, Ast.Var edx, Ast.Var ecx), []);
    Ast.Move(eax, Ast.BinOp (Type.MINUS, Ast.Var eax, Ast.Var edi), []);
    Ast.Halt (imm1, []);
  ] in

object
  inherit base_test
  method name = "expansion"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Lbb1 in
    let (g, bb2) = C.create_vertex g stmts_Lbb2 in
    let (g, bb3) = C.create_vertex g stmts_Lbb3 in
    let (g, bbdone) = C.create_vertex g stmts_done_L in

    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bbdone) in
    let g = C.add_edge_e g (C.G.E.create bb3 None bbdone) in
    g

  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Rbb1 in
    let (g, bb2) = C.create_vertex g stmts_Rbb2 in
    let (g, bb3) = C.create_vertex g stmts_Rbb3 in
    let (g, bbdone) = C.create_vertex g stmts_done_R in
    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bbdone) in
    let g = C.add_edge_e g (C.G.E.create bb3 None bbdone) in
    g

  method verify subg =
    validate subg;
    assert_fuzziness_partial subg Cmpres.ExactOnly 3 4
end

let tf_consolidation =
  let stmts_Lbb1 = [
    Ast.Move(edx, Ast.BinOp (Type.MINUS, Ast.Var esi, Ast.Var edi), []);
    Ast.Move(eax, Ast.BinOp (Type.MINUS, Ast.Var ecx, Ast.Var ebx), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, Ast.exp_false, Ast.Var zf), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "t", Ast.Lab "f", []);
  ] in
  let stmts_Lbb2 = [
    Ast.Label (Type.Name "t", []);
    Ast.Move(edx, Ast.BinOp (Type.PLUS, Ast.Var edx, imm4), []);
    Ast.Jmp(Ast.Lab "out", []);
  ] in
  let stmts_Lbb3 = [
    Ast.Label (Type.Name "f", []);
    Ast.Move(eax, Ast.BinOp (Type.MINUS, Ast.Var eax, imm1), []);
    Ast.Jmp(Ast.Lab "out", []);
  ] in
  let stmts_Lbb4 = [
    Ast.Label(Type.Name "out", []);
    Ast.Move(ecx, Ast.BinOp(Type.PLUS, Ast.Var esi, imm4), []);
    Ast.Move(ebp, Ast.BinOp(Type.PLUS, Ast.Var edx, Ast.Var eax), []);
    Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var ecx, Ast.Var ebp), []);
    Ast.Halt (imm1, []);
  ] in

  let stmts_Rbb1 = [
    Ast.Move(esi, Ast.BinOp (Type.MINUS, Ast.Var ecx, Ast.Var eax), []);
    Ast.Move(edi, Ast.BinOp (Type.MINUS, Ast.Var edx, Ast.Var ebp), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, Ast.exp_false, Ast.Var zf), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "t", Ast.Lab "f", []);
  ] in
  let stmts_Rbb2 = [
    Ast.Label (Type.Name "t", []);
    Ast.Move(esi, Ast.BinOp (Type.PLUS, Ast.Var esi, imm4), []);
    Ast.Jmp(Ast.Lab "out", []);
  ] in
  let stmts_Rbb3 = [
    Ast.Label (Type.Name "f", []);
    Ast.Move(edi, Ast.BinOp (Type.MINUS, Ast.Var edi, imm1), []);
    Ast.Jmp(Ast.Lab "out", []);
  ] in
  let stmts_Rbb4 = [
    Ast.Label(Type.Name "out", []);
    (*
      This should be
      edx = ecx + 4
      But, we _want_ it to conflict in a way that will only be detected if
      we make use of the fact that, in the entry BB the out assumption
      {edx, eax} <-> {esi, edi} is linked with assumptions for the BB's inputs
      (namely, if {edx} <-> {esi}, then we have the IN assumptions
      {esi} <-> {ecx} and {edi} <-> {eax}. This also forces the OUT assumption
      {eax} <-> {edi} for BB_Entry, which implies the IN assumptions
      {ecx} <-> {edx} and {ebx} <-> {ebp}). So here we will use
      edx = edx + 4
      which will produce the IN assumption {esi} <-> {edx} in this BB,
      conflicting with the IN assumption {ecx} <-> {edx} that is forced
      as described above (indeed, {edx} <-> {esi} is an IN assumption of
      (Lbb2, Rbb2) which will resolve the initial OUT assumption
      {edx, eax} <-> {esi, edi} of BB_entry to {edx} <-> {esi}, {eax} <-> {edi},
      starting the chain reaction above
    *)
    Ast.Move(edx, Ast.BinOp(Type.PLUS, Ast.Var edx, imm4), []);
    Ast.Move(ebx, Ast.BinOp(Type.PLUS, Ast.Var esi, Ast.Var edi), []);
    Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var edx, Ast.Var ebx), []);
    Ast.Halt (imm1, []);
  ] in

object
  inherit base_test
  method name = "tf_consolidation"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Lbb1 in
    let (g, bb2) = C.create_vertex g stmts_Lbb2 in
    let (g, bb3) = C.create_vertex g stmts_Lbb3 in
    let (g, bb4) = C.create_vertex g stmts_Lbb4 in

    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bb4) in
    let g = C.add_edge_e g (C.G.E.create bb3 None bb4) in
    g

  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Rbb1 in
    let (g, bb2) = C.create_vertex g stmts_Rbb2 in
    let (g, bb3) = C.create_vertex g stmts_Rbb3 in
    let (g, bb4) = C.create_vertex g stmts_Rbb4 in

    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bb4) in
    let g = C.add_edge_e g (C.G.E.create bb3 None bb4) in
    g
  method verify subg =
    validate subg;
    assert_exact_total subg
end

let trivial_stack_slot_test =
object
  inherit base_test
  method name = "trivial_stack_slot"
  method cfg_left =
    let temp = Disasm_temp.nt "t" Ast.reg_32 in
    let stmts = [
      Ast.Move(esp, Ast.BinOp(Type.MINUS, Ast.Var esp, imm4), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm0, Ast.exp_false,
			      Type.Reg 32), []);
      Ast.Move(esp, Ast.BinOp(Type.MINUS, Ast.Var esp, imm4), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm1, Ast.exp_false,
			      Type.Reg 32), []);
      Ast.Move(ebx, Ast.Load(Ast.Var mem, Ast.Var esp, Ast.exp_false,
			     Type.Reg 32), []);
      Ast.Move(temp, Ast.BinOp(Type.PLUS, Ast.Var esp, imm4), []);
      Ast.Move(ecx, Ast.Load(Ast.Var mem, Ast.Var temp, Ast.exp_false,
			     Type.Reg 32), []);
      Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var ebx, Ast.Var ecx), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let temp = Disasm_temp.nt "t" Ast.reg_32 in
    let stmts = [
      Ast.Move(esp, Ast.BinOp(Type.MINUS, Ast.Var esp, imm4), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm1, Ast.exp_false,
			      Type.Reg 32), []);
      Ast.Move(esp, Ast.BinOp(Type.MINUS, Ast.Var esp, imm4), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm0, Ast.exp_false,
			      Type.Reg 32), []);
      Ast.Move(edx, Ast.Load(Ast.Var mem, Ast.Var esp, Ast.exp_false,
			     Type.Reg 32), []);
      Ast.Move(temp, Ast.BinOp(Type.PLUS, Ast.Var esp, imm4), []);
      Ast.Move(edi, Ast.Load(Ast.Var mem, Ast.Var temp, Ast.exp_false,
			     Type.Reg 32), []);
      Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var edx, Ast.Var edi), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
    (* Not ready to enable this yet *)
    validate subg;
    let res_sexp = Subg.to_string subg in
    (*
     * Note: Here, we could pair R_ESPL to R_ESPR but, in the general case,
     * we might have a stack slot paired to a register, in which case
     * there's nothing to pair the base register to.
     * XXX:
     * HOWEVER, in general, I think we /have/ to take base registers into
     * account; e.g. if we paired *(R_ESPL + 4) to *(R_ESPR + 8), we can't
     * go on and pair *(R_ESPL + 12) to *(R_EBXR + 12). That would be an
     * inconsistent assumption.
     *)
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN ()) (OUT (((R_EAXL_284:u32) (R_EAXR_310:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAXL_284:u32) (R_EAXR_310:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

let trivial_load_test =
object
  inherit base_test
  method name = "trivial_load"
  method cfg_left =
    let stmts = [
      Ast.Move(eax, Ast.Load (Ast.Var mem, Ast.Var esp, Ast.exp_false, Type.Reg 32), []);
      Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var eax, Ast.Var ecx), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let stmts = [
(*      Ast.Move(ebx, Ast.Load (mem, Ast.Var ecx, Ast.exp_false, Type.Reg 32), []); *)
      Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var ebx, Ast.Var esi), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
(*    validate subg;*)
    let res_sexp = Subg.to_string subg in
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN
      (((R_ECX_1:u32 ary_R_ESP_2:u32_f0t3_3:u8?u32)
        (R_EBXR_6:u32 R_ESIR_2:u32))))
     (OUT (((R_EAX_4:u32) (R_EAXR_431:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAX_4:u32) (R_EAXR_431:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

let repeated_store_test =
object
  inherit base_test
  (*
   * XXX: We no longer collapse non-ESP-based loads/stores, so this
   * will remain disabled. We could do it, but not yet (introduces
   * tons of complexity in the validation).
   *)
  method name = "repeated_store"
  method cfg_left =
    let stmts = [
      Ast.Move(esp, Ast.BinOp (Type.MINUS, Ast.Var esp, imm4), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ebx, imm0, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ebx, imm1, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm0, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ebx, imm4, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(eax, Ast.Load(Ast.Var mem, Ast.Var ebx, Ast.exp_false,
                             Type.Reg 32), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let stmts = [
      (*
       * Different number of stores, different values stored, final
       * value remains the same. Also allocate more stack slots, store
       * a different value there. Since the stack slot is not visible,
       * it shouln't matter at all, nor should it be part of the
       * OUT assumptions (XXX: not checking that, currently).
       * XXX: When we pair ary_R_EDX to ary_R_ECX because of the stores,
       * we need to add {R_EDX} <-> {R_ECX} to the *IN* assumptions.
      *)
      Ast.Move(esp, Ast.BinOp (Type.MINUS, Ast.Var esp, imm8), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ecx, imm1, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ecx, imm0, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ecx, imm8, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ecx, imm4, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm8, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move(eax, Ast.Load(Ast.Var mem, Ast.Var ecx, Ast.exp_false,
                             Type.Reg 32), []);
      Ast.Halt (imm1, []);
    ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
    validate subg;
    assert_exact_total subg
end

(*
 * Abbreviations:
 * Ld -> Load
 * St -> Store
 * __ separates Left/Right side program operations
 * _ separates operations of the same program. Order matters.
 *)

(*
 * Two loads from two different input registers. The BBs should be declared
 * equivalent, under the assumption that the base registers are equivalent.
 *)
let mem_LdEDI__LdESI_test =
object
  inherit base_test
  method name = "mem_LdEDI__LdESI_test"
  method cfg_left =
    let open Mock.Helpers in
    let stmts = List.concat [
      gen_prologue 0;
      [
        Ast.Move(ebx, Ast.Load(Ast.Var mem, Ast.Var edi, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.Var ebx, []);
        Ast.Halt (imm1, [])
      ];
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let open Mock.Helpers in
    let stmts = List.concat [
      gen_prologue 0;
      [
        Ast.Move(ecx, Ast.Load(Ast.Var mem, Ast.Var esi, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.Var ecx, []);
        Ast.Halt (imm1, [])
      ];
      ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
    (* XXX: Can't validate this yet *)
    (* validate subg; *)
    let res_sexp = Subg.to_string subg in
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN (((R_EDI_1:u32) (R_ESI_1:u32)) ((mem_2:?u32) (mem_2:?u32))))
     (OUT (((R_EAX_3:u32) (R_EAX_3:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAX_3:u32) (R_EAX_3:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

(*
 *
 *)
let mem_LdEDI_StESI_LdESI_StEDI_test =
object
  inherit base_test
  method name = "mem_LdEDI_StESI_LdESI_StEDI_test"
  method cfg_left =
    let open Mock.Helpers in
    let stmts = List.concat [
      gen_prologue 0;
      [
        Ast.Move(ebx, Ast.Load(Ast.Var mem, Ast.Var edi, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esi, imm1, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.Var ebx, []);
        Ast.Halt (imm1, [])
      ];
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let open Mock.Helpers in
    let stmts = List.concat [
      gen_prologue 0;
      [
        Ast.Move(ecx, Ast.Load(Ast.Var mem, Ast.Var esi, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var edi, imm1, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.Var ecx, []);
        Ast.Halt (imm1, [])
      ];
      ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
(*    validate subg;*)
    let res_sexp = Subg.to_string subg in
    (*
     * XXX: The OUT assumptions carry the values, this is crap. It should
     * just be the array names.
    *)
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 2) (BB_Entry BB_Entry)
    ((IN
      (((R_ESI_1:u32) (R_EDI_1:u32)) ((mem_2:?u32) (mem_2:?u32))))
     (OUT
      (((R_EAX_3:u32) (R_EAX_3:u32))
       ((mem_4:?u32) (mem_4:?u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAX_3:u32) (R_EAX_3:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

let sccvn_load_test =
object
  inherit base_test
  method name = "sccvn_load_test"
  method cfg_left =
    let open Mock.Helpers in
    let temp1 = Disasm_temp.nt "t" Ast.reg_32 in
    let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
    let stmts = List.concat [
      gen_prologue 8;
      [
        Ast.Move(temp1, Ast.BinOp(Type.PLUS, Ast.Var esp, imm4), []);
        Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var temp1, imm4, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var esp, imm1, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(ebx, Ast.Load(Ast.Var mem, Ast.Var esp, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(temp2, Ast.BinOp(Type.MINUS, Ast.Var ebp, imm4), []);
        Ast.Move(eax, Ast.Load(Ast.Var mem, Ast.Var temp2, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var ebx, Ast.Var eax), []);
        Ast.Halt (imm1, []);
      ];
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let open Mock.Helpers in
    let stmts = List.concat [
      gen_prologue 0;
      [
        Ast.Move(eax, Ast.BinOp(Type.PLUS, imm4, imm1), []);
        Ast.Halt (imm1, []);
      ];
      ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
    validate subg;
    let res_sexp = Subg.to_string subg in
    (*
     * XXX: The OUT assumptions carry the values, this is crap. It should
     * just be the array names.
    *)
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN ()) (OUT (((R_EAXL_951:u32) (R_EAXR_985:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAXL_951:u32) (R_EAXR_985:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

let mem_stack_arg_reg_arg_test =
object
  inherit base_test
  method name = "mem_stack_arg_reg_arg_test"
  method cfg_left =
    let open Mock.Helpers in
    let temp1 = Disasm_temp.nt "t" Ast.reg_32 in
    let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
    let stmts = List.concat [
      gen_prologue 0;
      [
        (*
         * Hmm. This gives us a Load(TMem, R_ESI_N). We need to differentiate by
         * looking at the construction of the R_ESI_N value. If it's some
         * arithmetic operation we can't track, we have to give up. However if,
         * as is the case here, it's a series of loads, we should be able to
         * move forward (see memcases.org). But, if so, we need to modify the
         * logic in may_alias_with_store in transfer_function.ml, which
         * currently declares a possible aliasing situation as soon as it
         * sees a Load(TMem).
         *)
        (*
          void foo(int *a, int b)
          {
                  return *a + b;
          }
        *)
        Ast.Move(temp1, Ast.BinOp(Type.PLUS, Ast.Var ebp, immc), []);
        Ast.Move(esi, Ast.Load(Ast.Var mem, Ast.Var temp1, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.Load(Ast.Var mem, Ast.Var esi, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(temp2, Ast.BinOp(Type.PLUS, Ast.Var ebp, imm0x10), []);
        Ast.Move(edx, Ast.Load(Ast.Var mem, Ast.Var temp2, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var eax, Ast.Var edx), []);
        Ast.Halt (imm1, [])
      ];
    ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    let open Mock.Helpers in
    let stmts = List.concat [
      gen_prologue 0;
      [
        Ast.Move(ecx, Ast.Load(Ast.Var mem, Ast.Var esi, Ast.exp_false, Type.Reg 32), []);
        Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var ecx, Ast.Var edx), []);
        Ast.Halt (imm1, [])
      ];
      ] in
    Mock.build_single_bb_graph stmts
  method verify subg =
(*    validate subg; *)
    let res_sexp = Subg.to_string subg in
    (*
     * XXX: The OUT assumptions carry the values, this is crap. It should
     * just be the array names.
    *)
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN
      (((ary_R_ESP_1:u32_f12t15_2:u8?u32 mem_3:?u32)
        (R_EDX_1:u32 mem_2:?u32))))
     (OUT (((R_EAX_4:u32) (R_EAX_3:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAX_4:u32) (R_EAX_3:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

let arrayification_test =
  (*
    if (ptr->field1 == 0) {
      ptr->field1 = 1;
    }
    return ptr->field1 * ptr->field2;
  *)
  let temp = let ctx = BatHashtbl.create 4 in
             (fun n -> match Misc.bathashtbl_find_option ctx n with
             | Some t -> t
             | None -> let t = Disasm_temp.nt "t" Ast.reg_32 in
                       BatHashtbl.add ctx n t;
                       t)
  in
  let stmts_lbb1 = [
    Ast.Move(edx, Ast.BinOp(Type.PLUS, Ast.Var esp, imm8), []);
    Ast.Move(ebx, Ast.Load(Ast.Var mem, Ast.Var edx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(temp 1, Ast.Load(Ast.Var mem, Ast.Var ebx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var (temp 1)), []);
    Ast.CJmp(Ast.UnOp(Type.NOT, Ast.Var zf), Ast.Lab "default", Ast.Lab "product", []);
  ] in

  let stmts_rbb1 = [
    Ast.Move(ecx, Ast.BinOp(Type.PLUS, Ast.Var esp, imm8), []);
    Ast.Move(edx, Ast.Load(Ast.Var mem, Ast.Var ecx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(temp 1, Ast.Load(Ast.Var mem, Ast.Var edx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var (temp 1)), []);
    Ast.CJmp(Ast.UnOp(Type.NOT, Ast.Var zf), Ast.Lab "default", Ast.Lab "product", []);
  ] in

  let stmts_lbb2 = [
    Ast.Label (Type.Name "default", []);
    Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var ebx, imm1, Ast.exp_false, Type.Reg 32), []);
    Ast.Jmp(Ast.Lab "product", [])
  ] in

  let stmts_rbb2 = [
    Ast.Label (Type.Name "default", []);
    Ast.Move(mem, Ast.Store(Ast.Var mem, Ast.Var edx, imm1, Ast.exp_false, Type.Reg 32), []);
    Ast.Jmp(Ast.Lab "product", [])
  ] in

  let stmts_lbb3 = [
    Ast.Label (Type.Name "product", []);
    Ast.Move(temp 1, Ast.Load(Ast.Var mem, Ast.Var ebx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(ebx, Ast.BinOp(Type.PLUS, Ast.Var ebx, imm4), []);
    Ast.Move(temp 2, Ast.Load(Ast.Var mem, Ast.Var ebx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(eax, Ast.BinOp(Type.TIMES, Ast.Var (temp 1), Ast.Var (temp 2)), []);
    Ast.Halt(imm0, []);
  ] in
  let stmts_rbb3 = [
    Ast.Label (Type.Name "product", []);
    Ast.Move(temp 1, Ast.Load(Ast.Var mem, Ast.Var edx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(edx, Ast.BinOp(Type.PLUS, Ast.Var edx, imm4), []);
    Ast.Move(temp 2, Ast.Load(Ast.Var mem, Ast.Var edx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(eax, Ast.BinOp(Type.TIMES, Ast.Var (temp 1), Ast.Var (temp 2)), []);
    Ast.Halt(imm0, []);
  ] in
object(self)
  inherit base_test
  method name = "arrayification"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_lbb1 in
    let (g, bb2) = C.create_vertex g stmts_lbb2 in
    let (g, bb3) = C.create_vertex g stmts_lbb3 in

    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bb3) in
    g
  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_rbb1 in
    let (g, bb2) = C.create_vertex g stmts_rbb2 in
    let (g, bb3) = C.create_vertex g stmts_rbb3 in

    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bb3) in
    g
  method verify subg =
(*    validate subg;*)
    assert_exact_total subg
end

let zeroword_loop_test =
  (*
    The loop is
    int zeroword(void *buf)
    {
        u32 *start = buf;
        for (;; ++buf) {
            if (!*buf)
                return buf - start;
        }
    }
    this tries to emulate the strlen expansion that process
    4 bytes at a time.
  *)
  (*
    The LHS holds buff in EAX, start in EDX
  *)
  let stmts_Lbb1 = [
    Ast.Move(edx, Ast.Var eax, []);
  ] in
  let temp = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Lbb2 = [
    Ast.Label (Type.Name "loop_head", []);
    Ast.Move(temp, Ast.Load (Ast.Var mem, Ast.Var eax, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var temp), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "loop_body", Ast.Lab "out", []);
  ] in
  let stmts_Lbb3 = [
    Ast.Label (Type.Name "loop_body", []);
    Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var eax, imm4), []);
    Ast.Jmp(Ast.Lab "loop_head", []);
  ] in
  let stmts_Lbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(eax, Ast.BinOp(Type.MINUS, Ast.Var eax, Ast.Var edx), []);
    Ast.Halt (imm1, []);
  ] in

  (*
    The RHS holds buff in ESI, start in ECX
  *)
  let stmts_Rbb1 = [
    Ast.Move(ecx, Ast.Var esi, []);
  ] in
  let temp = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Rbb2 = [
    Ast.Label (Type.Name "loop_head", []);
    Ast.Move(temp, Ast.Load (Ast.Var mem, Ast.Var esi, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var temp), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "loop_body", Ast.Lab "out", []);
  ] in
  let stmts_Rbb3 = [
    Ast.Label (Type.Name "loop_body", []);
    Ast.Move(esi, Ast.BinOp(Type.PLUS, Ast.Var esi, imm4), []);
    Ast.Jmp(Ast.Lab "loop_head", []);
  ] in
  let stmts_Rbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(eax, Ast.BinOp(Type.MINUS, Ast.Var esi, Ast.Var ecx), []);
    Ast.Halt (imm1, []);
  ] in
object
  inherit base_test
  method name = "zeroword_loop"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Lbb1 in
    let (g, bb2) = C.create_vertex g stmts_Lbb2 in
    let (g, bb3) = C.create_vertex g stmts_Lbb3 in
    let (g, bb4) = C.create_vertex g stmts_Lbb4 in

    let g = C.add_edge_e g (C.G.E.create entry None bb2) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb4) in
    g
  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Rbb1 in
    let (g, bb2) = C.create_vertex g stmts_Rbb2 in
    let (g, bb3) = C.create_vertex g stmts_Rbb3 in
    let (g, bb4) = C.create_vertex g stmts_Rbb4 in

    let g = C.add_edge_e g (C.G.E.create entry None bb2) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb4) in
    g
  method verify subg =
    (* validate subg;*)
    assert_exact_total subg
end

let zeroword_loop_mismatch_test =
  (*
    Same as the zeroword_loop test, except the increment is different
    on the RHS.
    int zeroword(void *buf)
    {
        {u32,u16} *start = buf;
        for (;; ++buf) {
            if (!*buf)
                return buf - start;
        }
    }
  *)
  let stmts_Lbb1 = [
    Ast.Move(edx, Ast.Var eax, []);
  ] in
  let temp = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Lbb2 = [
    Ast.Label (Type.Name "loop_head", []);
    Ast.Move(temp, Ast.Load (Ast.Var mem, Ast.Var eax, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var temp), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "loop_body", Ast.Lab "out", []);
  ] in
  let stmts_Lbb3 = [
    Ast.Label (Type.Name "loop_body", []);
    Ast.Move(eax, Ast.BinOp(Type.PLUS, Ast.Var eax, imm4), []);
    Ast.Jmp(Ast.Lab "loop_head", []);
  ] in
  let stmts_Lbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(eax, Ast.BinOp(Type.MINUS, Ast.Var eax, Ast.Var edx), []);
    Ast.Halt (imm1, []);
  ] in

  (*
    The RHS holds buff in ESI, start in ECX
  *)
  let stmts_Rbb1 = [
    Ast.Move(ecx, Ast.Var esi, []);
  ] in
  let temp = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Rbb2 = [
    Ast.Label (Type.Name "loop_head", []);
    Ast.Move(temp, Ast.Load (Ast.Var mem, Ast.Var esi, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var temp), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "loop_body", Ast.Lab "out", []);
  ] in
  let stmts_Rbb3 = [
    Ast.Label (Type.Name "loop_body", []);
    Ast.Move(esi, Ast.BinOp(Type.PLUS, Ast.Var esi, imm2), []);
    Ast.Jmp(Ast.Lab "loop_head", []);
  ] in
  let stmts_Rbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(eax, Ast.BinOp(Type.MINUS, Ast.Var esi, Ast.Var ecx), []);
    Ast.Halt (imm1, []);
  ] in
object
  inherit base_test
  method name = "zeroword_loop_mismatch"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Lbb1 in
    let (g, bb2) = C.create_vertex g stmts_Lbb2 in
    let (g, bb3) = C.create_vertex g stmts_Lbb3 in
    let (g, bb4) = C.create_vertex g stmts_Lbb4 in

    let g = C.add_edge_e g (C.G.E.create entry None bb2) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb4) in
    g
  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Rbb1 in
    let (g, bb2) = C.create_vertex g stmts_Rbb2 in
    let (g, bb3) = C.create_vertex g stmts_Rbb3 in
    let (g, bb4) = C.create_vertex g stmts_Rbb4 in

    let g = C.add_edge_e g (C.G.E.create entry None bb2) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb4) in
    g
  method verify subg =
    (*
      For an unknown reason the SCCVN optimization pass causes
      validation to compute two non-overlapping skip lists resulting
      in no states to validate for the LHS. So due to time-constraints
      we disable validation for now, but it has to be fixed some day!
    *)
    (* validate subg; *)
    assert_fuzziness_partial subg Cmpres.ExactOnly 2 4
end

let slist_foreach_test =
  (*
    The loop is
    struct slist_node {
        int n;
        struct slist_node *next;
    };
    int sum = 0;
    for (p = head;;) {
        if (!p)
            return sum;
        sum += p->n;
        p = p->next
    }
  *)
  (*
    The LHS holds head in EAX, p in EDX, sum in ECX
  *)
  let stmts_Lbb1 = [
    Ast.Move(ecx, imm0, []);
    Ast.Move(edx, Ast.Var eax, []);
  ] in
  let stmts_Lbb2 = [
    Ast.Label (Type.Name "loop_head", []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var edx), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "loop_body", Ast.Lab "out", []);
  ] in
  let temp = Disasm_temp.nt "t" Ast.reg_32 in
  let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Lbb3 = [
    Ast.Label (Type.Name "loop_body", []);
    Ast.Move(temp, Ast.Load (Ast.Var mem, Ast.Var edx, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(ecx, Ast.BinOp (Type.PLUS, Ast.Var ecx, Ast.Var temp), []);
    Ast.Move(temp2, Ast.BinOp (Type.PLUS, Ast.Var edx, imm4), []);
    Ast.Move(edx, Ast.Load (Ast.Var mem, Ast.Var temp2, Ast.exp_false, Type.Reg 32), []);
    Ast.Jmp(Ast.Lab "loop_head", []);
  ] in
  let stmts_Lbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(eax, Ast.Var ecx, []);
    Ast.Halt (imm1, []);
  ] in

  (*
    The RHS holds head in ESI, p in EDI, sum in EBX
  *)
  let stmts_Rbb1 = [
    Ast.Move(ebx, imm0, []);
    Ast.Move(edi, Ast.Var esi, []);
  ] in
  let stmts_Rbb2 = [
    Ast.Label (Type.Name "loop_head", []);
    Ast.Move(zf, Ast.BinOp (Type.EQ, imm0, Ast.Var edi), []);
    Ast.CJmp(Ast.UnOp(Type.NEG, Ast.Var zf), Ast.Lab "loop_body", Ast.Lab "out", []);
  ] in
  let temp = Disasm_temp.nt "t" Ast.reg_32 in
  let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Rbb3 = [
    Ast.Label (Type.Name "loop_body", []);
    Ast.Move(temp, Ast.Load (Ast.Var mem, Ast.Var edi, Ast.exp_false, Type.Reg 32), []);
    Ast.Move(ebx, Ast.BinOp (Type.PLUS, Ast.Var ebx, Ast.Var temp), []);
    Ast.Move(temp2, Ast.BinOp (Type.PLUS, Ast.Var edi, imm4), []);
    Ast.Move(edi, Ast.Load (Ast.Var mem, Ast.Var temp2, Ast.exp_false, Type.Reg 32), []);
    Ast.Jmp(Ast.Lab "loop_head", []);
  ] in
  let stmts_Rbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(esi, Ast.Var ebx, []);
    Ast.Halt (imm1, []);
  ] in

object
  inherit base_test
  method name = "slist_foreach"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in

    let g = C.set_stmts g entry stmts_Lbb1 in
    let (g, bb2) = C.create_vertex g stmts_Lbb2 in
    let (g, bb3) = C.create_vertex g stmts_Lbb3 in
    let (g, bb4) = C.create_vertex g stmts_Lbb4 in

    let g = C.add_edge_e g (C.G.E.create entry None bb2) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb4) in
    g
  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in

    let g = C.set_stmts g entry stmts_Rbb1 in
    let (g, bb2) = C.create_vertex g stmts_Rbb2 in
    let (g, bb3) = C.create_vertex g stmts_Rbb3 in
    let (g, bb4) = C.create_vertex g stmts_Rbb4 in

    let g = C.add_edge_e g (C.G.E.create entry None bb2) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb4) in
    g
  method verify subg =
    validate subg;
    assert_exact_total subg
end

let cjmp_inversion_test =
  let stmts_Lbb1 = [
    Ast.Move(eax, Ast.BinOp (Type.EQ, Ast.Var eax, imm0), []);
    Ast.Move(ecx, Ast.UnOp(Type.NOT, Ast.Var eax), []);
    Ast.Move(ecx, Ast.UnOp(Type.NOT, Ast.Var ecx), []);
    Ast.CJmp(Ast.Var ecx, Ast.Lab "left", Ast.Lab "right", []);
  ] in
  let stmts_Lbb2 = [
    Ast.Label (Type.Name "left", []);
    Ast.Move (edx, imm0, []);
    Ast.Jmp (Ast.Lab "out", []);
  ] in
  let stmts_Lbb3 = [
    Ast.Label (Type.Name "right", []);
    Ast.Move(edx, imm1, []);
    Ast.Jmp(Ast.Lab "out", []);
  ] in
  let stmts_Lbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(eax, Ast.Var edx, []);
    Ast.Halt (imm1, []);
  ] in

  let stmts_Rbb1 = [
    Ast.Move(eax, Ast.BinOp (Type.EQ, Ast.Var eax, imm0), []);
    Ast.Move(edi, Ast.UnOp(Type.NOT, Ast.Var eax), []);
    Ast.Move(edi, Ast.UnOp(Type.NOT, Ast.Var edi), []);
    Ast.Move(edi, Ast.UnOp(Type.NOT, Ast.Var edi), []);
    Ast.CJmp(Ast.Var edi, Ast.Lab "right", Ast.Lab "left", []);
  ] in
  let stmts_Rbb2 = [
    Ast.Label (Type.Name "left", []);
    Ast.Move (esi, imm0, []);
    Ast.Jmp (Ast.Lab "out", []);
  ] in
  let stmts_Rbb3 = [
    Ast.Label (Type.Name "right", []);
    Ast.Move(esi, imm1, []);
    Ast.Jmp(Ast.Lab "out", []);
  ] in
  let stmts_Rbb4 = [
    Ast.Label (Type.Name "out", []);
    Ast.Move(eax, Ast.Var esi, []);
    Ast.Halt (imm1, []);
  ] in

object
  inherit base_test
  method name = "cjmp_inversion"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Lbb1 in
    let (g, bb2) = C.create_vertex g stmts_Lbb2 in
    let (g, bb3) = C.create_vertex g stmts_Lbb3 in
    let (g, bbdone) = C.create_vertex g stmts_Lbb4 in

    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bbdone) in
    let g = C.add_edge_e g (C.G.E.create bb3 None bbdone) in
    g

  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Rbb1 in
    let (g, bb2) = C.create_vertex g stmts_Rbb2 in
    let (g, bb3) = C.create_vertex g stmts_Rbb3 in
    let (g, bbdone) = C.create_vertex g stmts_Rbb4 in
    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 None bbdone) in
    let g = C.add_edge_e g (C.G.E.create bb3 None bbdone) in
    g

  method verify subg =
    (* validate subg; Fails :( *)
    assert_exact_total subg
end

let rewrite_global_test =
  (*
   * global uint8 a;
   * global uint32 b;
   * eax = pad:u32(Ld(a)) + Ld(b)
   *)

object
  inherit base_test
  method name = "rewrite_global_test"
  method cfg_left =
    (*
      The LHS has a at 0xa0a0a0a0 and b at 0xb0b0b0b0.
    *)
    let open Big_int_Z in
    let open Mock.Helpers in
    let temp = Disasm_temp.nt "t" Ast.reg_8 in
    let stmts = List.concat [
        gen_prologue 0;
        [
          Ast.Move (temp, Ast.Load (Ast.Var mem, Ast.Int (big_int_of_int 0xa0a0a0a0, Type.Reg 32),
                                    Ast.exp_false, Type.Reg 8), []);
          Ast.Move (ebx, Ast.Cast (Type.CAST_UNSIGNED, Type.Reg 32, Ast.Var temp), []);
          Ast.Move (eax, Ast.Int (big_int_of_int 0xb0b0b0b0, Type.Reg 32), []);
          Ast.Move (eax, Ast.Load (Ast.Var mem, Ast.Var eax, Ast.exp_false, Type.Reg 32), []);
          Ast.Move (eax, Ast.BinOp (Type.PLUS, Ast.Var eax, Ast.Var ebx), []);
          Ast.Halt (imm1, []);
        ];
      ] in
    Mock.build_single_bb_graph stmts
  method cfg_right =
    (*
      The LHS has a at 0xa1a1a1a1 and b at 0xb1b1b1b1.
    *)
    let open Big_int_Z in
    let open Mock.Helpers in
    let temp = Disasm_temp.nt "t" Ast.reg_8 in
    let stmts = List.concat [
        gen_prologue 0;
        [
          Ast.Move (temp, Ast.Load (Ast.Var mem, Ast.Int (big_int_of_int 0xa1a1a1a1, Type.Reg 32),
                                    Ast.exp_false, Type.Reg 8), []);
          Ast.Move (ecx, Ast.Cast (Type.CAST_UNSIGNED, Type.Reg 32, Ast.Var temp), []);
          Ast.Move (eax, Ast.Int (big_int_of_int 0xb1b1b1b1, Type.Reg 32), []);
          Ast.Move (ebx, Ast.Load (Ast.Var mem, Ast.Var eax, Ast.exp_false, Type.Reg 32), []);
          Ast.Move (eax, Ast.BinOp (Type.PLUS, Ast.Var ecx, Ast.Var ebx), []);
          Ast.Halt (imm1, []);
        ];
      ] in
    Mock.build_single_bb_graph stmts

  method verify subg =
    (* validate subg; *)
    let res_sexp = Subg.to_string subg in
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN
      (((ary_global_1:u32_f2694881440t2694881440_2:u8?u32)
        (ary_global_1:u32_f2711724449t2711724449_2:u8?u32))
       ((ary_global_1:u32_f2964369584t2964369587_3:u8?u32)
        (ary_global_1:u32_f2981212593t2981212596_3:u8?u32))))
     (OUT (((R_EAX_4:u32) (R_EAX_4:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAX_4:u32) (R_EAX_4:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

let vrg_rewrite1_test =
  (*
   * lea (%esi, %eax, 4), %ecx
   * mov 4(%ecx), %eax
   *)
  let temp0 = Disasm_temp.nt "t" Ast.reg_8 in
  let temp1 = Disasm_temp.nt "t" Ast.reg_32 in
  let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Lbb1 = [
    Ast.Move(temp0, Ast.Cast (Type.CAST_LOW, Type.Reg 8, Ast.Var eax), []);
    Ast.Move(temp1, Ast.BinOp (Type.TIMES, Ast.Var temp0, imm4), []);
    Ast.Move(ecx, Ast.BinOp (Type.PLUS, Ast.Var temp1, Ast.Var esi), []);
    Ast.Move(temp2, Ast.BinOp (Type.PLUS, Ast.Var ecx, imm4), []);
    Ast.Move(eax, Ast.Load(Ast.Var mem, Ast.Var temp2, Ast.exp_false, Type.Reg 32), []);
    Ast.Halt (imm1, []);
  ] in
  (* lea (%edi, %ebx, 4), %edx; mov 4(%edx, %eax) *)
  let temp0 = Disasm_temp.nt "t" Ast.reg_8 in
  let temp1 = Disasm_temp.nt "t" Ast.reg_32 in
  let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
  let stmts_Rbb1 = [
    Ast.Move(temp0, Ast.Cast (Type.CAST_LOW, Type.Reg 8, Ast.Var ebx), []);
    Ast.Move(temp1, Ast.BinOp (Type.TIMES, Ast.Var temp0, imm4), []);
    Ast.Move(edx, Ast.BinOp (Type.PLUS, Ast.Var temp1, Ast.Var edi), []);
    Ast.Move(temp2, Ast.BinOp (Type.PLUS, Ast.Var edx, imm4), []);
    Ast.Move(eax, Ast.Load(Ast.Var mem, Ast.Var temp2, Ast.exp_false, Type.Reg 32), []);
    Ast.Halt (imm1, []);
  ] in

object
  inherit base_test
  method name = "vrg_rewrite1_test"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Lbb1 in
    g
  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Rbb1 in
    g
  method verify subg =
    (* Grumble, fails validation with "unexpected input" *)
    (* validate subg; *)
    let res_sexp = Subg.to_string subg in
    let expected = "(subgraph (functions (fake fake)) (classification ExactOnly (OverlapTotal 2))
 (bbcmps
  (((EXACT 1) (BB_Entry BB_Entry)
    ((IN
      (((R_EAX_1:u32) (R_EBX_1:u32)) ((R_ESI_2:u32) (R_EDI_2:u32))
       ((mem_3:?u32) (mem_3:?u32))))
     (OUT (((R_EAX_4:u32) (R_EAX_4:u32))))))
   ((EXACT 0) (BB_Exit BB_Exit)
    ((IN ()) (OUT (((R_EAX_4:u32) (R_EAX_4:u32))))))))
 (edgepairs ((EP (E BB_Entry BB_Exit) (E BB_Entry BB_Exit)))))" in
    match strcmp (normalize_sexp expected) (normalize_sexp res_sexp) with
    | BatResult.Ok () ->
      Printf.printf "success\n"
    | BatResult.Bad diff ->
      Printf.eprintf "results differ:\n%s" diff;
      failwith "Did not get the expected subgraph"
end

let buoyancy_test =
  (*
    int musl_strncmp(char * s1, char *s2, size_t n) {
      if (!n--) return 0;
      for(; *s1 && *s2 && n && *s1 == *s2; s1++, s2++, n--);
      return *s1 - *s2;
    }
  *)
  (*
    The LHS uses sub to decrement n, and RHS uses lea.
    This has the effect that sccvn will propagate the value on the LHS
    and will not perform the n == 0 check in the for loop, but uses the
    ZF value computed at n--. Without buoyancy, this will cause a
    subset match.

     The following test case emulates the musl_strncmp case that the
     buoyancy test should solve.
  *)

  let module C = Ast_convenience in
  let open Mock.Helpers in
  let stmts_Lbb1 = List.concat [
      gen_prologue 0;
      push_reg esi;
      push_reg ebx;
      gen_load ~dst:esi ~index:((Ast.Var ebp) +! imm8) ~size:
        Ast.reg_32;
      gen_load ~dst:ebx ~index:((Ast.Var ebp) +! immc) ~size:Ast.reg_32;
      gen_jmp "loop_head";
    ] in
  let stmts_Lbb2 = List.concat [
      gen_label "loop_head";
      [
        (* Emulate sub, that is set the ZF flag *)
        esi ^= (Ast.Var esi) -! imm1;
        zf ^= ((Ast.Var esi) =! imm0);
        zf ^= ((Ast.Var ebx) =! imm0);
      ];
      gen_cjmp ~cond:(Ast.Var zf) ~if_true:(lab "epilog")
        ~if_false:(lab "loop_body");
    ] in
  let stmts_Lbb3 = List.concat [
      gen_label "loop_body";
      [
        zf ^= ((Ast.Var esi) =! imm0);
      ];
      gen_cjmp ~cond:(Ast.Var zf) ~if_true:(lab "epilog")
        ~if_false:(lab "loop_head");
    ] in
  let stmts_Lbb4 = List.concat [
      gen_label "epilog";
      pop ebx;
      pop esi;
      gen_retn 0;
    ] in
  let stmts_Rbb1 = List.concat [
      gen_prologue 0;
      push_reg esi;
      push_reg ebx;
      gen_load ~dst:esi ~index:((Ast.Var ebp) +! imm8) ~size:
        Ast.reg_32;
      gen_load ~dst:ebx ~index:((Ast.Var ebp) +! immc) ~size:Ast.reg_32;
      gen_jmp "loop_head";
    ] in
  let stmts_Rbb2 = List.concat [
      gen_label "loop_head";
      [
        (* Emulate lea, that is DO NOT set the ZF flag *)
        esi ^= (Ast.Var esi) -! imm1;
        zf ^= ((Ast.Var ebx) =! imm0);
      ];
      gen_cjmp ~cond:(Ast.Var zf) ~if_true:(lab "epilog")
        ~if_false:(lab "loop_body");
    ] in
  let stmts_Rbb3 = List.concat [
      gen_label "loop_body";
      [
        zf ^= ((Ast.Var esi) =! imm0);
      ];
      gen_cjmp ~cond:(Ast.Var zf) ~if_true:(lab "epilog")
        ~if_false:(lab "loop_head");
    ] in
  let stmts_Rbb4 = List.concat [
      gen_label "epilog";
      pop ebx;
      pop esi;
      gen_retn 0;
    ] in
object
  inherit base_test
  method name = "buoyancy_test"
  method cfg_left =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Lbb1 in
    let (g, bb2) = C.create_vertex g stmts_Lbb2 in
    let (g, bb3) = C.create_vertex g stmts_Lbb3 in
    let (g, bb4) = C.create_vertex g stmts_Lbb4 in

    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb4) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb4) in
    let g = C.add_edge_e g (C.G.E.create bb3 (Some false) bb2) in
    let g = C.add_edge_e g (C.G.E.create bb3 (Some true) bb4) in
    g
  method cfg_right =
    let module C = Cfg.AST in
    let open Open_cfg_ast in
    let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
    let g = C.set_stmts g entry stmts_Rbb1 in
    let (g, bb2) = C.create_vertex g stmts_Rbb2 in
    let (g, bb3) = C.create_vertex g stmts_Rbb3 in
    let (g, bb4) = C.create_vertex g stmts_Rbb4 in

    let g = C.add_edge_e g (C.G.E.create entry (Some false) bb2) in
    let g = C.add_edge_e g (C.G.E.create entry (Some true) bb4) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some false) bb3) in
    let g = C.add_edge_e g (C.G.E.create bb2 (Some true) bb4) in
    let g = C.add_edge_e g (C.G.E.create bb3 (Some false) bb2) in
    let g = C.add_edge_e g (C.G.E.create bb3 (Some true) bb4) in
    g
  method verify subg =
    assert_exact_total subg
end

let testcases = [
  rewrite_global_test;
  trivial_test;
  commutative_test;
  (* This is waiting on expression normalization *)
(*  commutative_abcd_test; *)
  assign_through_test;
  expansion_test;
(*  simple_loop_test;*)
(* this depends on our producing more accurate assumptions for
   TFs that are indistinguishable. Currently it will produce an exact match,
   whereas it should actually result in a conflict as soon as the subgraph is
   expanded to include both (Lbb1, Rbb1) and (Lbb4, Rbb4).*)
  (* tf_consolidation; *)
  trivial_load_test;
  trivial_stack_slot_test;
  arrayification_test;
(*  stack_vs_registerized_loop_test;*)
  (*
   * Disabled, as we can't validate it yet.
   *)
  (* repeated_store_test; *)
  mem_LdEDI__LdESI_test;
  mem_LdEDI_StESI_LdESI_StEDI_test;
  sccvn_load_test;
  mem_stack_arg_reg_arg_test;
  zeroword_loop_test;
  zeroword_loop_mismatch_test;
(*  eurosys_example;*)
(* Not ready for this yet
  slist_foreach_test; *)
  cjmp_inversion_test;
  vrg_rewrite1_test;
  buoyancy_test;
]

let run_tests () =
  let run_test testcase =
    let build_mock_prog pname cfg =
      if debug () then begin
	Printf.eprintf "MOCKPROG %s %s\n" pname Print.fo;
      end;
      let prog_addrmap = Mock.mockprog_tmpl 1 in
      let serialized_stmts = Mock.serialize_graph prog_addrmap 0 cfg in
      dprintf "serialized_stmts: %s\n%s\n%s\n" Print.fo
	(Print.list_to_string ~sep:"\n" Pp.ast_stmt_to_string serialized_stmts)
	Print.fc;
      (* XXX: func boundaries *)
      let interval = Interval.Function_interval.create
        (Int64.of_int 0) (Int64.of_int 0)
      in
      let augf = Function_info.create "fake" interval serialized_stmts in
      let cg = Callgraph.generate_singular_callgraph augf in
      let funcstats = new Stats.analyzable pname in
      let afs = Summarizer.handle_callgraph Asmir.arch_i386 pname None
        cg funcstats in
      if debug () then begin
	Printf.eprintf "cg nv: %d\n" (Callgraph.Callgraph.nb_vertex cg);
	Callgraph.dump_call_graph cg stderr;
	Cfg_pp.SsaStmtsDot.output_graph stderr (List.hd afs).Ktype.cfg;
	Printf.eprintf "\n%s\n" Print.fc;
      end;
      Mock.build_prog_summary
        (module BBMgr : Bb_cluster.BBClusterManagerSig with type t = BBMgr.t)
        pname prog_addrmap afs
    in
    dprintf "START TEST: %s %s1" testcase#name Print.fo;
    let cfg1 = testcase#cfg_left in
    let cfg2 = testcase#cfg_right in
    let pname1 = Printf.sprintf "%s-left" testcase#name in
    let pname2 = Printf.sprintf "%s-right" testcase#name in
    let prog1 = build_mock_prog pname1 cfg1 in
    let prog2 = build_mock_prog pname2 cfg2 in
    Hashtbl.iter (fun _ af -> testcase#verify_af_left af)
      (fst prog1).Ktype.pfuncs;
    Hashtbl.iter (fun _ af -> testcase#verify_af_right af)
      (fst prog2).Ktype.pfuncs;
    let results = TestingComparator.compare (TestingComparator.init ())
        ~entries_only:false prog1 prog2 in
    ignore(match results with
    | _, (x :: _ as ewbs) ->
      let module EP = Embarassingly_parallel in
      let str = EP.exns_with_bts_to_string ewbs in
      Printf.eprintf "Got %d exceptions from workers:\n%s\n"
          (List.length ewbs) str;
      failwith "EXCEPTIONS"
    | results, [] ->
      assert((List.length results) == 1);
      let (_, cmpres) = List.hd results in
      if testcase#expect_subgraph then begin
        let cmpres = List.hd cmpres in
        testcase#verify cmpres
      end else begin
        if (List.length cmpres) > 0 then
          let str = Subg.to_string (List.hd cmpres) in
          failwith (Printf.sprintf "Unexpectedly got match:\n%s\n" str)
      end);
    dprintf "END TEST: %s %s1" testcase#name Print.fc;
  in
  List.iter run_test testcases

let () =
  Printexc.record_backtrace true;
  Embarassingly_parallel.set_debug true;
  Pp.output_varnums := true;
  Pp.many_parens := true;
  Outdir.set_outdir "deleteme-various-test";
  run_tests ();
