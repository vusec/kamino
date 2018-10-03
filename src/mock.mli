type mockprog

val mockprog_tmpl : int -> mockprog
val build_single_bb_graph : Ast.stmt list -> Cfg.AST.G.t
val serialize_graph : mockprog -> int -> Cfg.AST.G.t -> Ast.stmt list
val build_prog_summary : (module Bb_cluster.BBClusterManagerSig with type t = 'a) ->
  string -> mockprog -> Ktype.analyzed_func list ->
  Ktype.analyzed_prog *
       'a

(*
    (Bb.bb_summary BatSet.t Bb_cluster.ClusterHashtbl.t *
       Ktype.analyzed_prog *
       Bb_cluster.HashableString.t Bb_cluster.StringHashtbl.t)*)

class mock_program : string ->
object
  method prog : mockprog
  method funcs : mock_func list
  method register_func : mock_func -> int
  method cg : Callgraph.Callgraph.t
end

and virtual mock_func : mock_program -> string ->
object
  method virtual cfg : Cfg.AST.G.t
  method name : string
  method stmts : Ast.stmt list
end

module Definitions :
sig
  val mem : Var.t
  val esp : Ast.var
  val ebp : Ast.var
  val eax : Ast.var
  val ebx : Ast.var
  val ecx : Ast.var
  val edx : Ast.var
  val esi : Ast.var
  val edi : Ast.var
  val zf : Ast.var
  val flag0 : Ast.exp
  val imm0 : Ast.exp
  val imm1 : Ast.exp
  val imm2 : Ast.exp
  val imm4 : Ast.exp
  val imm8 : Ast.exp
  val immc : Ast.exp
  val imm0x10 : Ast.exp
  val imm37 : Ast.exp
end

module Helpers :
sig
  val push_int : (int * int) -> Ast.stmt list
  val push_reg : Var.t -> Ast.stmt list
  val pop : Var.t -> Ast.stmt list
  val indexed_load : dst:Var.t -> base:Var.t -> index:Var.t -> scale:int -> disp:int -> Ast.stmt list
  val indexed_store : base:Var.t -> index:Var.t -> scale:int -> disp:int -> value:Ast.exp -> Ast.stmt list
  val gen_prologue : int -> Ast.stmt list
  val gen_call : string -> Ast.stmt list
  val gen_retn : int -> Ast.stmt list val label_map : Cfg.AST.G.t -> string
    -> (Type.addr * (Cfg.bbid * int))

  val gen_jmp: string -> Ast.stmt list
  val gen_cjmp: cond:Ast.exp -> if_true:Ast.exp -> if_false:Ast.exp -> Ast.stmt list
  val gen_label: string -> Ast.stmt list
  val gen_load: dst:Ast.var -> index:Ast.exp -> size:Type.typ -> Ast.stmt list
  val lab: string -> Ast.exp

  val (^=): Ast.var -> Ast.exp -> Ast.stmt
  val (+!): Ast.exp -> Ast.exp -> Ast.exp
  val (-!): Ast.exp -> Ast.exp -> Ast.exp
  val (=!): Ast.exp -> Ast.exp -> Ast.exp



end
