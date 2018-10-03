module D = Debug.Make(struct let name = "Mock" and default=`Debug end)
open D

open Interval

let build_func_summary name ast s e =
 Function_info.create name (Function_interval.create s e) ast

(*
 * For mocked-up code, we use an table that's indexed by bits in the fake
 * address
 *)
type bb_descr = (Int64.t * string)
type func_addrmap = (string * bb_descr array)
type prog_addrmap = func_addrmap array

type mockprog = prog_addrmap

let mock_func_addr_size = Int64.of_int 1048576
let mock_bb_addr_size = Int64.of_int 16384

let mockbb_tmpl = (Int64.zero, "BBn")

let mockfunc_tmpl =
  let bba = Array.make 0 mockbb_tmpl in
  ("fname", bba)

let mockprog_tmpl nfuncs =
  Array.create nfuncs mockfunc_tmpl

let prog_addrmap_dump prog =
  Array.iteri (fun i (fname, bbs) ->
    Printf.printf "FUNC %s:\n" fname;
    Array.iteri (fun j (bbaddr, bbname) ->
      Printf.printf "  BB %s: %#Lx\n" bbname bbaddr
    ) bbs
  ) prog

(*
 * Class to provide mapping from addr -> bb/func for our mocked-up functions.
*)
class mock_address_ranges prog_addrmap =
object (self)
  method get_program_bounds =
    let (_, low_bbs) = Array.get prog_addrmap 0 in
    let (_, high_bbs) = Array.get prog_addrmap ((Array.length prog_addrmap) - 1) in
    let (low, _) = Array.get low_bbs 0 in
    let (high, _) = Array.get high_bbs ((Array.length high_bbs) - 1) in
    (low, high)
  method get_function (addr : Int64.t) : (string * Int64.t * Libbfd.address_t) option =
    let func_idx = Int64.div addr mock_func_addr_size in
    let (fname, bbs) = Array.get prog_addrmap (Int64.to_int func_idx) in
    let (saddr, _) = Array.get bbs 0 in
    let (eaddr, _) = Array.get bbs ((Array.length bbs) - 1) in
    Some (fname, saddr, eaddr)
  method get_function_bb (addr : Int64.t) : ((string * Int64.t * Libbfd.address_t) option * (Int64.t * string)) option =
    let func_idx = Int64.div addr mock_func_addr_size in
    let bb_idx = Int64.div func_idx mock_bb_addr_size in
    let (_, bbs) = Array.get prog_addrmap (Int64.to_int func_idx) in
    let bb = Array.get bbs (Int64.to_int bb_idx) in
    (* XXX: factor out parts common with get_function *)
    Some (self#get_function addr, bb)
end
;;

let build_prog_summary (type bbmgr_t) bbmgrmod name mock_ranges afuncs =
  let module BBMgr = (val bbmgrmod : Bb_cluster.BBClusterManagerSig with type t = bbmgr_t) in
  let aprog = {
    Ktype.pname = name;
    Ktype.pranges = new mock_address_ranges mock_ranges;
    Ktype.pfuncs = List.fold_left (fun acc af ->
      Hashtbl.add acc (BatOption.get
                         (Function_info.Function.begin_address af.Ktype.function_info)) af;
      acc
    ) (Hashtbl.create (List.length afuncs)) afuncs;
  } in
  let open Bb_cluster in
  let bbmgr = BBMgr.create aprog in
  let () = List.iter (fun afunc ->
    Bb.BBidMap.iter (fun _ bbsum ->
      BBMgr.add bbmgr afunc bbsum
    ) afunc.Ktype.fbbs) afuncs in
  (aprog, bbmgr)

let stmts =
  let d = Asmir.decls_for_arch Asmir.arch_i386 (* XXX *) in
  let esp = List.find (fun v -> Var.name v = "R_ESP") d in
  [Ast.Move(esp, Ast.Int (Big_int_Z.big_int_of_int 0, Type.Reg 32), []); Ast.Move(esp, Ast.BinOp (Type.MINUS, Ast.Var esp, Ast.Int (Big_int_Z.big_int_of_int 4, Type.Reg 32)), [Type.StrAttr "esp_readjustment"])]


let build_single_bb_graph stmts =
  let module C = Cfg.AST in
  let open Open_cfg_ast in
  let (g, entry) = create (C.empty ()) Cfg.BB_Entry [] in
  let g = C.set_stmts g entry stmts in
  g

let print_stmts stmts =
  List.iter (fun s ->
    Printf.printf "%s\n" (Pp.ast_stmt_to_string s)) stmts

let serialize_graph prog_addrmap func_idx g =
  let module C = Cfg.AST in
  dprintf "serialize_graph: FUNC%d %s" func_idx Print.fo;
  let unsorted_vertices  = C.G.fold_vertex (fun v acc ->
    dprintf "Got a vertex\n";
    v::acc
  ) g [] in
  let predef_vertices = List.length (List.filter (fun v ->
    match C.G.V.label v with
    | Cfg.BB _ -> false
    | _ -> true) unsorted_vertices) in
  (* get BB number *)
  let bb_n v =
    match C.G.V.label v with
    | Cfg.BB n -> n + predef_vertices
    | Cfg.BB_Entry -> 0
    | Cfg.BB_Exit -> 1
    | _ -> failwith (C.v2s v)
  in
  (* Produce a mock BB address (XXX: assumes BBs are reasonably sized) *)
  let mock_addr v =
    dprintf "mock_addr: bb_n is %d" (bb_n v);
    (func_idx * (Int64.to_int mock_func_addr_size)) +
      ((Int64.to_int mock_bb_addr_size) * (bb_n v))
  in
  let stmts_add_addrs base stmts =
    let (_, ret) = List.fold_left (fun (idx, acc) s ->
      dprintf "stmts_add_addrs: %#Lx: %s" (Int64.of_int (base + idx))
        (Pp.ast_stmt_to_string s);
      let lab = Ast.Label (Type.Addr (Int64.of_int (base + idx)), []) in
      (idx + 1, [lab; s]::acc)
    ) (0, []) stmts in
    List.flatten (List.rev ret)
  in
  let vertices = List.sort (fun v1 v2 ->
    let l1 = bb_n v1 in
    let l2 = bb_n v2 in
    l1 - l2) unsorted_vertices in
  (*
   * BB numbers might not be consecutive (if the cfg is generated from
   * serialized IL of actual code that we prossessed somehow), so just
   * allocate "enough" BBs.
   *)
  let bb_addrs = Array.create 100 mockbb_tmpl in
  let nested_stmts = List.fold_left (fun acc v ->
    let stmts = C.get_stmts g v in
    let base_addr = mock_addr v in
    let () = Array.set bb_addrs (bb_n v) (Int64.of_int base_addr, C.v2s v) in
    let nstmts = stmts_add_addrs base_addr stmts in
    nstmts::acc) [] vertices in
  let () = Array.set prog_addrmap func_idx (Printf.sprintf "F%d" func_idx, bb_addrs) in
  dprintf "%s" Print.fc;
  List.flatten (List.rev nested_stmts)

(*
 * Those are just shorthands. Their name does not need to match
 * the names used in the .mli. In fact I added the '2' suffix
 * to make that explicit.
 *)
class type virtual mock_func_type2 =
object
  method virtual cfg : Cfg.AST.G.t
  method name : string
  method stmts : Ast.stmt list
end

class type mock_program_type2 =
object
  method prog : mockprog
  method funcs : mock_func_type2 list
  method register_func : mock_func_type2 -> int
  method cg : Callgraph.Callgraph.t
end

class virtual mock_func (prog : mock_program_type2) (name : string) =
object (self)
  val mutable idx = 0
  method virtual cfg : Cfg.AST.G.t
  method name = name
  method stmts = serialize_graph prog#prog idx self#cfg
  initializer
    idx <- prog#register_func (self :> mock_func_type2)
end

let rewrite_calls stmts labmap =
  let rewrite = function
    | Ast.Jmp (Ast.Lab label, attrs) as s
        when Misc.is_call Asmir.arch_i386 s ->
      (match Misc.bathashtbl_find_option labmap label with
      | None ->
        let str = Printf.sprintf "Call to unknown function: %s"
          (Pp.ast_stmt_to_string s)
        in
        failwith str
      | Some addr ->
        dprintf "Rewriting label '%s' to %#Lx" label addr;
        let addr = Big_int_Z.big_int_of_int64 addr in
        Ast.Jmp (Ast.Int (addr, Type.Reg 32), attrs))
    | s -> s
  in
  List.map rewrite stmts

class mock_program name =
object (self)
  val mutable next_func_idx = 0
  val mutable funcs = []
  val prog_addrmap = mockprog_tmpl 100
  method funcs = funcs
  method register_func (nfunc : mock_func_type2) =
    let ret = next_func_idx in
    next_func_idx <- next_func_idx + 1;
    funcs <- nfunc :: funcs;
    ret
  method prog = prog_addrmap
  method cg =
    let augfs = List.map (fun f ->
      let stmts = f#stmts in
      let upd_addrs low high addr =
        let low = match (Int64.compare addr low < 0) with
          | true -> addr
          | false -> low
        in
        let high = match (Int64.compare addr high > 0) with
          | true -> addr
          | false -> high
        in
        (low, high)
      in
      let (low, high) = List.fold_left (fun (low, high) s ->
        match Bb.stmt_get_addr s with
        | None -> (low, high)
        | Some addr -> upd_addrs low high addr
      ) (Int64.max_int, Int64.min_int) stmts
      in
      let interval = Interval.Function_interval.create low high in
      Function_info.create f#name interval stmts
    ) funcs
    in
    let faddrs = BatHashtbl.create 10 in
    List.iter (fun augf ->
      let syms = Function_info.symbols augf in
      let addr = match Function_info.begin_address augf with
        | None -> failwith "Mocked up function with no address!"
        | Some addr -> addr
      in
      List.iter (fun sym ->
          BatHashtbl.add faddrs sym addr) syms) augfs;
    let augfs = List.map (fun f ->
      let stmts = match Function_info.stmts f with
        | None -> failwith "Mocked up function with no stmts!"
        | Some stmts -> stmts
      in
      let stmts = rewrite_calls stmts faddrs in
      Function_info.set_stmts f stmts) augfs
    in
    let resolver addr =
      let str = Printf.sprintf "Call to external function: %#Lx" addr in
      failwith str
    in
    Callgraph.generate_call_graph resolver augfs
end

module Definitions =
struct
  let mem = Disasm_i386.mem
  let arch_decls = Asmir.decls_for_arch Asmir.arch_i386 (* XXX *)
  let esp = List.find (fun v -> Var.name v = "R_ESP") arch_decls
  let ebp = List.find (fun v -> Var.name v = "R_EBP") arch_decls
  let eax = List.find (fun v -> Var.name v = "R_EAX") arch_decls
  let ebx = List.find (fun v -> Var.name v = "R_EBX") arch_decls
  let ecx = List.find (fun v -> Var.name v = "R_ECX") arch_decls
  let edx = List.find (fun v -> Var.name v = "R_EDX") arch_decls
  let esi = List.find (fun v -> Var.name v = "R_ESI") arch_decls
  let edi = List.find (fun v -> Var.name v = "R_EDI") arch_decls
  let zf = List.find (fun v -> Var.name v = "R_ZF") arch_decls
  let flag0 = Ast.Int (Big_int_Z.big_int_of_int 0, Type.Reg 1)
  let imm0 = Ast.Int (Big_int_Z.big_int_of_int 0, Type.Reg 32)
  let imm1 = Ast.Int (Big_int_Z.big_int_of_int 1, Type.Reg 32)
  let imm2 = Ast.Int (Big_int_Z.big_int_of_int 2, Type.Reg 32)
  let imm4 = Ast.Int (Big_int_Z.big_int_of_int 4, Type.Reg 32)
  let imm8 = Ast.Int (Big_int_Z.big_int_of_int 8, Type.Reg 32)
  let immc = Ast.Int (Big_int_Z.big_int_of_int 12, Type.Reg 32)
  let imm0x10 = Ast.Int (Big_int_Z.big_int_of_int 16, Type.Reg 32)
  let imm37 = Ast.Int (Big_int_Z.big_int_of_int 37, Type.Reg 32)
end

module Helpers =
struct
  open Definitions
  let push_int (i, bytes) =
    assert (bytes > 0);
    let typ = Type.Reg (bytes * 8) in
    let immbytes = Ast.Int (Big_int_Z.big_int_of_int bytes, Type.Reg 32) in
    let bi = Big_int_Z.big_int_of_int i in
    [
      Ast.Move (esp, Ast.BinOp (Type.MINUS, Ast.Var esp, immbytes), []);
      Ast.Move (mem, Ast.Store (Ast.Var mem, Ast.Var esp,
                                Ast.Int (bi, typ), Ast.exp_false, typ), []);
    ]

  let push_reg reg =
    assert ((Var.typ reg) = (Type.Reg 32));
    [
      Ast.Move (esp, Ast.BinOp (Type.MINUS, Ast.Var esp, imm4), []);
      Ast.Move (mem, Ast.Store (Ast.Var mem, Ast.Var esp,
                                Ast.Var reg, Ast.exp_false, Type.Reg 32), []);
    ]

  let pop reg =
    assert ((Var.typ reg) = (Type.Reg 32));
    [
      Ast.Move (reg, Ast.Load (Ast.Var mem, Ast.Var esp,
                               Ast.exp_false, Type.Reg 32), []);
      Ast.Move (esp, Ast.BinOp (Type.PLUS, Ast.Var esp, imm4), []);
    ]

  let indexed_load  ~dst ~base ~index ~scale ~disp =
    let immsc = Ast.Int (Big_int_Z.big_int_of_int scale, Type.Reg 32) in
    let temp0 = Disasm_temp.nt "t" Ast.reg_32 in
    let temp1 = Disasm_temp.nt "t" Ast.reg_32 in
    let stmts = [
      Ast.Move (temp0, Ast.BinOp (Type.TIMES, Ast.Var index, immsc), []);
      Ast.Move (temp1, Ast.BinOp (Type.PLUS, Ast.Var base, Ast.Var temp0), []);
    ] in
    let (addr, stmts) =
      if disp = 0 then begin
        (temp1, stmts)
      end else begin
        let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
        let immdisp = Ast.Int (Big_int_Z.big_int_of_int disp, Type.Reg 32) in
        let s = Ast.Move (temp2, Ast.BinOp (Type.PLUS, Ast.Var temp1, immdisp), []) in
        (temp2, List.concat [stmts; [s]])
      end
    in
    let ld = Ast.Move (dst, Ast.Load (Ast.Var mem, Ast.Var addr, Ast.exp_false, Type.Reg 32), []) in
    List.concat [stmts; [ld];]

  let indexed_store ~base ~index ~scale ~disp ~value =
    let immsc = Ast.Int (Big_int_Z.big_int_of_int scale, Type.Reg 32) in
    let temp0 = Disasm_temp.nt "t" Ast.reg_32 in
    let temp1 = Disasm_temp.nt "t" Ast.reg_32 in
    let stmts = [
      Ast.Move (temp0, Ast.BinOp (Type.TIMES, Ast.Var index, immsc), []);
      Ast.Move (temp1, Ast.BinOp (Type.PLUS, Ast.Var base, Ast.Var temp0), []);
    ] in
    let (addr, stmts) =
      if disp = 0 then begin
        (temp1, stmts)
      end else begin
        let temp2 = Disasm_temp.nt "t" Ast.reg_32 in
        let immdisp = Ast.Int (Big_int_Z.big_int_of_int disp, Type.Reg 32) in
        let s = Ast.Move (temp2, Ast.BinOp (Type.PLUS, Ast.Var temp1, immdisp), []) in
        (temp2, List.concat [stmts; [s]])
      end
    in
    let st = Ast.Move (mem, Ast.Store (Ast.Var mem, Ast.Var addr, value, Ast.exp_false, Type.Reg 32), []) in
    List.concat [stmts; [st]]

  let gen_prologue bytes =
    let i = ref 0 in
    let getlab = (fun () ->
      let lab = Printf.sprintf "Prologue%d" !i in
      i := !i + 1;
      Type.Name lab)
    in
    let lab1 = getlab () in
    let lab2 = getlab () in
    let lab3 = getlab () in
    let immbytes = Ast.Int (Big_int_Z.big_int_of_int bytes, Type.Reg 32) in
    [Ast.Label (lab1, [Type.Asm "push %ebp"]);
     Ast.Move (esp, Ast.BinOp (Type.MINUS, Ast.Var esp, imm4), []);
     Ast.Move (mem, Ast.Store(Ast.Var mem, Ast.Var esp, Ast.Var ebp, Ast.exp_false,
                              Type.Reg 32), []);
     Ast.Label (lab2, [Type.Asm "mov %esp, %ebp"]);
     Ast.Move (ebp, Ast.Var esp, []);
     Ast.Label (lab3, [Type.Asm (Printf.sprintf "sub $%d, %%esp" bytes)]);
     Ast.Move (esp, Ast.BinOp (Type.MINUS, Ast.Var esp, immbytes), [])]

  let gen_call target_func_name =
    [Ast.Move (esp, Ast.BinOp (Type.MINUS, Ast.Var esp, imm4), []);
  (* Note: should push the retaddr here, but we don't use it, so... *)
     Ast.Move (mem, Ast.Store (Ast.Var mem, Ast.Var esp, imm0, Ast.exp_false,
                               Type.Reg 32), []);
  (* The address in the attribute is not used *)
     Ast.Jmp (Ast.Lab target_func_name, [Type.StrAttr "call 0x0"])]

  let gen_retn bytes =
  (* local vars to cleanup *)
    let immbytes = Ast.Int (Big_int_Z.big_int_of_int bytes, Type.Reg 32) in
    let ra = Disasm_temp.nt "ra" Ast.reg_32 in
    [
      Ast.Move (esp, Ast.BinOp (Type.PLUS, Ast.Var esp, immbytes), []);
      Ast.Move (ebp, Ast.Load (Ast.Var mem, Ast.Var esp, Ast.exp_false, Type.Reg 32),
                [Type.StrAttr "pop %ebp"]);
      Ast.Move (esp, Ast.BinOp (Type.PLUS, Ast.Var esp, imm4), []);
      Ast.Move (ra, Ast.Load (Ast.Var mem, Ast.Var esp, Ast.exp_false,
                              Type.Reg 32), []);
      Ast.Move (esp, Ast.BinOp (Type.PLUS, Ast.Var esp, imm4), []);
      Ast.Jmp (Ast.Var ra, [Type.StrAttr "ret   "]);
      Ast.Halt (imm1, []);
    ]

  let label_map ast_cfg =
    let htbl = Cfg.AST.G.fold_vertex (fun v acc ->
      let stmts = Cfg.AST.get_stmts ast_cfg v in
      let (_, _, nacc) = List.fold_left (fun (curr_addr, offset, a) s ->
        let ncurr_addr, na = match s with
        | Ast.Label (Type.Addr addr, _) ->
          (Some addr, a)
        | Ast.Label (Type.Name str, _) ->
          let addr =
            try
              BatOption.get(curr_addr)
            with Not_found ->
              failwith "No addr yet!"
          in
          ignore(match Misc.bathashtbl_find_option a str with
          | Some (prev_addr, _) ->
            dprintf "Duplicate label %s at %#Lx (also found at %#Lx)" str addr
              prev_addr;
            failwith "Duplicate mock label!"
          | None ->
            ());
          BatHashtbl.add a str (addr, (Cfg.AST.G.V.label v, offset));
          (curr_addr, a)
        | _ ->
          (curr_addr, a)
        in
        (ncurr_addr, offset + 1, na)
      ) (None, 0, acc) stmts
      in
      nacc
    ) ast_cfg (BatHashtbl.create 10)
    in
    BatHashtbl.find htbl



  let sign_extend typ exp = Ast.Cast (Type.CAST_SIGNED,typ,exp)
  let zero_extend typ exp = Ast.Cast (Type.CAST_UNSIGNED,typ,exp)
  let low ~typ ~exp = Ast.Cast (Type.CAST_LOW,typ,exp)
  let low8 exp = low ~typ:Ast.reg_8 ~exp

  let lab s = Ast.Lab s

  let gen_cjmp ~cond ~if_true ~if_false =
    [Ast.CJmp(cond, if_true, if_false,[])]
  let gen_jmp s = [Ast.Jmp(lab s,[])]

  let gen_load ~dst ~index ~size =
    let load_exp =
      Ast.Load (Ast.Var mem, index, Ast.little_endian, size) in
    let dst_typ = Var.typ dst in
    if Typecheck.bits_of_width dst_typ > Typecheck.bits_of_width size
    then [Ast.Move (dst, zero_extend dst_typ load_exp, [])]
    else [Ast.Move (dst,load_exp,[])]

  let gen_label s = [Ast.Label (Type.Name s, [])]

  let (^=) avar exp = Ast.Move(avar, exp, [])
  let (+!) exp exp' = Ast.BinOp (Type.PLUS, exp, exp')
  let (-!) exp exp' = Ast.BinOp (Type.MINUS, exp, exp')
  let (=!) exp exp' = Ast.BinOp (Type.EQ, exp, exp')
end
