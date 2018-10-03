module D = Debug.Make(struct let name = "Side-effect" and default=`Debug end)
open D

open Ktype.Exceptions

module FuncHashtbl = Function_info.Hashtbl

let ( -| ) f g x = f (g x)

(* XXX: This helper should be put in a suitable module*)
let reg_by_name name= List.find (fun n -> (Var.name n) = name) Asmir.x86_regs
let esp = Ast.Var (reg_by_name "R_ESP")


module Function_summary =
struct
  module Interval = Interval.Address_interval
  type kill =
  | KillReg of Var.t
  | KillStackSlot of Interval.t
  | KillGlobal of Interval.t
  | KillAllRegs
  | KillAllStoresAndGlobals

  type 'a maybe_control_dep = Cfd of 'a | Cfi of 'a

  type cfkill = kill maybe_control_dep

  type t = {name : string; killlist: cfkill list;}

  let box_cfi k = Cfi k
  let unbox_cf = function
    | Cfd k -> k
    | Cfi k -> k

  let unbox_cfis cfs =
    List.fold_left (fun acc cf ->
      match acc with
      | BatResult.Ok l ->
        (match cf with
        | Cfi k -> BatResult.Ok (k :: l)
        | Cfd _ -> BatResult.Bad ())
      | BatResult.Bad () as bad ->
        bad) (BatResult.Ok []) cfs

  let to_string sum =
    let k_to_str = function
      | KillReg v -> Pp.var_to_string v
      | KillStackSlot i -> Printf.sprintf "stack slot %s" (Interval.to_string i)
      | KillGlobal i -> Printf.sprintf "global %s" (Interval.to_string i)
      | KillAllRegs -> "all_regs"
      | KillAllStoresAndGlobals -> "all_stores_and_globals"
    in
    let cf_to_str cf =
      let k, pref = match cf with
      | Cfd k -> (k, "CFD")
      | Cfi k -> (k, "CFI")
      in
      Printf.sprintf "[%s] %s" pref (k_to_str k)
    in
    Printf.sprintf "%s: killlist %s" sum.name
      (Print.list_to_string ~sep:" & " cf_to_str sum.killlist)

  let empty = { name = "empty"; killlist = []; }
  let unknown name = {name;
                      (*
                       * Note: It's the Cfd aspect that matters here and
                       * forces us to not touch a call to an unknown function.
                       * Otherwise, KillAllRegs/KillAllStoresAndGlobals is
                       * incorrect as it is an overapproximation (and we're
                       * not allowed to do that).
                       *)
                      killlist = [Cfd KillAllRegs;
                                  Cfd KillAllStoresAndGlobals]}
  let cdecl name =
    let open BatPervasives in
    let cfi_reg = box_cfi -| (fun v -> KillReg v ) -| reg_by_name in
    let ret_and_caller_saved = ["R_EAX"; "R_ECX"; "R_EDX"] in
    {
      name;
      killlist = box_cfi KillAllStoresAndGlobals ::
        (List.map cfi_reg ret_and_caller_saved);
    }

(*
  XXX: will be resurrected when we start properly summarizing functions again.
  let for_observable stores =
    {
      name = "observable";
      killlist = List.map (fun store ->
        match store with
        | Function.X86.Infinite -> failwith "Can't get here"
        | Function.X86.Kill store ->
        let region = store.Function.X86.region in
        match store.Function.X86.basereg with
        | None -> KillGlobal region
        | Some basereg ->
          (* Currently this is caught earlier, but play it safe. *)
          if (Karch.X86.is_esp basereg) then
            KillStackSlot region
          else
            KillAllStoresAndGlobals
      ) stores;
    }
*)

  let compare_intervals i1 i2 =
    match (Interval.begin_ i1, Interval.begin_ i2) with
    | (None, None) -> 0
    | (Some _, None) -> 1
    | (None, Some _) -> -1
    | (Some low1, Some low2) -> Int64.compare low1 low2

  let minimalize_kill_list kl =
    let has_allregs, has_allmem = List.fold_left (fun (ar, am) k ->
      match unbox_cf k with
      | KillAllRegs -> (true, am)
      | KillAllStoresAndGlobals -> (ar, true)
      | _ -> (ar, am)) (false, false) kl
    in
    List.filter (fun k ->
      match unbox_cf k with
      | KillStackSlot _ -> not has_allmem
      | KillGlobal _ -> not has_allmem
      | KillReg _ -> not has_allregs
      | _ -> true) kl

  let minimalize t = {t with killlist = minimalize_kill_list t.killlist}

  let normalize_kill_list = List.sort compare
  let normalize t = {t with killlist = normalize_kill_list t.killlist}

  let sexp_of_t t =
    let open Sexplib in
    let name = Sexp.of_string t.name in
    let t = normalize (minimalize t) in
    let sexp_of_kill = function
      | KillStackSlot x ->
        Sexp.List [Sexp.of_string "SS"; Interval.sexp_of_t x]
      | KillReg r ->
        Sexp.List [Sexp.of_string "REG"; Sexp.of_string (Var.name r)]
      | KillGlobal region ->
        Sexp.List [Sexp.of_string "GLOBAL"; Interval.sexp_of_t region]
      | KillAllRegs ->
        Sexp.of_string "ALLREGS"
      | KillAllStoresAndGlobals ->
        Sexp.of_string "ALLMEM"
    in
    let sexp_of_cf cf =
      let str, k = match cf with
      | Cfd k -> ("CFD", k)
      | Cfi k -> ("CFI", k)
      in
      Sexp.List [Sexp.of_string str; sexp_of_kill k]
    in
    let sexps = List.map sexp_of_cf t.killlist in
    Sexp.List (name :: sexps)
  let equal {killlist = kl1} {killlist = kl2} =
    let compare_kills k1 k2 =
      match k1 with
      | KillAllStoresAndGlobals ->
        (match k2 with
        | KillAllStoresAndGlobals -> 0
        | _ -> -1)
      | KillAllRegs ->
        (match k2 with
        | KillAllStoresAndGlobals -> 1
        | KillAllRegs -> 0
        | _ -> -1)
      | KillGlobal i1 ->
        (match k2 with
        | KillAllStoresAndGlobals
        | KillAllRegs -> 1
        | KillGlobal i2 -> compare_intervals i1 i2
        | _ -> -1)
      | KillStackSlot i1 ->
        (match k2 with
        | KillAllStoresAndGlobals
        | KillAllRegs
        | KillGlobal _ -> 1
        | KillStackSlot i2 -> compare_intervals i1 i2
        | KillReg _ -> -1)
      | KillReg v1 ->
        (match k2 with
        | KillAllStoresAndGlobals
        | KillAllRegs
        | KillGlobal _
        | KillStackSlot _ -> 1
        | KillReg v2 -> Var.compare v1 v2)
    in
    let compare cf1 cf2 =
      match cf1, cf2 with
      | Cfd _, Cfi _ -> -1
      | Cfi _, Cfd _ -> 1
      | Cfd k1, Cfd k2
      | Cfi k1, Cfi k2 -> compare_kills k1 k2
    in
    let kl1, kl2 = (List.sort compare kl1, List.sort compare kl2) in
    try
      BatList.fold_left2 (fun acc k1 k2 ->
        match acc with
        | false -> acc
        | true -> 0 = (compare k1 k2)) true kl1 kl2
    with Invalid_argument _ -> false

  let join name t t' =
    let nt = {
      name;
      killlist = BatList.unique (t.killlist @ t'.killlist);
    } in
    normalize (minimalize nt)

  let merge name sum1 sum2 =
    let kl_partition =
      BatList.partition (fun cf ->
        match cf with
        | Cfd _ -> true
        | Cfi _ -> false)
    in
    let merge_kill_lists kl1 kl2 =
      let kl = BatList.unique (kl1 @ kl2) in
      normalize_kill_list (minimalize_kill_list kl)
    in
    let kl1_cfd, kl1_cfi = kl_partition sum1.killlist in
    let kl2_cfd, kl2_cfi = kl_partition sum2.killlist in
    let kl_cfd = merge_kill_lists kl1_cfd kl2_cfd in
    let kl_cfi = merge_kill_lists kl1_cfi kl2_cfi in
    dprintf "merge\n%s\n%s" (to_string sum1) (to_string sum2);
    {
      name;
      killlist = kl_cfd @ kl_cfi;
    }

  let remove_var t to_remove =
    let kl' = List.filter (fun cf ->
      match unbox_cf cf with
      | KillReg v -> not (Var.equal v to_remove)
      | _ -> true) t.killlist
    in
    {t with killlist = kl'}

(*
  let remove_stackslots_and_regs summary =
    let kl' = List.filter (function
      | KillStackSlot _
      | KillReg _ -> false
      | _ -> true) summary.killlist
    in
    {summary with killlist = kl'}
*)
(*
  let merge_callees callees =
    let callees = List.map (fun sum ->
      remove_stackslots_and_regs sum) callees in
    match callees with
    | [] ->
      empty
    | single_callee :: [] ->
      single_callee
    | callees ->
      BatList.reduce (fun acc sum ->
        merge "callees" acc sum) callees
*)
end

type reachable_load = {
  rl_typ: Type.typ;
  rl_addr: Type.addr option;
  rl_bbid: Cfg.bbid;
  (*
   * This is the offset of the load in the notional array of just
   * the load statements in the BB. We use the (bbid, load_offset)
   * pair to lookup the information about what is actually loaded
   * which is provided by one of our oracle functions. We cannot
   * really use the address of the instruction for that, as there
   * could be BBs w/o an address that do loads (e.g. BBs generated
   * by a rep prefix to an x86 instruction).
   *)
  rl_load_offset: int;
}

let reachable_load_to_string rl =
  let addr = BatOption.map_default (Printf.sprintf "%#Lx" ) "unknown"
    rl.rl_addr
  in
  Printf.sprintf "(@%s, (%s, %d))" addr (Cfg.bbid_to_string rl.rl_bbid)
    rl.rl_load_offset

module Reachable_load_set = BatSet.Make(
  struct
    type t = reachable_load
    let compare rl1 rl2 =
      let cmp_bbid a b =
        let open Cfg in
        let to_num = function
        | BB_Entry -> -4
        | BB_Exit -> -3
        | BB_Indirect -> -2
        | BB_Error -> -1
        | BB n ->
          (* The above mapping assumes n is always >= 0 *)
          assert (n >= 0);
          n
        in
        (to_num a) - (to_num b)
      in
      let diff = cmp_bbid rl1.rl_bbid rl2.rl_bbid in
      match diff with
      | 0 -> rl1.rl_load_offset - rl2.rl_load_offset
      | _ -> diff
  end)

let reachable_load_set_to_string rload_set =
  let e = Reachable_load_set.enum rload_set in
  Print.enum_to_string ~enclosing:("[", "]") reachable_load_to_string e

(*
  XXX: DANGER. we should be making sure that stack variables are
  only ever accessed through ESP, right? This should be handled alright
  in the SSA arrays, but we're being simplistic here.
*)
let augmented_loads_in_stmts stmts_with_addr =
  let (_, ret) = List.fold_left (fun (load_idx, acc) (maybe_addr, s) ->
    let was_load, nacc = match s with
    | Ast.Move (_, Ast.Load (mem, idx, _, width), _) ->
      true, (width, maybe_addr, load_idx) :: acc
    | _ ->
      false, acc
    in
    let load_idx = match was_load with
      | true -> load_idx + 1
      | false -> load_idx
    in
    (load_idx, nacc)) (0, []) stmts_with_addr
  in
  ret

let compute_reachable_loads cfg =
  let module Analysis =
  struct
    module C = Cfg.AST
    type vertex = C.G.V.t
    type edge = C.G.E.t
    type g = C.G.t
    type data = Reachable_load_set.t option
    let direction = Fixpoint.Backward
    let equal = (=)
    let join a b =
      match a, b with
      | Some a, Some b ->
        Some (Reachable_load_set.union a b)
      | Some x, None
      | None, Some x ->
        Some x
      | None, None ->
        failwith "umm what?"
    let analyze e r_in =
      let next_v = C.G.E.src e in
      let lab = C.G.V.label next_v in
      let stmts = Cfg.AST.get_stmts cfg next_v in
      let stmts_waddr = Misc.stmts_with_addrs stmts in
      let aug_loads = augmented_loads_in_stmts stmts_waddr in
      let rloads = List.map (fun (w, addr, loff) ->
        {
          rl_typ = w;
          rl_addr = addr;
          rl_bbid = lab;
          rl_load_offset = loff;
        }) aug_loads in
      let n = Reachable_load_set.of_enum (BatList.enum rloads) in
      match r_in with
      | None ->
        Some n
      | Some r_in ->
        Some (Reachable_load_set.union n r_in)
  end
  in
  let module FP = Fixpoint.Make(Cfg.AST.G)(Analysis) in
  let oracle query_v =
    let initial v =
      match Cfg.AST.G.out_degree cfg v = 0 with
      | true -> Some Reachable_load_set.empty
      | false -> None
    in
    FP.analyze initial cfg query_v
  in
  oracle

(* loc is a 0-based offset of a statement within the BB *)
let reachable_loads_at oracle cfg bbid loc =
  let module C = Cfg.AST in
  let loads_from_succs v =
    let succs = C.G.succ cfg v in
    let rloads = List.map (fun succ ->
      BatOption.get (oracle succ)) succs
    in
    BatList.reduce Reachable_load_set.union rloads
  in
  let v =
    try
      C.find_vertex cfg bbid
    with Not_found -> failwith "requested non-existing vertex"
  in

  let stmts = C.get_stmts cfg v in
  let nr_stmts = List.length stmts in
  (* Statements within the same BB that follow the target statement *)
  let rem = BatList.take (nr_stmts - loc - 1) (List.rev stmts) in
  let rem_waddr = Misc.stmts_with_addrs rem in
  let aug_loads = augmented_loads_in_stmts rem_waddr in
  let rloads = List.map (fun (w, addr, loff) ->
    {
      rl_typ = w;
      rl_addr = addr;
      rl_bbid = bbid;
      rl_load_offset = loff;
    }) aug_loads in
  let local_rloads = Reachable_load_set.of_enum (BatList.enum rloads) in
  let nonlocal_rloads = loads_from_succs v in
  Reachable_load_set.union local_rloads nonlocal_rloads

(* XXX hard-coded arch *)
let default_pass_ctx = Analysis_pass.default_pipeline_ctx

let getfunc = function
  | Function_info.Function f -> f
  | f -> failwith (Printf.sprintf "getfunc: %s" (Function_info.to_string f))

let ast_cfg_to_ssa_cfg func ?(keypref=None) ast_cfg pipeline_ctx =
  let open Analysis_pass in
  let pipeline_name = "sideeffects-pipeline" in
  let passes = List.map make_pass [
    `BapSsaSimplifications1;
    `DropNopBBs1;
    `ComputeDataDependencies;
    `ComputeFunctionInputs;
    `RewriteLoadStores;
  ] in
  let keypref = BatOption.map (fun p ->
    Printf.sprintf "%s/%s/%s" p (Analysis_pass.fdir (getfunc func)) pipeline_name) keypref
  in
  let fnames = (Function_info.symbols_to_str func) in
  let _,cfg = List.fold_left (fun (ctx,cfg) pass ->
      apply_ssa_cfg_pass ~pipeline_name ctx fnames ~keypref cfg pass)
      (pipeline_ctx, Cfg_ssa.of_astcfg ast_cfg) passes in
  cfg

let should_touch f =
  match f with
  | Function_info.Function _ ->
    let fnames = Function_info.symbols f in
    let confusing =
      if Function_info.has_attr f (Func_attr.Confusing "") then
        ["Confusing"]
      else
        []
    in
    let blacklisted =
      if List.exists Symbols.sym_is_blacklist fnames then
        ["Blacklisted"]
      else
        []
    in
    let wb =
      if Function_info.has_attr f Func_attr.WellBehaved then
        []
      else
        ["Not WellBehaved"]
    in
    let reasons = confusing @ blacklisted @ wb in
    begin
      match reasons with
      | [] ->
        BatResult.Ok ()
      | reasons ->
        let str = Print.list_to_string ~enclosing:("", "")
            ~sep:"&&" (fun x -> x) reasons
        in
        BatResult.Bad str
    end
  | _ -> failwith "can't get here"

let calculate_initial_function_summary f =
  let fnames = Function_info.symbols_to_str f in
  dprintf "calculate_initial_function_summary %s" (Function_info.to_string f);
  let summarize_well_behaved ast_cfg =
    (*
     * TBD: actually summarize. For now, we pretend there's
     * not much we can do. Need to be looking at control-flow-
     * dependent stores and so on.
     *)
    Function_summary.unknown fnames
  in
  match f with
  | Function_info.Unknown _ ->Function_summary.unknown fnames
  | Function_info.Indirect -> Function_summary.unknown fnames
  | Function_info.ExternalFunction _ -> Function_summary.cdecl fnames
  | Function_info.Function func as f ->
    let ast_cfg = BatOption.get (Function_info.astcfg f) in
    match should_touch f with
    | BatResult.Ok () ->
      summarize_well_behaved ast_cfg
    | BatResult.Bad _ ->
      Function_summary.unknown fnames

let function_call_sites cg f =
  let call_sites = BatHashtbl.create (Callgraph.Callgraph.out_degree cg f) in
  Callgraph.Callgraph.iter_succ_e (fun call_site ->
    let callee = Callgraph.Callgraph.E.dst call_site in
    let _, {Callgraph.call_site = addr}, _ = call_site in
    BatHashtbl.add call_sites addr callee) cg f;
  call_sites

let get_bounds region =
  let module Interval = Interval.Address_interval in
  match (Interval.begin_ region,
         Interval.end_ region) with
  | Some l, Some h -> (l, h)
  | _ -> failwith "can't get here"

type oracle = {
  summary_for_func: Function_info.t -> Function_summary.t;
  reachable_loads_at: Cfg.bbid -> int -> Reachable_load_set.t;
  stackheight_at: Type.addr -> int option option;
  descr_for_load: (Cfg.bbid * int) -> Function.X86.kill_descr option option;
}

let kill_var v =
  let killer_var = Ast.Var (Var.newvar "K_undefined" (Var.typ v)) in
  Ast.Move (v, killer_var, [Type.Liveout; Type.Synthetic])

let kill_mem idx width =
  let mem = Disasm_i386.mem in
  let bits = width * 8 in
  let value = Ast.Var (Var.newvar "K_undefined" (Type.Reg bits)) in
  let edn = Ast.little_endian in
  let store = Ast.Store (Ast.Var mem, idx, value, edn, Type.Reg bits) in
  let lhs = mem in
  Ast.Move (lhs, store, [Type.Liveout; Type.Synthetic])


exception Could_not_track_reachable_load of reachable_load

let kill_reachable_load oracle stackheight rl acc =
  let open Function.X86 in
  let descr = match oracle.descr_for_load (rl.rl_bbid, rl.rl_load_offset) with
    | None ->
      dprintf "Internal error: no load for (%s, %d)"
        (Cfg.bbid_to_string rl.rl_bbid) rl.rl_load_offset;
      raise (Could_not_track_reachable_load rl)
    | Some d -> d
  in
  let descr = match descr with
    | Some d ->
      d
    | None ->
      raise (Could_not_track_reachable_load rl)
  in
  let res = match descr.basereg with
    | None -> (* Global *)
      let low, high = get_bounds descr.region in
      (* +1 cause bounds are inclusive *)
      let width = Int64.to_int (Int64.add (Int64.sub high low) Int64.one) in
      assert (width = (Typecheck.bytes_of_width rl.rl_typ));
      let idx = Ast.Int (Big_int_Z.big_int_of_int64 low, Ast.reg_32) in
      BatResult.Ok [kill_mem idx width]
    | Some reg when Karch.X86.is_stack_reg reg ->
      (*
       * OK, so. We have here a load of a stack location. The offset
       * is based on entry_esp. However, the value of esp at our
       * current location (i.e. at the call site) might very well
       * be different (very likely, when arguments are passed on
       * the stack). Therefore, we need to add the current (negative)
       * stackheight to the base offset.
       *)
      let low, high = get_bounds descr.region in
      (* +1 cause bounds are inclusive *)
      let width = Int64.to_int (Int64.add (Int64.sub high low) Int64.one)in
      let rl_width = Typecheck.bytes_of_width rl.rl_typ in
      if width <> rl_width then begin
        dprintf "widths differ: region has width %d, rl %s has width %d"
          width (reachable_load_to_string rl) rl_width
      end;
      let offset = Int64.add low (Int64.of_int stackheight) in
      let taddr = Disasm_temp.nt "kill_addr" Ast.reg_32 in
      let immoff = Ast.Int (Big_int_Z.big_int_of_int64 offset, Type.Reg 32) in
      let s_addr_calc = Ast.Move (taddr,
                                  Ast.BinOp (Type.MINUS, Ast.Var reg,
                                             immoff),
                                  [Type.Synthetic])
      in
      let mem = Disasm_i386.mem in
      let undef = Var.newvar "K_undefined" rl.rl_typ in
      let s_kill = Ast.Move (mem, Ast.Store (Ast.Var mem, Ast.Var taddr,
                                             Ast.Var undef, Ast.exp_false,
                                             rl.rl_typ), [Type.Synthetic])
      in
      BatResult.Ok [s_addr_calc; s_kill]
    | _ -> BatResult.Bad ()
  in
  match res with
  | BatResult.Ok kstmts ->
    kstmts @ acc
  | BatResult.Bad () -> failwith "TBD: add spoonful of grace here"

let cfkill_to_stmts oracle curr_addr bbidoff cfkill =
  let do_cfi k =
    let open Function_summary in
    match k with
    | KillReg v ->
      [kill_var v]
    | KillStackSlot region ->
      let open Ast_convenience in
      let low, high = get_bounds region in
      let width = Int64.to_int (Int64.sub high low) in
      let offset = Ast.Int (Big_int_Z.big_int_of_int64 low, Ast.reg_32) in
      let idx = esp +* offset in
      [kill_mem idx width]
    | KillGlobal region ->
      let low, high = get_bounds region in
      let width = Int64.to_int (Int64.sub high low) in
      let idx = Ast.Int (Big_int_Z.big_int_of_int64 low, Ast.reg_32) in
      [kill_mem idx width]
    | KillAllRegs ->
      failwith "KillAllRegs should be removed"
    | KillAllStoresAndGlobals ->
      let stackheight = match oracle.stackheight_at curr_addr with
        | Some h ->
          (match h with
          | None ->
            let str = Printf.sprintf "Stackheight @%#Lx is indeterminate"
              curr_addr
            in
            failwith str
          | Some h ->
            h)
        | None ->
          let str = Printf.sprintf "Couldn't get stackheight @%#Lx" curr_addr in
          failwith str
      in
      let bbid, off = bbidoff in
      let reachable_loads = oracle.reachable_loads_at bbid off in
      dprintf "Reachable loads from call @%#Lx: %s" curr_addr
        (reachable_load_set_to_string reachable_loads);
      Reachable_load_set.fold (kill_reachable_load oracle stackheight)
        reachable_loads []
  in
  match cfkill with
  | Function_summary.Cfd _ ->
    (* XXX: need to bail gracefully here *)
    BatResult.Bad "CFD kill!"
  | Function_summary.Cfi k ->
    BatResult.Ok (do_cfi k)

exception Bad of string
let gen_summary_stmts oracle curr_addr bbidoff summary =
  try
    BatResult.Ok (List.fold_left
                 (fun acc cfkill ->
                  match cfkill_to_stmts oracle curr_addr bbidoff cfkill with
                    (* XXX Shouldn't this be acc @ stmts? *)
                  | BatResult.Ok stmts -> stmts @ acc
                  | BatResult.Bad reason -> raise (Bad reason))
                 [] summary.Function_summary.killlist)
  with Bad reason -> BatResult.Bad reason

let summarize_call_at_bb oracle call_sites cfg v =
  let stmts = Cfg.AST.get_stmts cfg v in
  match Bb.get_bbbounds_from_ast stmts with
  | None ->
    (* No address means no calls *)
    BatResult.Ok None
  | Some (_, high) ->
    (match Misc.bathashtbl_find_option call_sites high with
    | None ->
      (*
       * BB does not include a call (remember, we forcibly split up
       * BBs after calls, so calls only appear at the end of a BB).
       * In this case, there's nothing to do.
       *)
      BatResult.Ok None
    | Some target ->
      assert(match target with
      | Function_info.Function _
      | Function_info.ExternalFunction _ -> true
      | _ ->
        dprintf "Trying to summarize call to %s" (Function_info.to_string target);
        false);
      let curr_addr = high in
      let target_summary = oracle.summary_for_func target in
      let bbid = Cfg.AST.G.V.label v in
      let off = List.length stmts - 1 in
      (match gen_summary_stmts oracle curr_addr (bbid, off) target_summary with
       | BatResult.Ok stmts -> BatResult.Ok (Some stmts)
       | BatResult.Bad reason -> BatResult.Bad reason ))

let maybe_do_bb oracle call_sites cfg v =
  let succ_e = Cfg.AST.G.succ_e cfg v in
  let module V = Cfg.AST.G.V in
  let module E = Cfg.AST.G.E in
  match succ_e with
  | [e] ->
    (*
     * Only bother looking at BBs w/ fall-through edges, that
     * do not point to BB_Error (if the edge points to BB_Error,
     * it most likely means the current BB ends with a call to
     * a function we can't handle).
     *)
    if (None = E.label e) &&
      ((V.label (E.dst e)) <> Cfg.BB_Error) then
      summarize_call_at_bb oracle call_sites cfg v
    else
      BatResult.Ok None
  | _ ->
    BatResult.Ok None

let replace_vertex_with_bb_error cfg v =
  let module C = Cfg.AST in
  let module G = C.G in
  let preds_e = G.pred_e cfg v in
  let cfg = List.fold_left (fun acc e ->
    C.remove_edge_e cfg e) cfg preds_e in
  let succs_e = G.succ_e cfg v in
  let cfg = List.fold_left (fun acc e ->
    C.remove_edge_e cfg e) cfg succs_e in
  let cfg = C.remove_vertex cfg v in
  let cfg, bberr = Cfg_ast.find_error cfg in
  List.fold_left (fun acc e ->
    C.add_edge_e acc (G.E.create (G.E.src e) (G.E.label e) bberr)) cfg preds_e

let do_summarize ~keypref oracle cg f pipeline_ctx =
  let module C = Cfg.AST in
  let ast_cfg = match Function_info.astcfg f with
    | Some cfg -> cfg
    | None -> failwith "Internal error: no cfg"
  in
  let call_sites = function_call_sites cg f in
  let req_addrs = BatList.of_enum (BatHashtbl.keys call_sites) in
  let stackheight_at = Function.X86.calc_stack_height_at_addrs ast_cfg
    req_addrs
  in
  let incorrect_ssa_cfg = ast_cfg_to_ssa_cfg ~keypref f ast_cfg pipeline_ctx in
  let descr_for_load = Function.X86.compute_load_info incorrect_ssa_cfg in
  let oracle = {oracle with stackheight_at; descr_for_load} in
  let ast_cfg = C.G.fold_vertex (fun v ng ->
    try
      (match maybe_do_bb oracle call_sites ng v with
       | BatResult.Ok res ->
          (match res with
           | None ->
              ng
           | Some append_stmts ->
              let stmts = C.get_stmts ng v in
              let stmts = stmts @ append_stmts in
              C.set_stmts ng v stmts)
       | BatResult.Bad reason->
          dprintf "Linking %s (%s) to BB_Error because %s"
                          (Cfg.AST.v2s v) (Function_info.to_string f) reason;
          replace_vertex_with_bb_error ng v)
    with Could_not_track_reachable_load rl ->
      let fdescr = Function_info.to_string f in
      dprintf "Function %s: Linking %s (%s) to BB_Error (unable to summarize \
               the call because we couldn't track the reachable load %s)"
        fdescr (Cfg.AST.v2s v) (Function_info.to_string f)
        (reachable_load_to_string rl);
      (* Can't handle this BB then :( *)
      replace_vertex_with_bb_error ng v
  ) ast_cfg ast_cfg
  in
  ignore(match keypref with
  | None -> ()
  | Some keypref ->
    let key = Printf.sprintf "%s/after-summarize-calls.ast.dot" keypref in
    Outdir.with_file_out key (fun oc ->
    Graph_dump.output_ast oc ast_cfg));
  Function_info.set_astcfg f ast_cfg

let summarize_calls_for_func ~keypref summary_for_func cg f pipeline_ctx =
  let fdescr = Function_info.to_string f in
  dprintf "summarize_calls_for_func for %s" fdescr;
  match Function_info.astcfg f with
  | Some ast_cfg ->
    begin
      match should_touch f with
      | BatResult.Ok () ->
        (try
           ignore(Cfg.AST.find_vertex ast_cfg Cfg.BB_Indirect);
           failwith "got BB_Indirect"
         with Not_found -> ());
        let bb_rloads_in = compute_reachable_loads ast_cfg in
        let oracle = {
          summary_for_func;
          reachable_loads_at = reachable_loads_at bb_rloads_in ast_cfg;
          stackheight_at = (fun _ -> failwith "stackheight_at not available yet");
          descr_for_load = (fun _ -> failwith "descr_for_load not available yet");
        } in
        do_summarize ~keypref oracle cg f pipeline_ctx
      | BatResult.Bad reasons  ->
        dprintf "Function %s is %s" fdescr reasons;
        f
    end
  | None ->
    dprintf "Function %s has no statements" fdescr;
    f

let do_update_stackheight fi cg_acc =
  let module C = Callgraph in
  let module CG = Callgraph.Callgraph in
  let succ_e = CG.succ_e cg_acc fi in
  let reqaddrs = List.map (fun e ->
      (CG.E.label e).C.call_site) succ_e
  in
  let height_at = match Function_info.astcfg fi with
    | None -> (fun (_ : Type.addr) -> None)
    | Some astcfg ->
      let resp = Function.X86.calc_stack_height_at_addrs astcfg reqaddrs in
      let get addr = match resp addr with
        | None ->
          let str = Printf.sprintf "Couldn't calculate stackheight at %#Lx"
              addr
          in
          failwith str
        | Some None ->
          None
        | Some (Some d) ->
          Some (Int64.of_int d)
      in
      get
  in
  List.fold_left (fun nacc e ->
      let lab = CG.E.label e in
      let src, dst = CG.E.src e, CG.E.dst e in
      let temp_cg = CG.remove_edge_e nacc e in
      assert (lab.C.stack_height = None);
      let sh = height_at lab.C.call_site in
      let nlab = {lab with C.stack_height = sh} in
      CG.add_edge_e temp_cg (CG.E.create src nlab dst)
    ) cg_acc succ_e

let update_stackheights cg =
  Analysis_pass.fold_vertex (fun fi cg_acc ->
      match fi with
      | Function_info.Function _ when not (Function_info.has_attr fi (Func_attr.Confusing "")) ->
        do_update_stackheight fi cg_acc
      | _ ->
        cg_acc
    ) cg cg

let calculate_well_behaved cg =
  let cg = update_stackheights cg in
  Analysis_pass.map_vertex (fun fi ->
    match Function_info.astcfg fi with
    | None -> fi
    | Some ast_cfg ->
      let fdescr = Function_info.to_string fi in
      if (not (Function_info.has_attr fi (Func_attr.Confusing ""))) &&
        Function.X86.is_well_behaved fdescr ast_cfg then
        Function_info.set_attr fi Func_attr.WellBehaved
      else
        fi) cg

let fixed_point_summaries cg =
  let cg, out = Callgraph.add_out_node cg in
  (*
   * We add a dummy out node, but to kickstart the dataflow analysis,
   * it needs to have some value other than L.top. So add a dummy
   * KillReg for this variable and filter it out from the final
   * summaries.
   *)
  let dummy_outv = Disasm_temp.nt "summary_dummy" Ast.reg_32 in
  let module DF =
  struct
    module L =
    struct
      type t = Function_summary.t
      let top = Function_summary.empty
      let meet a b =
        let an = a.Function_summary.name in
        let bn = b.Function_summary.name in
        dprintf "FPS.meet %s %s" an bn;
        Function_summary.merge (Printf.sprintf "(%s & %s)" an bn) a b
      let equal = Function_summary.equal
    end
    module G = Callgraph.Callgraph
    let s0 _ = out
    let init _ = L.top
    let dir = GraphDataflow.Backward

    let transfer_function cg fi from_callee =
      let fnames = Function_info.symbols_to_str fi in
      let gen = match fi = out with
        | true -> {
          Function_summary.name = "out_node";
          Function_summary.killlist = [Function_summary.Cfi
                                          (Function_summary.KillReg dummy_outv)]
        }
        | false -> calculate_initial_function_summary fi
      in
      dprintf "FPS.merge into %s" fnames;
      Function_summary.merge (Printf.sprintf "(%s & callee)" fnames)
        gen from_callee
  end
  in
  let module Dataflow = GraphDataflow.Make(DF) in
  let incoming, outgoing = Dataflow.worklist_iterate cg in
  let unwrap = (fun sum -> Function_summary.remove_var sum dummy_outv)  in
  (fun x ->
    let res = outgoing x in
    unwrap res)

let calculate_function_summaries ~func_filter cg =
  let func_filter = match Options.summarize_calls with
    | Options.CallSumCdecl ->
      (* In this case, we don't really need the summaries, we're only called
       * to calculate the final stack height, which determines the WellBehaved
       * attribute. Therefore, we only need look at the functions the caller
       * cares about.
      *)
      func_filter
    | Options.CallSumCalculate ->
      (* Here we need to have all function summaries *)
      (fun _ -> true )
  in
  let cg = calculate_well_behaved cg in
  let module FuncHashtbl = Function_info.Hashtbl in
  let htbl = FuncHashtbl.create (Callgraph.Callgraph.nb_vertex cg) in
  Callgraph.Callgraph.iter_vertex (fun fi ->
    let summary = match Options.summarize_calls with
      | Options.CallSumCalculate ->
        (*
         * XXX: We're taking a huge shortcut here. We don't dare touch calls to
         * observable functions yet, so the summary for all those is unknown,
         * which we can't handle. Hence, there's no need to propagate summaries.
         * For cdecl functions, we always generate a more useful summary, but
         * those are always leaves in the callgraph, so again, no need to
         * propagate to the non-leaf nodes (which are observable functions).
         *)
        calculate_initial_function_summary fi
      | Options.CallSumCdecl ->
        Function_summary.cdecl "forced"
    in
    FuncHashtbl.add htbl fi summary;
    dprintf "Final summary (%s): %s"
      (Function_info.to_string fi)
      (Function_summary.to_string summary)) cg;
  let summary_for_func fi =
    match FuncHashtbl.find_option htbl fi with
    | Some summary ->
      summary
    | None ->
      let str = Printf.sprintf "Could not get summary for %s"
        (Function_info.to_string fi) in
      failwith str
  in
  (cg, summary_for_func)

let summarize_calls ~func_filter ~keypref cg state =
  let (cg, sff) = calculate_function_summaries ~func_filter cg in
  let do_all () =
    Analysis_pass.map_vertex (fun func ->
        if func_filter func then begin
          try
            begin
              match FuncHashtbl.find state func with
              | Some pipeline_ctx when func_filter func ->
                let do_func () =
                  summarize_calls_for_func ~keypref sff cg func pipeline_ctx
                in
                let b = new Perfacc.bench "summarize_calls_ff" in
                b#start (Function_info.to_string func);
                Misc.finally b#stop do_func ()
              | _ ->
                func
            end
          with Confusing_function str ->
            (*
             * This might happen b/c we run our own side-pipeline
             * manually here. The function will be declared confusing
             * later anyway, don't bother with summarizing the calls
            *)
            dprintf "summarize_calls: %s turned out to be Confusing"
              (Function_info.to_string func);
            func
        end else
          func
      ) cg
  in
  let b = new Perfacc.bench "summarize_calls" in
  b#start "nada";
  Misc.finally b#stop do_all ()
