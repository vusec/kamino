module D = Debug.Make(struct let name = "Load_store_analysis" and default=`Debug end)
open D

open Ssa
open Ktype.Exceptions
open Misc.Pervasives
open Crappy_vsa

module C = Cfg.SSA
module G = C.G

module Helpers = Analysis_helpers.SSA
module Sinkpath = Memory_region_analysis.Sinkpath

type arrayfication_ctx = {
  (* baseptr -> [((low, high), ary); ((low, high), ary); ...] *)
  base2array : (((Int64.t * Int64.t) * Var.t) list) Var.VarMap.t;
    (*
     * The following mapping keeps tabs on which mems are replace by arrays.
     * This is required to determine which phis to remove that are found to be
     * defined by arrays in the translation from AST with arrays to SSA form.
     *)
  mem2ary : (Ssa.value, Var.t) BatMap.t;
}
module SinkTbl = BatHashtbl.Make(Var)

let memr2arrays memr =
  let module VM = Var.VarMap in
  Memrange.fold_pointers (fun var map ->
      (* For each base variable (region) ... *)
      let intvls = Memrange.fold_intervals (fun acc (l, h) ->
          let Var.V (vidx, vname, vtyp) = var in
          let vtyp = Pp.typ_to_string vtyp in
          let name = Printf.sprintf "ary_%s_%d:%s_f%Ldt%Ld" vname vidx vtyp l h in
          let ary = Var.newvar name (Type.Array (Type.Reg 32, Type.Reg 8)) in
          ((l, h), ary) :: acc
        ) [] memr var in
      VM.add var intvls map
    ) (VM.empty) memr

let lookup_ary map base ~low ~high =
  let open Big_int_Z in
  let lookup_intvls =
    try
      Var.VarMap.find base map
    with Not_found ->
      failwith (Printf.sprintf "Couldn't find ary for base %s" (Pp.var_to_string base))
  in
  let intervals = lookup_intvls in
  try
    BatList.find_map (fun ((l, h), ary) ->
        let l = big_int_of_int64 l in
        let h = big_int_of_int64 h in
        let open Big_int_convenience in
        if (low >=% l) && (low <=% h) then begin
          if high >% h then begin
            let bi2s = string_of_big_int in
            let str =
              Printf.sprintf "High offset off access [%s, %s] extends \
                              outside recovered interval [%s, %s]" (bi2s low) (bi2s high)
                (bi2s l) (bi2s h)
            in
            failwith str
          end;
          Some ary
        end else
          None) intervals
  with Not_found ->
    Printf.eprintf "Couldn't get interval for [%s, %s] in %s"
      (string_of_big_int low) (string_of_big_int high)
      (Var.name base);
    failwith "No interval for offset"

let rewrite_stmt_ptrs vsa_info cfg sinktbl stmts =
  dprintf "rewrite_stmt_ptrs";
  let maybe_calc mem idx =
    if Var.typ idx <> Type.Reg 32 then begin
      failwith "Memory index not 32-bits wide!"
    end;
    match Var.typ mem with
    | Type.Reg _ ->
      failwith "mem is Reg?!"
    | Type.Array _ ->
      (* Usually TLS accesses get translated using arrays. TBD *)
      raise (Confusing_function "Has own arrays")
    | Type.TMem _ ->
        (*
         * Change Load (mem, idx) to
         *
         * t1 = idx - base
         * Load (mem, idx)
         *
         * so that we can do VSA on t1 to deduce the array bounds.
         *)
      begin
        let module Sinkpath = Memory_region_analysis.Sinkpath in
        match Memory_region_analysis.sinkpaths_for_var vsa_info cfg idx with
        | [sinkpath]
          when Karch.X86.is_stack_reg (Sinkpath.sink sinkpath) ->
          dprintf "sinkpath_for_var %s = %s" (Pp.var_to_string idx) (Sinkpath.to_string sinkpath);
          let base = Sinkpath.sink sinkpath in
          SinkTbl.add sinktbl idx sinkpath;
          begin
            let t1 = Disasm_temp.nt "index_for_vsa" Ast.reg_32 in
            let exp = Ssa.BinOp (Type.MINUS, Ssa.Var idx, Ssa.Var base) in
            let attrs = [Type.Synthetic; Type.StrAttr "index_for_vsa"] in
            let calc = Ssa.Move (t1, exp, attrs) in
            dprintf "Will prepend %s" (Pp.ssa_stmt_to_string calc);
            [calc]
          end
        | _ ->
          []
      end
  in
  let to_prepend stmt =
    dprintf "to_prepend: looking at %s" (Pp.ssa_stmt_to_string stmt);
    match stmt with
    | Ssa.Move (_, Ssa.Load (_, Ssa.Lab _, _, _), _) ->
      failwith "Label in Load"
    | Ssa.Move (_, Ssa.Store (_, Ssa.Lab _, _, e, typ), _) ->
      failwith "Label in Store"
    | Ssa.Move (_, Ssa.Load (mem, Ssa.Var idx, _, _), _)
    | Ssa.Move (_, Ssa.Store (mem, Ssa.Var idx, _, _, _), _) ->
      begin
        match mem with
        | Ssa.Var mem ->
          stmt :: (maybe_calc mem idx)
        | _ ->
          failwith "mem is not a variable"
      end
    | _ ->
      [stmt]
  in
  let rev_stmts = List.fold_left (fun rev_stmts stmt ->
      (to_prepend stmt) @ rev_stmts) [] stmts in
  List.rev rev_stmts

let rewrite_cfg_ptrs vsa_info orig_cfg =
  let module C = Cfg.SSA in
  let sinktbl = SinkTbl.create 100 in
  let cfg = C.G.fold_vertex (fun v cfg ->
      let stmts = C.get_stmts orig_cfg v in
      let stmts = rewrite_stmt_ptrs vsa_info orig_cfg sinktbl stmts in
      C.set_stmts cfg v stmts
    ) orig_cfg orig_cfg in
  (cfg, sinktbl)

  let new_array bounds_for ctx ~mem ~ptr ~base ~tmp =
    begin
      match mem with
      | Ssa.Var mem ->
        begin
          match Var.typ mem with
          | Type.TMem _ -> ()
          | _ -> failwith "inappropriate mem type"
        end
      | _ -> failwith "mem is not an Ssa.Var"
    end;
    let (low, high) = bounds_for ~ptr ~base in
    dprintf "bounds_for tmp %s: (%#Lx, %#Lx)" (Pp.var_to_string tmp) low high;
    let open Big_int_Z in
    let low = big_int_of_int64 low in
    let high = big_int_of_int64 high in
    lookup_ary ctx.base2array base ~low ~high

let adj_high w high =
  let open Big_int_Z in
  let open Big_int_convenience in
  dprintf "adj_high %s" (string_of_big_int high);
  let max = big_int_of_int64 Int64.max_int in
  dprintf "max is %s" (Big_int_Z.string_of_big_int max);
  if high ==% max then
    high
  else
    high +% w -% bi1

let unpack_offset infinity = function
  | Some off ->
    let open Big_int_Z in
    dprintf "Unpacking %s" (string_of_big_int off);
    let ret = int64_of_big_int off in
    ret
  | None -> infinity

  let bounds_for vsa_info cfg sinktbl typ ~ptr ~base =
    let sinkpath base =
      try
        SinkTbl.find sinktbl base
      with Not_found ->
        let s = Printf.sprintf "No sinkpath for %s" (Pp.var_to_string base) in
        failwith s
    in
    match Memory_region_analysis.reduce_var vsa_info cfg ~ptr (sinkpath ptr) with
    | Some (retbase, lb, ub) ->
      if Var.compare retbase base <> 0 then begin
        let s = Printf.sprintf "Got a different base (%s) than the one supplied (%s)"
            (Pp.var_to_string retbase) (Pp.var_to_string base) in
        failwith s
      end;
      let access_width = Big_int_Z.big_int_of_int (Typecheck.bytes_of_width typ) in
      let ub = BatOption.map (adj_high access_width) ub in
      let lb = unpack_offset Int64.min_int lb in
      let ub = unpack_offset Int64.max_int ub in
      (lb, ub)
    | None ->
      failwith "TBD: couldn't determine bounds?"

  let arrayfy_mem_access bounds_for ctx ~ptr ~base ~tmp stmt =
    let gen_adj ary tmp =
      let open Big_int_convenience in
      let tmp2 = Disasm_temp.nt "adjusted_index" Ast.reg_32 in
      let bounds = Var_convenience.Array.bounds ary in
      let lb = match Interval.Big_int.begin_ bounds with
        | None -> failwith "Empty interval for ary!"
        | Some lb -> lb
      in
      let s = Ssa.Move(tmp2,
                       Ssa.BinOp (Type.MINUS,
                                  Ssa.Var tmp, Ssa.Int (lb, Type.Reg 32)),
                       [Type.Synthetic]) in
      (s, tmp2)
    in
    match stmt with
    | Ssa.Move (avar, Ssa.Load (mem, _, e, typ), attrs) ->
      let ary = new_array (bounds_for typ) ctx ~mem ~ptr ~base ~tmp in
      let ctx = {ctx with mem2ary = BatMap.add mem ary ctx.mem2ary} in
      let adj, tmp2 = gen_adj ary tmp in
      let nload = Ssa.Move (avar, Ssa.Load (Ssa.Var ary, Ssa.Var tmp2, e, typ), attrs) in
      (ctx, Some [nload; adj])

    | Ssa.Move (_, Ssa.Store (mem, _, v, e, typ), attrs) ->
      let ary = new_array (bounds_for typ) ctx ~mem ~ptr ~base ~tmp in
      let ctx = {ctx with mem2ary = BatMap.add mem ary ctx.mem2ary} in
      let adj, tmp2 = gen_adj ary tmp in
        (*
         * We purposefuly reuse the ary as the avar, this will be taken care of by
         * the reSSAfication code.
         *)
      let nstore = Ssa.Move (ary, Ssa.Store (Ssa.Var ary, Ssa.Var tmp2, v, e, typ), attrs) in
      (ctx, Some [nstore; adj])

    | _ ->
      let s = Printf.sprintf "Stmt following an index_for_vsa calculation is \
                              not a memory access: %s" (Pp.ssa_stmt_to_string stmt) in
      failwith s

  let collect_mem_access bounds_for memr ~ptr ~base ~tmp stmt =
    match stmt with
    | Ssa.Move (_, Ssa.Load (_, _, _, typ), _)
    | Ssa.Move (_, Ssa.Store (_, _, _, _, typ), _) ->
      let (low, high) = bounds_for typ ~ptr ~base in
      let memr = Memrange.access memr base ~low ~high typ in
      (memr, None)
    | _ ->
      let s = Printf.sprintf "Stmt following an index_for_vsa calculation is \
                              not a memory access: %s" (Pp.ssa_stmt_to_string stmt) in
      failwith s

  let ary_is_tmem = function
    | Int _ -> false
    | Lab _ -> false
    | Var var ->
      (match Var.typ var with
       | Type.TMem _ -> true
       | _ -> false)

  let collect_global vsa_info memr s =
    match s with
    | Ssa.Move (_, Ssa.Load (ary, idx, _, typ), _)
    | Ssa.Move (_, Ssa.Store (ary, idx, _, _, typ), _) ->
      assert(ary_is_tmem ary);
      let si = CrappyVSA.si_for_val vsa_info idx in
      if CrappyVSA.SI.is_constant si then begin
        let w = Big_int_Z.big_int_of_int (Typecheck.bytes_of_width typ) in
        let (_, low, _) = si in
        let low = Big_int_Z.big_int_of_int64 low in
        let high = adj_high w low in
        let low = unpack_offset Int64.min_int (Some low) in
        let high = unpack_offset Int64.max_int (Some high) in
        let memr = Memrange.access memr Var_convenience.Array.global_array_base ~low ~high typ in
        (memr, s)
      end else begin
        (memr, s)
      end
    | _ ->
      (memr, s)

  let rewrite_global vsa_info ctx s =
    let open Var_convenience in
    let calc_nidx ~idx typ =
      let open Big_int_convenience in
      let si = CrappyVSA.si_for_val vsa_info idx in
      if CrappyVSA.SI.is_constant si then begin
        let width = Big_int_Z.big_int_of_int (Typecheck.bytes_of_width typ) in
        let (_, low, _) = si in
        let low = Big_int_Z.big_int_of_int64 low in
        let high = adj_high width low in
        let ary = lookup_ary ctx.base2array
            Array.global_array_base ~low ~high in
        let bounds = Array.bounds ary in
        match Interval.Big_int.begin_ bounds with
        | None -> failwith "No low bound for interval in globals"
        | Some lbound -> Some (ary, Ssa.Int (low -% lbound, Type.Reg 32))
      end else begin
        None
      end
    in
    match s with
    | Ssa.Move (avar, Ssa.Load (mem, idx, e, typ), attrs) ->
      assert(ary_is_tmem mem);
      begin
        match calc_nidx ~idx typ with
        | Some (ary, idx) ->
          let ctx = {ctx with mem2ary = BatMap.add mem ary ctx.mem2ary} in
          let nload = Ssa.Load (Ssa.Var ary, idx, e, typ) in
          (ctx, Ssa.Move (avar, nload, attrs))
        | None ->
          (ctx, s)
      end
    | Ssa.Move (avar, Ssa.Store (mem, idx, value, e, typ), attrs) ->
      assert(ary_is_tmem mem);
      begin
        match calc_nidx ~idx typ with
        | Some (ary, idx) ->
          let ctx = {ctx with mem2ary = BatMap.add mem ary ctx.mem2ary} in
          let nstore = Ssa.Store (Ssa.Var ary, idx, value, e, typ) in
          (ctx, Ssa.Move (ary, nstore, attrs))
        | None ->
          (ctx, s)
      end
    | _ ->
      (ctx, s)

  let examine_mem_accesses_in_stmts f g acc stmts =
    dprintf "arrayfy_stmts";
    let rec inner acc seen remaining =
      dprintf "inner";
      match remaining with
      | [] ->
        (acc, seen)
      | [s] ->
        (* Only one stmt left, our pattern involves two, so we're done *)
        (acc, s :: seen)
      | s :: next :: rest ->
        (*
         * Search for a sequence of [index_for_vsa; Load/Store].
         *)
        begin
          dprintf "inner: looking at %s" (Pp.ssa_stmt_to_string s);
          match s with
          | Ssa.Move (tmp, Ssa.BinOp (Type.MINUS, Ssa.Var ptr, Ssa.Var base),
                      [Type.Synthetic; Type.StrAttr str])
            when str = "index_for_vsa" ->
            dprintf "arrayfy_stmts: found pattern (tmp %s)" (Pp.var_to_string tmp);
            (*
             * Our callback updates its acc and may request that the Load/Store
             * get replaced with a list of new statements.
             *)
            let acc, rewritten = f acc ~ptr ~base ~tmp next in
            begin
              match rewritten with
              | Some nstmts ->
                inner acc (nstmts @ [s] @ seen) rest
              | None ->
                inner acc ([next] @ [s] @ seen) rest
            end
          | Ssa.Move (_, Ssa.Load _, _)
          | Ssa.Move (_, Ssa.Store _, _) ->
            let acc, s = g acc s in
            inner acc (s :: seen) (next :: rest)
          | _ ->
            inner acc (s :: seen) (next :: rest)
        end
    in
    let acc, rev_stmts = inner acc [] stmts in
    (acc, List.rev rev_stmts)

  let sinktbl_to_str sinktbl =
    let to_s sink =
      try
        let sp = SinkTbl.find sinktbl sink in
        Printf.sprintf "%s : %s" (Pp.var_to_string sink) (Sinkpath.to_string sp)
      with Not_found ->
        failwith (Printf.sprintf "Programming is hard, let's go shopping (%s)" (Pp.var_to_string sink))

    in
    Print.enum_to_string ~enclosing:("[", "]") ~sep:"\n" to_s
      (SinkTbl.keys sinktbl)

  let arrayfy_cfg cfg =
    let module C = Cfg.SSA in
    (*
     * 1. Calculate the VSA information; we make use of it to
     *    decide what may be or definitely is not a pointer.
     *)
    let vsa_info = CrappyVSA.calculate cfg "before rewrite_ptrs" in

    (*
     * 2. For each each Load/Store (mem, idx), decide which is the base ptr
     *    (by looking at sinks in the (conceptual) VRG graph) and rewrite the
     *    stmt to:
     *        t1 = idx - base [synthetic, @str "index_for_vsa"]
     *        Load/Store (mem, idx)
     * The t1 var is unused at this stage; it would have been nice to use the VSA
     * information on t1 to determine the array bounds, but our VSA implementation
     * is too weak for that. Simultaneously, we build up the sinktbl which maps
     * from the idx to a sinkpath. This is later used to build the VRG properly.
     *)
    let (cfg, sinktbl) = rewrite_cfg_ptrs vsa_info cfg in
    dprintf "SinkTbl = %s" (sinktbl_to_str sinktbl);
    (*
     * 3. Need to recompute the data deps or the statements we just added
     * will not be found as definitions.
     *)
    let vsa_info = CrappyVSA.calculate cfg "before arrayfy" in
    let memr = Memrange.create Var.VarSet.empty in
    let memr = C.G.fold_vertex (fun v memr ->
        let stmts = C.get_stmts cfg v in
        let pattern_cb = collect_mem_access (bounds_for vsa_info cfg sinktbl) in
        let globals_cb = collect_global vsa_info in
        let memr, _ = examine_mem_accesses_in_stmts
            pattern_cb globals_cb memr stmts in
        memr) cfg memr
    in
    let ctx = {
      base2array = memr2arrays memr;
      mem2ary = BatMap.empty;
    } in
    C.G.fold_vertex (fun v (ctx, ncfg) ->
        let stmts = C.get_stmts cfg v in
        (*
         * 4. Look for the pattern we produced earlier and change
         *        t1 = idx - base
         *        Load/Store (mem, idx)
         *    to
         *        t1 = idx - base
         *        adj_idx = t1 - low_bound
         *        Load/Store (ary, adj_idx)
         *    This builds up the VRG and uses Bellman-Ford on it to calculate
         *    the array bounds.
         *)
        let pattern_cb = arrayfy_mem_access (bounds_for vsa_info cfg sinktbl) in
        let globals_cb = rewrite_global vsa_info in
        let ctx, stmts = examine_mem_accesses_in_stmts
            pattern_cb globals_cb ctx stmts in
        let ncfg = C.set_stmts ncfg v stmts in
        (ctx, ncfg)) cfg (ctx, cfg)

module NormalizeAstCfgIndices =
struct
  module NV = Var_convenience.NormalizableVar
  module Ary = Var_convenience.Array
  module I = Interval.Big_int
  let pmap f (p, p') = (f p, f p')

  (*
   * When normalizing variables, we have to make sure that we normalize to
   * an unique idx, because the Var.hash function uses the idx as the hash
   * value. So everything depending on Var.hash, such as translation to SSA
   * will break if this invariant is broken.
   *
   * For registers, we can normalize them to their arch counter-parts.
   * Arrays will be normalized by create a new idx for each unique array.
   * To compare arrays we use the array's name.
   *
   * Memory is normalized to idx 0.
   *)

  let rec norm_reg arch v =
    try
      let new_var = List.find (fun v' -> (Var.name v) = (Var.name v'))
          (Asmir.decls_for_arch arch) in
      dprintf "Normalizing variable %s to %s" (Pp.var_to_string v)
        (Pp.var_to_string new_var);
      NV.return new_var
    with Not_found -> NV.return v
  and norm_ary  =
    let ctx = BatHashtbl.create 8 in
    (fun ary ->
       if Ary.is_array ary
       then
         match Misc.bathashtbl_find_option ctx (Var.name ary) with
         | Some new_ary -> dprintf "Normalizing array %s to existing %s" (Pp.var_to_string ary)
                             (Pp.var_to_string new_ary);
           NV.return new_ary
         | None ->
           let base_reg = Ary.base_reg ary in
           let bounds = Ary.bounds ary in
           (match I.begin_ bounds, I.end_ bounds with
            | Some l, Some h ->
              let l, h = pmap Big_int_Z.int64_of_big_int (l,h) in
              let new_ary = Var.renewvar (Ary.of_var base_reg l h) in
              BatHashtbl.add ctx (Var.name new_ary) new_ary;
              dprintf "Normalizing array %s to %s" (Pp.var_to_string ary)
                (Pp.var_to_string new_ary);
              NV.return new_ary
            | _ -> NV.return ary)
       else NV.return ary)
  and norm_mem v = if Var.name v = "mem"
    then
      let new_mem = Var.construct 0 "mem" (Var.typ v) in
      dprintf "Normalizing memory %s to %s" (Pp.var_to_string v)
        (Pp.var_to_string new_mem);
      NV.return new_mem
    else NV.return v
  and apply v normalizers = NV.to_v (List.fold_left (fun t norm ->
      NV.bind t norm) (NV.return v) normalizers)

  let normalize arch =
    let visitor = object(self)
      inherit Ast_visitor.nop

      method normalize v =
        Type.ChangeTo (apply v [norm_reg arch; norm_ary; norm_mem])
      method visit_avar = self#normalize
      method visit_rvar = self#normalize
    end
    in
    Ast_visitor.cfg_accept visitor
end

module PatchArrays =
struct
  module Ary = Var_convenience.Array
  let is_ary_load = function
    | Move (_, Load (ary, _, _, _), _)
      when Ary.is_array (Helpers.val2var_exn ary)-> true
    | _ -> false

  let is_ary_store = function
    | Move (_, Store (ary, _, _, _, _), _)
      when Ary.is_array (Helpers.val2var_exn ary)-> true
    | _ -> false

  let is_phi_of_ary = function
    | Move (_, Phi vars, _) ->
      List.for_all Ary.is_array vars
    | _ -> false

  let filter_phi_of_mem arrayfication_ctx = function
    | Move(_, Phi vars, _) ->
      let find x = BatMap.Exceptionless.find x arrayfication_ctx.mem2ary in
      let vars = List.map (fun v -> Var v) vars in
      let defined_by_ary = BatList.filter_map find vars in
      if (List.length defined_by_ary) > 0
      then begin
        if (List.length defined_by_ary) > 1
        then
          let _, same = List.fold_left (fun (ary, same) ary' ->
              if not same then (ary', false)
              else (ary', (Var.name ary) = (Var.name ary'))
            ) (List.hd defined_by_ary, true) (List.tl defined_by_ary)
          in same
        else true
      end
      else false
    | _ -> false

  let any preds el =
    let is_true b = b = true in
    List.exists is_true (List.map (fun pred -> pred el) preds)

  let is_ary_load_or_store = any [is_ary_load; is_ary_store]

  type array_patch_ctx = {
    bb_to_loads_stores : (Cfg.bbid, stmt list) BatHashtbl.t;
    bb_to_phis : (Cfg.bbid, stmt list) BatHashtbl.t;
  }
  let collect_patch_sources ~normalized_rewritten_ssacfg =
    (*
     * Foreach BB, we collect the loads and stores.
     * We rely on the order of the memory operations in each BB for matching.
     * That is, we do *not expect* the order to *change*.
     * This seems more stable then relying on offsets (e.g., the remove_temps option
     * when converting from SSA to AST can already cause a change in the offsets.)
     *)
    let acc = {
      bb_to_loads_stores =  BatHashtbl.create 8;
      bb_to_phis = BatHashtbl.create 8;
    } in
    G.fold_vertex (fun v acc ->
        let bbid = G.V.label v in
        let rev_loads_stores, rev_phis =
          List.fold_left (fun (loads_stores, phis) stmt ->
              if is_ary_load_or_store stmt then begin
                (stmt :: loads_stores, phis)
              end else begin
                if is_phi_of_ary stmt then begin
                  (loads_stores, stmt::phis)
                end else begin
                  (loads_stores, phis)
                end
              end
            ) ([], []) (C.get_stmts normalized_rewritten_ssacfg v)
        in
        BatHashtbl.add acc.bb_to_loads_stores bbid (List.rev rev_loads_stores);
        (* The order doesn't really matter, but lets stay consistent. *)
        BatHashtbl.add acc.bb_to_phis bbid (List.rev rev_phis);
        acc
      ) normalized_rewritten_ssacfg acc

  let get_ary = function
    | Move (_, Load(ary, _,_,_),_) ->
      let ary' = Helpers.val2var_exn ary in
      if (Ary.is_array ary') then (None, Some ary)
      else (None, None)
    | Move (avar, Store(ary, _,_,_,_),_) ->
      let ary' = Helpers.val2var_exn ary in
      if (Ary.is_array avar) && (Ary.is_array ary')
      then (Some avar, Some ary)
      else (None, None)
    | _ -> (None, None)

  (* Helper to check we are replacing the correct array. *)
  let assert_ary ary ary' =
    let ary = Helpers.val2var_exn ary in
    let ary' = Helpers.val2var_exn ary' in
    assert((Ary.base_reg ary) = (Ary.base_reg ary'));
    assert(Interval.Big_int.equal (Ary.bounds ary) (Ary.bounds ary'))

  (*
   * For a load we only replace the idx, but for a store we replace both
   * the store idx, but also the avar in the move.
   * The avar in a move is always an array, when the store idx is an array.
   * So we have to make sure the correct array is assigned or otherwise
   * the assigned array will be removed by DCE since subsequent loads will
   * use the /correct/ array as an idx.
   *)
    let try_replace_ary replacement = function
      | Move (avar, Load(ary, idx, edn, t), attr) as load ->
        (match replacement with
         | None, Some nary ->
           assert_ary ary nary;
           let new_load = Move (avar, Load(nary, idx, edn, t), attr) in
           dprintf "Replacing %s with %s" (Pp.ssa_stmt_to_string load)
             (Pp.ssa_stmt_to_string new_load);
           Some new_load
         (* In case of a memory load, not converted to an array load *)
         | None, None ->
           assert(not (Helpers.mem_is_ary ary));
           None
         | _ ->
           raise (Confusing_function "Unexpected replacement definition to replace load!")
        )
      | Move (avar, Store(ary, idx, v, edn, t), attr) as store ->
        (match replacement with
         | Some navar, Some nary ->
           assert_ary (Var avar) (Var navar);
           assert_ary ary nary;
           let new_store = Move (navar, Store(nary, idx, v, edn, t), attr) in
           dprintf "Replacing %s with %s" (Pp.ssa_stmt_to_string store)
             (Pp.ssa_stmt_to_string new_store);
           Some new_store
         (* In case of memory store, not converted to an array store *)
         | None, None ->
           assert(not (Ary.is_array avar));
           assert(not (Helpers.mem_is_ary ary));
           None
         | _ ->
           raise (Confusing_function "Unexpected replacement definition to replace store!")
        )
      | _ ->
        raise (Confusing_function
                 "Unexpected statement to replace, can only replace stores and loads!")

  let patch patch_ctx arrayfication_ctx ~rewritten_ssacfg =
    G.fold_vertex (fun v cfg ->
        let bbid = G.V.label v in
        (* First we deal the phis *)
        let stmts = (C.get_stmts cfg v) in
        (* Remove phis of mem defined by array stores *)
        let stmts = List.filter ((filter_phi_of_mem arrayfication_ctx) |- not)
            stmts
        in
        (* Prepend phis of arrays *)
        let stmts = (BatHashtbl.find patch_ctx.bb_to_phis bbid) @ stmts in
        (* After the phis, we replace loads and stores of arrays. *)
        let ary_loads_stores = BatHashtbl.find patch_ctx.bb_to_loads_stores bbid in
        let rev_stmts, left_ary_loads_stores =
          List.fold_left (fun (stmts, ary_loads_stores) stmt ->
              match ary_loads_stores with
              | [] ->
                (* Check if we missed an array load or store *)
                if is_ary_load_or_store stmt then begin
                  let reason =
                    Printf.sprintf
                      "Missed array load/store while rewriting!\n%s"
                      (Pp.ssa_stmt_to_string stmt) in
                  raise (Confusing_function reason)
                end else (stmt :: stmts, [])
              | h :: t  ->
                begin
                  if is_ary_load_or_store stmt then
                    (match try_replace_ary (get_ary h) stmt with
                     | Some nstmt -> (nstmt :: stmts, t)
                     | None -> (stmt :: stmts, ary_loads_stores))
                  else  (stmt :: stmts, ary_loads_stores)
                end
            ) ([], ary_loads_stores) stmts
        in
        if List.length left_ary_loads_stores > 0 then begin
          let str =
            (Printf.sprintf "Failed to match the following memory statements in %s\n%s"
               (Cfg.bbid_to_string bbid)
               (Print.list_to_string Pp.ssa_stmt_to_string left_ary_loads_stores))
          in
          raise (Confusing_function str)
        end else C.set_stmts cfg v (List.rev rev_stmts)
      ) rewritten_ssacfg rewritten_ssacfg
end

let rewrite_stack_loadstores arch g =
       (*
        * TODO: this should be in the cxt and it should be automagically
        * invalidated after transform passes. As things are, we recalculate
        * it here and in collect_mem_accesses.
        *)
        let arrayfication_ctx, rewritten_ssacfg = arrayfy_cfg g in
       (*
        * Do SSA conversion /again/, so that the array variables
        * will get proper indices so that they obey the SSA form
        * (i.e. only assigned to once). Unfortunately, we need
        * to convert back to AST for this.
        *
        * When converting from SSA to AST, the resulting AST retains the
        * assign once property, resulting in a different SSA form when converted
        * back to SSA again.
        * To make sure that references to the same register, array, or memory
        * location in SSA form result in the *same* variable in AST we normalize the
        * indices.
       *)
       (*
         The copied-out phi parameters will become identities after the normalization.
       *)
        (*
           Keep temps when translating SSA to AST.
           This is required to keep the number of loads between
              rewritten SSA and normalized rewritten SSA equal.
           It seems that the translation to AST with remove_temps
              removes array loads to temps.
           Haven't fully investigated the reason why, but keeping
              temps prevents functions from being marked confusing
              because of a missed load/store to an array.

             R.V
         *)
        let normalized_rewritten_astcfg =
          Analysis_helpers.AstCfg.remove_identities
            (NormalizeAstCfgIndices.normalize arch
               (Cfg_ssa.to_astcfg ~remove_temps:false rewritten_ssacfg))
        in
        let normalized_rewritten_ssacfg = Cfg_ssa.of_astcfg normalized_rewritten_astcfg
        in
        Printf.eprintf "SSA CFG before rewriting stores & loads\n";
        Graph_dump.output_ssa stderr g;

        (* At this point, memory accesses have been replaced by accesses
         * through idx = calculation(); ary_BASEPTR_blah[idx]
         *)
        Printf.eprintf "\nSSA CFG after rewriting stores & loads\n";
        Graph_dump.output_ssa stderr rewritten_ssacfg;


        (* Next, we convert to AST again, making sure that ary_BASEPTR_blah
         * has the same Var.idx everywhere (i.e. if it has the same ary name,
         * it's the same variable)
        *)
        Printf.eprintf "\nAST CFG after normalization stores & loads\n";
        Graph_dump.output_ast stderr normalized_rewritten_astcfg;

        (* Do ssa conversion again. This time, the variable indexes of the
         * arrays in memory accesses will not interfere with each other
         * (before, any store to memory would change the memory idx).
         *)
        Printf.eprintf "\nSSA CFG after normalization stores & loads\n";
        Graph_dump.output_ssa stderr normalized_rewritten_ssacfg;
       (*
         Now that we have a SSA CFG with array indices that considers alias-relationships
         we collect the loads and stores and move them to our existing SSA CFG and replace
         the arrays with indices that didn't consider aliasing.
       *)
        (* The above was all about arrayfication of memory accesses and
         * making sure the arrays we add all observe the SSA properties
         * (we ensured that by going to AST and re-running the SSA
         * conversion). Transcribe the array names and indices we calculated
         * in the normalized_rewritten_ssacfg to our rewritten_ssacfg (which,
         * remember, has additional statements (for calculating the index of
         * an array access) compared to our original SSA CFG).
        *)
        let patch_ctx =
          PatchArrays.collect_patch_sources ~normalized_rewritten_ssacfg
        in
        PatchArrays.patch patch_ctx arrayfication_ctx ~rewritten_ssacfg
