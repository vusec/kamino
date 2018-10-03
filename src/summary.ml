module D = Debug.Make(struct let name = "Summary" and default=`Debug end)
open D

open Ktype.Exceptions

module StringMap = BatMap.Make(String)
module BBIface =
struct
  type id = Int64.t
  type element = Stmt_context.stmt_context list
  let id_to_string = Printf.sprintf "%#Lx"
end


module BBcache = Pfc.MakePersistentCache(BBIface);;

exception No_runtime_info;;
exception Unknown_bbaddr;;

open Stmt_context;;

let has_reachable_call cfg bb callinfo =
  let bb_has_call v =
      let stmts = Cfg.SSA.get_stmts cfg v in
      match Bb.get_bbbounds_from_ssa stmts with
      | BatResult.Ok (_, last) when Callinfo.call_at_addr callinfo last <> None ->
        true
      | _ ->
        false
  in
  let module Reach = Reachable.SSA in
  let reachable_set = Reach.reachable cfg bb in
  try
    ignore(List.find bb_has_call reachable_set);
    true
  with Not_found -> false

module Algo =
  struct
    let filter_outputs vis callinfo func bb =
      let filter_invisible = object
        method reason = "not useful"
        method filter output =
          dprintf "filter_invisible: considering %s" (Ssa_ext.Variable.to_string output);
          let outv = Ssa_ext_convenience.Variable.var output in
          let bound_is_neg v =
            let bounds = Var_convenience.Array.bounds v in
            let breg = Var_convenience.Array.base_reg v in
            match Interval.Big_int.end_ bounds with
            | None ->
              failwith "zero-size array?"
            | Some high ->
              let high = Arithmetic.to_sbig_int (high, (Var.typ breg)) in
              dprintf "bound is %Ld" (Big_int_Z.int64_of_big_int high);
              (Big_int_Z.compare_big_int high Big_int_convenience.bi0) < 0
          in
          if (Var_convenience.Array.is_array outv)
              (*
               * XXX: we'd need semi-accurate info on function arguments
               * to properly separate local variables from arguments to
               * a call. Until we can do that, consider *all* stores visible
               * and hope that compilers will mostly not generate pointless
               * stores at -Ox, x > 1 or x = s.
               * XXX: x86-specific: i386ism
               *)
(*
              (((String.compare (Var.name (Transfer_function.base_reg_for_ary output)) "R_ESP") <> 0) ||
                  (not (bound_is_neg outv)))
*)
          then begin
            let basereg = Var.name (Transfer_function.base_reg_for_ary output) in
            let is_sp = (String.compare basereg "R_ESP") = 0 in
            let cfg = Function_info.Function.ssacfg func in
            let bbv = Cfg.SSA.find_vertex cfg bb.Bb.id in
            (*
             * Arrays are always useful (they're visible outside the function),
             * unless they're located in the local stack frame and there's no
             * reachable call (this is a hack to keep call arguments live :().
             *)
            if is_sp && bound_is_neg outv then begin
              if (has_reachable_call cfg bbv callinfo) then begin
                (true, "stackvar+bound_is_neg+has_reachable_call")
              end else begin
                let ret = Visibility.var_def_used vis
                    (Ssa_ext_convenience.Variable.var output) bb.Bb.id
                in
                (ret, Printf.sprintf
                   "stackvar+bound_is_neg+has_reachable_call+visible=%b" ret)
              end
            end else begin
              assert(Ssa_ext_convenience.Variable.is_array output);
              (true, "array")
            end
          end else if Var_convenience.Array.is_mem outv then begin
              (* Heap stores are always visible *)
              (true, "mem")
          end else begin
            let ret = Visibility.var_def_used vis
                (Ssa_ext_convenience.Variable.var output) bb.Bb.id
            in
            (ret, Printf.sprintf "reg+visible=%b" ret)
          end
      end
      in
      let filter_esp = object
        method reason = "esp adjustment in well-behaved function"
        method filter output =
          match output with
          | Ssa_ext.Variable.Var (v, _)
          | Ssa_ext.Variable.VarExp (v, _, _) ->
            let wb = Function_info.Function.has_attr func Func_attr.WellBehaved in
            0 <> (List.length (Karch.X86.filter_vars_if_well_behaved wb [v]))
      end
      in
      let apply_output_filters filters bb tfs =
        (* XXX: keep flag registers used by a cjmp *)
        StringMap.filter (fun name tf ->
          let output = tf.Transfer_function.output in
          List.fold_left (fun acc filt ->
            match acc with
            | false ->
              false
            | true ->
              let res = filt#filter output in
              if not res then
                dprintf "dropping output %s: %s" name filt#reason;
              res
          ) true filters
        ) tfs
      in
      let do_filter bb tfs =
        let tfs = apply_output_filters [filter_esp] bb tfs in

        (* Keep invisible TFs around *)
        let (visible_tfs, invisible_tfs) =
          StringMap.partition (fun name tf ->
              let output = tf.Transfer_function.output in
              let res, msg = filter_invisible#filter output in
              if not res then begin
                dprintf "moving output %s to invisibles: %s" name msg
              end else begin
                dprintf "keeping output %s visible: %s" name msg
              end;
              res) tfs
        in
        let invisible_tfs = StringMap.filterv (fun tf ->
            let open Transfer_function in
            let open Visibility in
            var_is_live_in_defining_bb vis
              (Ssa_ext_convenience.Variable.var tf.output) bb.Bb.id) invisible_tfs
        in
        {bb with Bb.tfs = Some visible_tfs; Bb.invisible_tfs = invisible_tfs}
      in
      match bb.Bb.tfs with
      | None -> bb
      | Some tfs -> do_filter bb tfs


    let analyze_func keypref pipeline_ctx func =
      let module Function = Function_info.Function in
      let fdescr = Function.to_string func in
      dprintf "FUNC %s" fdescr;
      let keypref = Printf.sprintf "%s/%s" keypref (Analysis_pass.fdir func) in
      let ssa_cfg = Function.ssacfg func in
      let domfuncs = Ktype.SsaDom.compute_all ssa_cfg
          (Cfg.SSA.G.V.create Cfg.BB_Entry) in
      let rec domtree2graph acc start =
        let idom_vertex = Cfg.SSA.G.V.create (Cfg.SSA.G.V.label start) in
        let acc = Cfg.SSA.add_vertex acc idom_vertex in
        List.fold_left (fun acc v ->
            let dom_vertex = Cfg.SSA.G.V.create (Cfg.SSA.G.V.label v) in
            let acc = Cfg.SSA.add_vertex acc dom_vertex in
            let acc = Cfg.SSA.add_edge acc idom_vertex dom_vertex in
            domtree2graph acc dom_vertex
          ) acc (domfuncs.Ktype.SsaDom.dom_tree start)
      in
      let domgraph = domtree2graph (Cfg.SSA.empty ())
        (Cfg.SSA.G.V.create Cfg.BB_Entry)
      in
      let domtree_key = Printf.sprintf "%s/%s" keypref "domtree.dot" in
      Outdir.with_file_out domtree_key (fun oc ->
          Graph_dump.output_ssa oc domgraph);

      let dump_ssa_ext v stmts =
        (* Since this SSA CFG was created from a single BB, it should only
           consist of two BBs, BB_Entry and BB_Exit (which should only contain
           a label *)
        let key = Printf.sprintf "%s/%s.ssa_ext.dot" keypref (Cfg.SSA.v2s v) in
        Outdir.with_file_out key (fun oc ->
            let outstr = Print.list_to_string ~sep:("\n")
                (Ssa_ext.Statement.to_string) stmts in
            Printf.fprintf oc "%s\n" outstr)
      in
      let compute_tfs stmts =
        let tfs = Transfer_function.compute_for_bb stmts in
        List.fold_left (fun acc tf ->
          let key = (Ssa_ext.Variable.to_string (tf.Transfer_function.output)) in
          dprintf "Adding tf for output %s" key;
	  StringMap.add key tf acc
	) (StringMap.empty) tfs
      in
      let dump_tfs pref bbsum =
        let key = Printf.sprintf "%s/%s.%s_tfs" keypref
            (Cfg.bbid_to_string bbsum.Bb.id) pref
        in
        let do_tfs oc visible invisible =
          let open Sexplib in
          let sexp = Sexp.List [
              Sexp.Atom "TRANSFER_FUNCTIONS";
              Sexp.List [
                (* Explicitly #tfs for easily getting an overview w/ grep *)
                Sexp.Atom "VISIBLE";
                Sexp.Atom (Printf.sprintf "%d" (List.length visible));
                Std.sexp_of_list Transfer_function.sexp_of_t visible;];
              Sexp.List [
                Sexp.Atom "INVISIBLE";
                Sexp.Atom (Printf.sprintf "%d" (List.length invisible));
                Std.sexp_of_list Transfer_function.sexp_of_t invisible;];
            ] in
          let fmt = Format.formatter_of_out_channel oc in
          Sexp.pp_hum fmt sexp;
          Format.pp_print_newline fmt ();
          Format.pp_print_flush fmt ()
        in
        Outdir.with_file_out key (fun oc ->
            match bbsum.Bb.tfs with
              | None -> Printf.fprintf oc "None"
              | Some tfs ->
                let visible = StringMap.values tfs in
                let invisible = StringMap.values bbsum.Bb.invisible_tfs in
                do_tfs oc (BatList.of_enum visible) (BatList.of_enum invisible)
          );
      in
      let walk_bb fdescr v =
        dprintf "Looking at BB %s of %s %s\n" (Cfg.SSA.v2s v) fdescr Print.fo;
        let ssa_stmts = Cfg.SSA.get_stmts ssa_cfg v in
        let ssa_ext_stmts = Ssa_ext.of_prog ssa_stmts in
        dump_ssa_ext v ssa_ext_stmts;

        let tfs =
          try
            let ret = compute_tfs ssa_ext_stmts in
            dprintf "Generated %i transfer function(s)"
              (StringMap.cardinal ret);
            Transfer_function.dump (StringMap.values ret);
            Some ret
          with Transfer_function.Incomputable msg ->
            dprintf "TF: %s" msg;
            None
        in
        let bbaddr =
          match tfs with
          | Some tfs when (StringMap.cardinal tfs) > 0 ->
	    (match Bb.get_bbaddr_from_ssa ssa_stmts with
            | Some addr -> Some addr
            | None ->
	      dprintf "couldn't get bbaddr from stmt ";
              None)
          | _ ->
            None
        in
        let summary =
          {
            Bb.bb_saddr = bbaddr;
            Bb.bb_fbegin = BatOption.get (Function_info.Function.begin_address func);
            Bb.id = Cfg.SSA.G.V.label v;
            Bb.tfs = tfs;
            Bb.invisible_tfs = StringMap.empty;
          }
        in
        dprintf "Done looking at %s %s\n" (Cfg.SSA.v2s v) Print.fc;
        dump_tfs "unfiltered" summary;
        Some summary
      in
      let bb_summaries = Cfg.SSA.G.fold_vertex
	(fun v acc -> (walk_bb fdescr v) :: acc) ssa_cfg [] in
      let bb_summaries = BatList.filter_map (fun x -> x) bb_summaries in
      let fbbs = List.fold_left (fun acc bbsum ->
	  Bb.BBidMap.add bbsum.Bb.id bbsum acc
	) (Bb.BBidMap.empty) bb_summaries
      in
      let visibility = Visibility.initialize ~keypref:(Some keypref) ssa_cfg in
      let callinfo = Analysis_pass.get_callinfo pipeline_ctx in
      (* XXX: verify we don't add two BBs with the same address, ever *)
      let fbbs = Bb.BBidMap.map (fun bb ->
          let bb = filter_outputs visibility callinfo func bb in
          dump_tfs "final" bb;
          bb
        ) fbbs in
      let open Ktype in
      {
        function_info = func;
        cfg = ssa_cfg;
        fbbs;
        dominfo = domfuncs;
	visibility;
        callinfo;
      }

    let init_outdirs_for_callgraph keypref cg =
      (* Generate fdir/function_name for every function *)
      ignore(Analysis_pass.map_vertex (fun fi ->
          match fi with
          | Function_info.Function func ->
            let fdir = Analysis_pass.fdir func in
            let keypref = Printf.sprintf "%s/%s/function_name" keypref fdir in
            Outdir.with_file_out keypref (fun oc ->
                Printf.fprintf oc "%s\n" (Function_info.Function.symbols_to_str func));
            fi
          | _ ->
            fi) cg)

    let handle_ast_callgraph ?(func_filter = (fun _ -> true)) arch ?keypref:(keypref=None) cg =
      let open Analysis_pass in
      let func_filter = match Options.summarize_calls with
        | Options.CallSumCalculate -> (fun _ -> true)
        | Options.CallSumCdecl -> func_filter
      in
      let (state, cg) = process_ast_pipeline ~func_filter ~keypref
        arch
        cg (List.map make_pass [
          `StartAst;
          (* Give up on everything containing calls; we're only looking
             at primitives for this project *)
          `VerifyNoCalls;
          `CollectCalls;
          (* obviously, this needs to come after CollectCalls *)
          `ReplaceCallStmts;
          `RemoveHaltStmts;
        ])
      in
      (state, cg)

    let handle_astcfg_callgraph ?(func_filter = (fun _ -> true)) state ?keypref:(keypref=None) cg =
      let open Analysis_pass in
      (*
       * Note: we can't start filtering just yet; we need to observe called
       * functions to calculate call side effects. After this is done,
       * we can focus on the functions we care about. (Obviously this could be
       * done in a lazy fashion by computing the transitive closure of the
       * functions reachable from the functions the user has selected. Too
       * much development work for too little gain ATM).
       *)
      let func_filter = match Options.summarize_calls with
        | Options.CallSumCalculate -> (fun _ -> true)
        | Options.CallSumCdecl -> func_filter
      in

      let state, cg = process_astcfg_pipeline ~func_filter ~keypref
        cg state
        (List.map make_pass [
          (* XXX: this assumes there are no actual indirect jumps other than rets *)
          `RemoveIndirect; (* Needs to run first! *)
          `PruneUnreachable1;
          `CoalesceCfg1;
          (*
           * Commentid: rymquofUk0
           * Note: there is a bug in BAP's coalescing which causes it to
           * ignore our protection of the break-after-a-call edge, under
           * conditions that I haven't had time to pinpoint yet. Therefore
           * we need to run BreakAfterCalls after every coalescing pass.
           *)
          `BreakAfterCalls1;
          `SubregLiveness;
        ])
      in

      let cg = Calls.account_for_calls ~func_filter ~keypref cg in
      let cg = Side_effect.summarize_calls ~func_filter ~keypref cg state in

      let state, cg = process_astcfg_pipeline ~func_filter ~keypref
        cg state
        (List.map make_pass [
          (* Redo those after the account_for_calls changes *)
          (*
           * XXX: should make sure the output file is not the same for passes
           * that are repeated.
           *)
          `PruneUnreachable2;
          `CoalesceCfg2;
          (*
           * BreakAfterCalls _needs_ to follow Coalescing (see
           * comment rymquofUk0 above)
           *)
          `BreakAfterCalls2;
          `ForceSingleExit;
          (*
           * BuildAddrmap needs to run after any pass that
           * might break/coallesce BBs.
           *)
          `BuildAddrmap;
        ])
      in
      (state, cg)

    let handle_callgraph ?(func_filter = (fun _ -> true)) arch keypref params cg funcstats =
      let open Analysis_pass in
      let oc = Outdir.get_outpath "pipeline_mem" in
      let dump_mem_stats str = Printf.fprintf oc "%s: %d bytes\n%!" str
          ((Gc.stat ()).Gc.heap_words * 4)
      in
      init_outdirs_for_callgraph keypref cg;
      dump_mem_stats "handle_callgraph entry";
      let (state, cg) = handle_ast_callgraph arch
        ~keypref:(Some keypref) cg
      in
      dump_mem_stats "after handle_ast_callgraph";
      let (state, cg) = handle_astcfg_callgraph ~func_filter state
        ~keypref:(Some keypref) cg
      in
      dump_mem_stats "after handle_astcfg_callgraph";
      let state, cg = process_ssa_pipeline ~func_filter
	(* TBD: Dumping should be made conditional on a cli option *)
	~keypref:(Some keypref) state cg
        (List.map make_pass [
          `StartSsa;
          `ComputeDataDependencies;
          `NormalizeCjmps;
	  `BapSsaSimplifications1;
          `DropNopBBs1;
          `ComputeDataDependencies;
          `ComputeFunctionInputs;
          `RewriteLoadStores;
	  `BapSsaSimplifications2;
          (* Recalculate data dependencies, RewriteLoadStores changes definitions *)
          `ComputeDataDependencies;
          `ComputeCollapsibleLoads;
          `RemoveNoreturnEdges; (* needs to come before MarkEaxLiveout *)
	  `MarkEaxLiveout;
(*	  `PhiPropagationPass; *)
          `MarkStoresLiveout; (* needs to come before DeadCodeElimination *)
          (* XXX: DCE & BB_Error don't play well together *)
          `DeadCodeElimination1;
          (* `PartialRedundantDefinitionElimination; *)
          `CoalesceSsa1;
          `Buoyancy;
          `BapSsaSimplifications3;
          `DeadCodeElimination2;
          (* So we don't drop an empty BB_Entry *)
          `CoalesceSsa2;
          `DropNopBBs2;
        ])
      in
      dump_mem_stats "after process_ssa_pipeline";
      let skip f msg =
        dprintf "Skipping analysis of function %s: %s"
          (Function_info.to_string f) msg
      in
      let ret = Analysis_pass.fold_vertex
          (fun f acc -> match f with
            | Function_info.Function _ when not (func_filter f) ->
              skip f "filtered";
              acc
            | Function_info.Function func when Function_info.has_attr f (Func_attr.Confusing "")->
              let attrs = Function_info.Function.attrs func in
              let msgs = BatEnum.filter_map (fun x -> match x with
                  | Func_attr.Confusing s -> Some s
                  | _ -> None) (Func_attr.FuncAttrSet.enum attrs) in
              let msgs = BatList.of_enum msgs in
              assert(1 = (List.length msgs));
              let msg = List.hd msgs in
              let msg = Printf.sprintf "Confusing: %s" msg in
              skip f msg;
              funcstats#failed msg;
              acc
            | Function_info.Function func as fi->
              (try
                 let ctx = match FuncHashtbl.find state fi with
                   | Some pipeline_ctx ->
                     pipeline_ctx
                   | None ->
                     let s = Printf.sprintf "no pipeline ctx for %s"
                         (Function_info.Function.to_string func) in
                     failwith s
                 in
                 let func = analyze_func keypref ctx func in
                 funcstats#analyzed;
                 func :: acc
              with Confusing_function msg ->
                wprintf "Could not analyze function %s: %s"
                  (Function_info.Function.to_string func) msg;
                acc)
            | Function_info.ExternalFunction _ ->
              skip f "external function";
              acc
            | Function_info.Indirect ->
              skip f "indirect call";
              funcstats#failed "indirect";
              acc
            | Function_info.Unknown _  ->
              skip f "unknown";
              funcstats#failed "unknown";
              acc
          ) cg []
      in
      dump_mem_stats "after analyze_func(s)";
      ret

    let function_filter params =
      let collect_selected strings =
        let names, addrs = List.fold_left (fun (names, addrs) str ->
            if str.[0] = '0' then begin
              let addr =
                try
                  Int64.of_string str
                with _ ->
                  failwith (Printf.sprintf "Couldn't parse %s" str)
              in
              (names, BatSet.add addr addrs)
            end else begin
              (BatSet.add str names, addrs)
            end) (BatSet.empty, BatSet.empty) strings
        in
        ((fun name -> BatSet.mem name names), (fun addr -> BatSet.mem addr addrs))
      in
      match params with
      | None -> (fun _ -> true)
      | Some params ->
        begin
          match Input.BinaryParameters.find_option params "funcs" with
          | Some []
          | None -> (fun _ -> true)
          | Some interesting_funcs ->
            dprintf "Limiting further analysis to functions %s"
              (Print.list_to_string BatPervasives.identity interesting_funcs);
            let want_name, want_addr = collect_selected interesting_funcs in
            (fun fi ->
               let names = Function_info.symbols fi in
               let addr = Function_info.begin_address fi in
               (List.exists want_name names) ||
               (BatOption.map_default want_addr false addr)
            )
        end

    let keep_interesting asm_prog =
      let is_plt addr =
        let start_addr = Asmir.get_section_startaddr asm_prog ".plt" in
        let end_addr = Asmir.get_section_endaddr asm_prog ".plt" in
        let interval = Interval.Section_interval.create start_addr end_addr in
        dprintf "keep_interesting: PLT is %s" (Interval.Section_interval.to_string interval);
        (Interval.Section_interval.contains interval addr) &&
        (* The interval contains its endpoint, we don't want that *)
        (Int64.compare addr end_addr < 0)
      in
      List.filter (fun fi ->
          match Function_info.begin_address fi with
          | None ->
            dprintf "keep_interesting: dropping %s: no address" (Function_info.to_string fi);
            false
          | Some addr when is_plt addr ->
            dprintf "keep_interesting: dropping %s: in PLT" (Function_info.to_string fi);
            false
          | _ ->
            dprintf "keep_interesting: keeping %s: not in PLT" (Function_info.to_string fi);
            true)

    let handle_binary ?runid i {Input.path=path; Input.parameters=params} =
      let binary = Input.BinaryPath.s path in
      let asm_prog = Asmir.open_program binary in
      let arch = Asmir.get_asmprogram_arch asm_prog in
      let ranges = Asmir.get_function_ranges asm_prog in
      (*
       * Add a prog%d prefix so that this works even if two binaries have
       * the same basename.
       *)
      let keypref = match runid with
        | Some n -> Printf.sprintf "run%d/prog%d-%s" n i (FilePath.basename binary)
        | None -> Printf.sprintf "prog%d-%s" i (FilePath.basename binary) in
      let gen_function_info (names, s, e) =
        let ast = Asmir.asmprogram_to_bap_range asm_prog s e in
        match names with
        | [] -> failwith "TBD"
        | name :: aliases ->
          let f = Function_info.Function.create name (Interval.Function_interval.create s e) ast in
          let f = List.fold_left Function_info.Function.add_alias f aliases in
          Function_info.Function f
      in
      (*
       * Note: we need to look at all funcs to build the callgraph. Filtering
       * happens later, after computing the side-effects, to avoid all the
       * expensive passes.
       *)
      let ranges = Misc.demangle_franges ranges in
      let ranges = Misc.dedup_franges ranges in
      let aug_funcs = List.map gen_function_info ranges in
      let aug_funcs = keep_interesting asm_prog aug_funcs in
      dprintf "got %d funcs" (List.length aug_funcs);
      let plt_entries = Plt.plt_entries_from binary in
      dprintf "got %d plt entries" (List.length plt_entries);
      let unkn_func_resolver addr = Plt.plt_resolve_addr asm_prog plt_entries
          addr in
      let cgbench = new Perfacc.bench "callgraph" in
      cgbench#start "";
      let call_graph =
        Callgraph.generate_call_graph unkn_func_resolver aug_funcs in
      let output_callgraph oc = Callgraph.dump_call_graph call_graph oc in
      Outdir.with_file_out (keypref ^ "/callgraph.dot") output_callgraph;
      dprintf "about to stop cgbench";
      cgbench#stop ();
      let funcstats = new Stats.analyzable binary in
      let func_filter = function_filter params in
      dprintf "about to handle_callgraph";
      let funcs = handle_callgraph ~func_filter arch keypref params call_graph
          funcstats
      in
      (funcs, funcstats)
  end;; (* module Algo *)

exception Cannot_summarize of string

let generate_coverage_report ?runid stats =
  let print_coverage oc =
    Printf.fprintf oc "%s\n" (Sexplib.Sexp.to_string_hum
  stats#sexp_of_t) in
  let filepath = match runid with
    | Some n -> Printf.sprintf "run%d/coverage" n
    | None -> "coverage" in
  Outdir.with_file_out ~append:true filepath print_coverage

let binidx = ref (-1)

let summarize_binary_spec ?runid ?(report_coverage=true) binary_spec =
  incr binidx;
  let {Input.path} = binary_spec in
  let binary = FilePath.basename (Input.BinaryPath.s path) in
  dprintf "Summerizing (%d) %s" !binidx binary;
  let benchmark = new Perfacc.bench "binary" in
  benchmark#start binary;
  let (funcs, stats) = Algo.handle_binary ?runid !binidx binary_spec in
  if report_coverage then generate_coverage_report ?runid stats;
  let begin_address af = Function_info.Function.begin_address af.Ktype.function_info in
  let name af = Function_info.Function.to_string af.Ktype.function_info in
  let add_lookup_entry table af = match begin_address af with
    | Some addr -> BatHashtbl.add table addr af; table
    | None -> raise (Cannot_summarize
                       (Printf.sprintf "Function %s has no begin address!"
                          (name af))) in
  let lookup_table = List.fold_left add_lookup_entry
      (dprintf "CREATED"; BatHashtbl.create (List.length funcs))
      funcs
  in
  let result = {
    Ktype.pname = binary;
    Ktype.pranges = new Address_ranges.address_ranges (Input.BinaryPath.s path);
    Ktype.pfuncs = lookup_table;
  } in
  benchmark#stop ();
  result

let summarize_binary ?(report_coverage=true) path =
  let binary_spec = Input.create_binary_spec path in
  summarize_binary_spec ~report_coverage binary_spec

let fold ~f ~init ?runid binary_specs =
  let aux acc binary_spec =
    f acc (summarize_binary_spec ?runid binary_spec) in
  List.fold_left aux init binary_specs
