module D = Debug.Make(struct let name = "Kamino" and default=`Debug end)
open D

let inputs = ref []
let output = ref stdout

type mode = CommandlineMode | BatchMode of Batch.t

let opt_classifier = ref "ByFunc"
let opt_compare_strategy = ref "combcmp"
let opt_matching_policy = ref "exhaustive"
let opt_timeout = ref 600
let opt_validate_result = ref false
let opt_detailed_stats = ref false
let opt_gc_stats = ref false
let opt_mode = ref CommandlineMode;;

Perfacc.output_on_stdout := true

let usage = "Usage: " ^ Sys.argv.(0) ^ " [options] binary[,params] [binary[,params]]\nExamine code fragments for contextual equivalence.\n"

let speclist =
  [
    ("-classifier",
     Arg.String (fun cl -> opt_classifier := cl),
     "BB classifier");
    ("-strategy",
     Arg.String (fun s -> opt_compare_strategy := s),
     "BB compare strategy");
    ("-matching-policy",
     Arg.String (fun s -> opt_matching_policy := s),
     "Fragment matching policy");
    ("-outdir",
     Arg.String (fun path -> Outdir.set_outdir path),
     "Output directory");
    ("-timeout",
     Arg.String (fun spec->
         try
           opt_timeout := Input.Parsers.parse_timeout spec
         with Failure s -> raise (Arg.Bad s)),
     "Timeout execution after specified time (e.g., 10 or 10s, 10m, and 10h)");
    ("-validate",
     Arg.Unit (fun () -> opt_validate_result := true),
     "Validate the matched fragments.");
    ("-max-workers",
     Arg.Int (fun n -> ForkWork.set_ncores n),
     "Set the maximum number of workers that can be used at the same time."
    );
    ("-no-fork",
     Arg.Unit (fun () -> Embarassingly_parallel.set_debug true),
     "Do not fork worker processes (forces single-threaded execution)");
    ("-batch",
    Arg.String (fun s -> opt_mode := BatchMode (Batch.from_file s)),
     "Run kamino in batch-mode with specification in FILE.");
    ("-batch-example",
     Arg.Unit (fun () ->
         Printf.printf "Example batch configuration:\n%s\n"
           (Sexplib.Sexp.to_string_hum (Batch.dump_example ()));
         exit 0),
     "Display an example batch configuration and exits."
    );
    ("-detailed-stats",
     Arg.Unit (fun () -> opt_detailed_stats := true),
     "Dump detailed stats (will consume a lot of disk space!)");
  ]

let print_usage_and_exit e =
  Arg.usage speclist (e ^ "\n" ^ usage);
  exit 1

let anon_arg str =
  try
    let input = Input.Parsers.parse_binary_spec str in
    inputs := input :: !inputs
  with Failure s -> raise (Arg.Bad s)

let generate_report_bbmgr ?runid path clusters =
  let filename = match runid with
    | Some n -> Printf.sprintf "run%d/clusters" n
    | None -> "clusters" in
  Outdir.with_file_out ~append:true filename (fun oc ->
    BatEnum.iter (fun (descr, elems) ->
      let name = Bb_cluster.cluster_name descr in
      let size = BatSet.cardinal elems in
      Printf.fprintf oc "%s %s  %d elements\n%!" path name size) clusters)

module HackMeUpScotty (BBMgr : Bb_cluster.BBClusterManagerSig) (Algo : Comparator.AlgoSig with type bbcluster_type := BBMgr.t and type bbcluster_key := Bb_cluster.ClusterHashtbl.key)  (Validator : Validation.Validator with type subgraph = Algo.Subgraph.t)
=
struct
  let handle_result ?id ~clname  num (subg : Algo.Subgraph.t) =
    let validate_result result =
      dprintf "--- VALIDATION START ---\n";
      let descr =
        let module Function = Function_info.Function in
        let afl, afr = Algo.Subgraph.afs subg in
        Printf.sprintf "match involving %s vs %s"
          (Function.to_string afl.Ktype.function_info)
          (Function.to_string afr.Ktype.function_info)
      in
      let validation_result = Validator.validate subg in
      dprintf "--- VALIDATION STOP ---\n";
      ignore(match validation_result with
          | BatResult.Bad str ->
            dprintf "Could not validate %s: %s" descr str
          | BatResult.Ok () ->
            dprintf "Validated %s" descr);
      validation_result
    in
    let validated =
      if !opt_validate_result then begin
        try
          begin
            match validate_result subg with
            | BatResult.Ok () -> `Validated
            | BatResult.Bad _ -> `FailedValidation
          end
        with Not_found -> (* XXX: this shouldn't reach us here! *)
          `FailedValidation
      end else begin
        `NotValidated
      end
    in
    let subdir = match validated with
      | `Validated -> "validated"
      | `NotValidated -> "not_validated"
      | `FailedValidation -> "failed_validation" in
    let resultdir = match id with
      | Some n -> Printf.sprintf "results/%d" n
      | None -> "results" in
    let key = Printf.sprintf "%s/%s/cluster_%s/%d" resultdir subdir clname num in
    let module Subg = Algo.Subgraph in
    Outdir.with_file_out (key ^ ".dot") (Subg.dump subg);
    Outdir.with_file_out (key ^ ".sexp") (fun oc ->
        output_string oc (Subg.to_string subg));
    let key = Printf.sprintf "%s/overview" resultdir in
    let open Sexplib in
    let validation_status = match validated with
      | `Validated -> Sexp.Atom "V"
      | `NotValidated -> Sexp.Atom "-"
      | `FailedValidation -> Sexp.Atom "X" in
    Outdir.with_file_out ~append:true key (fun oc ->
      let match_result = Cmpres.cfgcmp_res_to_sexp (Subg.res subg) in
      let flags = Subg.FlagsSet.elements (Subg.flags subg) in
      let flags = Std.sexp_of_list Cmpres.sexp_of_func_cmp_flags flags in
      let cluster = Sexp.List [Sexp.Atom "cluster"; Sexp.Atom clname] in
      let sexp = Sexp.List [Sexp.Atom "res"; match_result; cluster; flags;
                            validation_status]
      in
      let fmt = Format.formatter_of_out_channel oc in
      Sexp.pp_mach fmt sexp;
      Format.pp_print_newline fmt ();
      Format.pp_print_flush fmt ()
    )
end

let run_commandline, run_batch =
  let open Bb_cluster in
  let module EP = Embarassingly_parallel in
  let do_duplicated_commandline () =
    let module BBMgr = (val (Bb_cluster.bbclustermanagerfactory !opt_classifier) : BBClusterManagerSig) in
    let module Policy = (val (Comparator.matchingpolicyfactory
                                (module Comparator.BBCmpResRich : Comparator.BBCmpResSig)
                                !opt_matching_policy)
                          : Comparator.CfgMatchingPolicy)
    in
    let module Summarizer = Summary.Algo in
    let module Comparator = Comparator.Algo(BBMgr)(Policy) in
    let module Validator = Validation.SymbValidator(BBMgr)(Comparator) in
    let module Hack = HackMeUpScotty(BBMgr)(Comparator)(Validator) in
    if !inputs = [] then print_usage_and_exit "No input specified!";
    let toplevel_bench = new Perfacc.bench "toplevel" in
    toplevel_bench#start "";
    let cluster results aprog =
      let bbmgr = BBMgr.create aprog in
      let add_cluster func bb = BBMgr.add bbmgr func bb in
      BatEnum.iter (fun func -> BatEnum.iter (add_cluster func)
        (Bb.BBidMap.values func.Ktype.fbbs))
        (BatHashtbl.values aprog.Ktype.pfuncs);
      (aprog, bbmgr) :: results in
    let analyzed_binaries = List.rev (Summary.fold ~init:[] ~f:cluster !inputs) in
    match (Input.Parsers.parse_compare_strategy !opt_compare_strategy) with
    | `CombinatorialComparison ->
      let do_comparison () =
        if !opt_detailed_stats then begin
          let key = "detailed_stats" in
          Perfacc.set_bench_dump_key (Some key)
        end;
        ignore(BatList.reduce (fun left right ->
            let results, ewbs = Comparator.compare (Comparator.init ()) left right in
            List.iter (fun (desc, subgraphs) ->
                ignore(List.fold_left (fun acc subg ->
                    let clname = Bb_cluster.cluster_name desc in
                    Hack.handle_result ~clname acc subg;
                    acc + 1) 0 subgraphs)) results;
            if List.length ewbs > 0 then begin
              let str = EP.exns_with_bts_to_string ewbs in
              Printf.eprintf "--- Got %d exceptions from workers ---\n%s\n---\n"
                (List.length ewbs) str;
              failwith "exceptions"
            end;
            right) analyzed_binaries)
      in
      Misc.finally toplevel_bench#stop do_comparison ()
    | _ -> failwith "Unexpected mismatch on compare strategy!"
  in
  let do_duplicated_batch batch =
    let open Bb_cluster in
    let module BBMgr = (val (Bb_cluster.bbclustermanagerfactory "ByTag") : BBClusterManagerSig) in
    let module Summarizer = Summary.Algo in
    let module Policy = (val (Comparator.matchingpolicyfactory
                                (module Comparator.BBCmpResRich : Comparator.BBCmpResSig)
                                !opt_matching_policy)
                          : Comparator.CfgMatchingPolicy)
    in
    let module Comparator = Comparator.Algo(BBMgr)(Policy) in
    let module Validator = Validation.SymbValidator(BBMgr)(Comparator) in
    let module Hack = HackMeUpScotty(BBMgr)(Comparator)(Validator) in

    let toplevel_bench = new Perfacc.bench "toplevel" in
    toplevel_bench#start "";
    let gen_tags run =
      let binary_names = List.map (fun binary_spec ->
        FilePath.basename (Input.BinaryPath.to_string binary_spec.Input.path))
        (Batch.Run.binaries run) in
      let tags = BatHashtbl.create 128 in
      let add_tags inline_info =
        let add_by_binid ~binid addr tag = match Misc.bathashtbl_find_option tags binid with
          | Some tags' -> BatHashtbl.replace tags binid ((addr, tag) :: tags')
          | None -> BatHashtbl.add tags binid ((addr,tag) :: [])
        in
        let open Batch.Run in
        let {parent} = inline_info in
        let {out_of_line_copy} = inline_info in
        let {binary_idx; name; addr} = parent in
        let {binary_idx=binary_idx'; name=name'; addr=addr'} =
          out_of_line_copy in
        let tag = Printf.sprintf "%s-%s-%Lx--%s-%s-%Lx"
          (List.nth binary_names binary_idx) name addr
          (List.nth binary_names binary_idx') name' addr'
        in
        add_by_binid ~binid:binary_idx addr tag;
        add_by_binid ~binid:binary_idx' addr' tag;
      in
      List.iter add_tags (Batch.Run.inlines run);
      tags
    in
    let add_tag bbmgr idx (addr, tag) =
      Printf.eprintf "Assigning tag %s to 0x%Lx for binary %i\n" tag addr idx;
      BBMgr.add_config bbmgr (Int64.to_string addr) tag in
    let cluster runid tags (results, idx) aprog =
      Printf.eprintf "Clustering tags for %s (%d)\n" aprog.Ktype.pname
        idx;
      let bbmgr = BBMgr.create aprog in
      ignore(match Misc.bathashtbl_find_option tags idx with
      | Some tags -> List.iter (fun (addr, tag) ->
        Printf.eprintf "Adding tag %s\n" tag;
        add_tag bbmgr idx (addr,tag)) tags
      | None -> failwith (Printf.sprintf "No tags for binary %i" idx));
      let add_cluster func bb = BBMgr.add bbmgr func bb in
      BatEnum.iter (fun func -> BatEnum.iter (add_cluster func)
        (Bb.BBidMap.values func.Ktype.fbbs))
        (BatHashtbl.values aprog.Ktype.pfuncs);
      generate_report_bbmgr ~runid aprog.Ktype.pname (BBMgr.enum bbmgr);
    (* Note that we add the results in reverse order! *)
      ((aprog, bbmgr) :: results, idx + 1) in
    let analyze_run run_id run =
      let tags = gen_tags run in
      let analyzed_binaries,_ = Summary.fold ~runid:run_id
        ~init:([],0)
        ~f:(cluster run_id tags)
        (Batch.Run.binaries run) in
      let analyzed_binaries = List.rev analyzed_binaries in
      let pair_list_elems_exn l =
        let rec aux acc = function
          | [] -> acc
          | h :: h' :: t -> aux ((h, h') :: acc) t
          | _ ->
             failwith "Cannot pair list elements on a list with odds number of elements!"
        in
        List.rev (aux [] l) in
      let paired_analyzed_binaries = pair_list_elems_exn
        analyzed_binaries in
      match (Input.Parsers.parse_compare_strategy !opt_compare_strategy) with
      | `CombinatorialComparison ->
         let do_comparison () =
           List.iter (fun ((prog, bbmgr), (prog', bbmgr')) ->
             Printf.eprintf "Going to compare %s(%d) with %s(%d)\n"
               prog.Ktype.pname (BatEnum.count (BBMgr.keys bbmgr))
               prog'.Ktype.pname (BatEnum.count (BBMgr.keys bbmgr'));
             let results, ewbs = Comparator.compare
               (Comparator.init ()) (prog, bbmgr) (prog', bbmgr') in
             List.iter (fun (desc, subgraphs) ->
               ignore(List.fold_left (fun acc subg ->
                 let clname = Bb_cluster.cluster_name desc in
                 Hack.handle_result ~id:run_id ~clname acc subg;
                 acc + 1) 0 subgraphs)) results;
             if List.length ewbs > 0 then begin
               let str = EP.exns_with_bts_to_string ewbs in
               Printf.eprintf "--- Got %d exceptions from workers ---\n%s\n---\n"
                 (List.length ewbs) str;
               failwith "exceptions"
             end;
           ) paired_analyzed_binaries
         in
         do_comparison ()
      | _ -> failwith "Unexpected mismatch on compare strategy!"
    in
    let analyze_runs batch =
      ignore(List.fold_left
        (fun run_id run ->
          if !opt_detailed_stats then begin
            let key = Printf.sprintf "run%d/detailed_stats" run_id in
            Outdir.with_file_out (key ^ "/" ^ "run_descr") (fun oc ->
                let sexp = Batch.Run.sexp_of_t run in
                let fmt = Format.formatter_of_out_channel oc in
                Sexplib.Sexp.pp_hum fmt sexp;
                Format.pp_print_newline fmt ();
                Format.pp_print_flush fmt ();
              );
            Perfacc.set_bench_dump_key (Some key)
          end;
          analyze_run run_id run;
          Perfacc.set_bench_dump_key None;
          run_id + 1
        ) 0 (Batch.runs batch)) in
    let final exn =
      let inner_final () =
        match exn with
        | Some exn -> raise exn
        | None -> ()
      in
      Misc.finally inner_final toplevel_bench#stop ()
    in
    Misc.finally_with_exn final analyze_runs batch
  in
  (do_duplicated_commandline, do_duplicated_batch)

let main () =
  ignore(Gc.create_alarm (fun () ->
      if !opt_gc_stats then
        Gc.print_stat stderr
    ));
  Printexc.record_backtrace true;
  Pp.output_varnums := true;
  Arg.parse speclist anon_arg usage;
  Printf.printf "Allowed running time is %d seconds\n" !opt_timeout;
  flush stdout;
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ ->
      Printf.eprintf "Exceeded allowed execution time (%d seconds)\n"
        !opt_timeout;
      exit 7
    ));
  ignore(Unix.alarm !opt_timeout);
  match !opt_mode with
  | CommandlineMode -> run_commandline ()
  | BatchMode b -> run_batch b

let toplevel_finalizer e =
  Outdir.with_file_out "gc_stats" (fun out ->
      Gc.print_stat out);
  Outdir.with_file_out "result.log" (fun out ->
      match e with
      | Some exn ->
        output_string out (Printexc.to_string exn);
        output_string out "\n";
        Printexc.print_backtrace out;
      | None -> output_string out "success!")

let () = Misc.finally_with_exn toplevel_finalizer main ()
