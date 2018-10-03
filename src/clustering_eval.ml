open Lwt
open Core.Std

let debug_f = Lwt_log.debug_f
let info_f = Lwt_log.info_f
let notice_f = Lwt_log.notice_f
let warning_f = Lwt_log.warning_f

let debugdir = ref None

let with_dir_in_debugdir desc f =
  let d = match !debugdir with
    | None -> Filename.temp_dir desc "clustering_eval"
    | Some debugdir -> Filename.temp_dir ~in_dir:debugdir desc "clustering_eval"
  in
  FileUtil.mkdir d;
  f d >>= (fun ret ->
      (match !debugdir with
       | None -> FileUtil.rm ~recurse:true ~force:FileUtil.Force [d]
       | _ -> ());
      Lwt.return ret)

let cmd_to_s (_, argv) =
  let argv = Array.to_list argv in
  String.concat ~sep:" " argv

module Lwt_process_runner =
struct
  let process_creation_tokens =
    let counter = ref 0 in
    let f () =
      counter := !counter + 1;
      Lwt.return !counter
    in
    Lwt_pool.create 16 f

  let run_cmd ?stdin:(stdin=`Keep) ?stdout:(stdout=`Keep)
                        ?stderr:(stderr=`Keep) cmd =
    debug_f "EXEC: %s\n" (cmd_to_s cmd)
    >>= (fun () ->
        Lwt_pool.use process_creation_tokens (fun tok ->
            debug_f "Using tok %d\n" tok
            >>= (fun () ->
                Lwt_process.exec ~stdin ~stdout ~stderr cmd)))
end

module Subject =
struct
  type t = {
    builddir : string;
    cc : string;
    ccv : string;
    prim : string;
    impl : string;
    sym : string;
    param : string;
    addr : string;
  }
  let sym ~prim ~impl =
    Printf.sprintf "%s_%s" impl prim
  let binary_name t =
    Printf.sprintf "%s-%s-%s-%s" t.cc t.ccv t.param t.prim
  let binary_path t =
    Printf.sprintf "%s/%s/%s" t.builddir t.prim (binary_name t)
  let to_s t = Printf.sprintf "%s.%s.%s.%s.%s" t.cc t.ccv t.param t.prim t.impl
  let short t = t.param
  let to_key = to_s
  let compare s1 s2 =
    String.compare (to_key s1) (to_key s2)
  let hash t = String.hash (to_s t)

  let create ~builddir ~cc ~ccv ~prim ~impl ~param  =
    let ret = {
      cc;
      ccv;
      prim;
      impl;
      sym = sym ~prim ~impl;
      param;
      builddir;
      addr = "0";
    } in
    let open FileUtil in
    if test Is_file (binary_path ret) then begin
      let addr = Sym_resolver.symbol_address (binary_path ret)
          (sym ~prim ~impl) in
      let addr = Printf.sprintf "%Ld" addr in
      Some {ret with addr}
    end else begin
      None
    end

  let gen_batch s1 s2 =
    Printf.sprintf "
((version 1)
 (runs
  (((binaries
     (((path %s) (parameters ()))
      ((path %s) (parameters ()))))
    (inlines
     (((parent ((binary_idx 0) (name %s) (addr %s)))
       (out_of_line_copy
        ((binary_idx 1) (name %s) (addr %s))))))))))"
      (binary_path s1) (binary_path s2)
      s1.sym s1.addr
      s2.sym s2.addr

end

let make_executable_copy path =
    let tf = Filename.temp_file "copy" (Filename.basename path) in
    FileUtil.cp ~force:FileUtil.Force ~recurse:false ~preserve:true [path] tf;
    FileUtil.chmod (`Symbolic [
      `User (`Set (`List [`Read; `Exec]));
      `Group (`Remove (`List [`Read; `Write; `Exec]));
      `Other (`Remove (`List [`Read; `Write; `Exec]))]) [tf];
    tf

let check_process_status cmd st =
  let open Unix in
  let ret = Exit_or_signal.of_unix st in
  match ret with
  | Ok () ->
    Lwt.return ret
  | err ->
    debug_f "%s: %s" (cmd_to_s cmd) (Exit_or_signal.to_string_hum err)
    >>= (fun () ->
        Lwt.return ret)

let kamino_finished outdir =
  let open FileUtil in
  let resultpath = Printf.sprintf "%s/%s" outdir "result.log" in
  if not (test Is_file resultpath) then begin
    Lwt_io.eprintf "Kamino finished but no %s\n" resultpath >|= (fun () ->
        false)
  end else begin
    let res = In_channel.read_all resultpath in
    if not (String.equal res "success!") then begin
      Lwt_io.eprintf "Kamino threw an exception\n" >|= (fun () ->
          false)
    end else begin
      Lwt.return true
    end
  end

let write_batch ~id s1 s2 =
  try
    begin
      let batchpath, oc = Filename.open_temp_file "batch" id in
      let batch = Subject.gen_batch s1 s2 in
      Out_channel.output_string oc batch;
      Out_channel.flush oc;
      Out_channel.close oc;
      batchpath
    end
  with Sys_error _ ->
    (* FD leak diagnostics *)
    ignore(Sys.command (Printf.sprintf "ls -l /proc/%d/fd" (Unix.getpid () |! Pid.to_int)));
    exit 1

module TrivialEquiv =
struct
  type t = {
    path : string;
  }
  let create path =
    {path = make_executable_copy path;}
  let equivalent t s1 s2 : bool Lwt.t =
    let comparison = Printf.sprintf "trivial+%s--%s" (Subject.to_s s1) (Subject.to_s s2) in
    debug_f "trivial-equiv %s\n" comparison >>= (fun () ->
        let batchpath = write_batch "triv" s1 s2 in
        Lwt.finalize (fun () ->
            with_dir_in_debugdir comparison (fun outdir ->
                let logpath = Printf.sprintf "%s/%s" outdir "triv-equiv.log" in
                let logfd = Unix.openfile
                    ~mode:[Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] logpath
                in
                let cmd = (t.path,
                           [|
                             t.path;
                             "-b"; batchpath;
                           |])
                in
                Lwt_process_runner.run_cmd
                    ~stdin:`Keep
                    ~stdout:(`FD_move logfd)
                    ~stderr:(`Dev_null)
                    cmd
                >>= (check_process_status cmd)
                >>= (function
                    | Ok () ->
                      Lwt.return (String.is_suffix ~suffix:": identical\n"
                                    (In_channel.read_all logpath))
                    | _ ->
                      Lwt.return false
                  )
              )
          ) (fun () ->
            Lwt.return (FileUtil.rm ~force:FileUtil.Force [batchpath])))
end

let equiv_trivial =
  let base = Filename.dirname (Filename.realpath Sys.executable_name) in
  let triv = Printf.sprintf
      "%s/../../_obuild/trivial-equiv/trivial-equiv.asm" base
  in
  TrivialEquiv.create triv

module KaminoEquiv =
struct
  type t = {
    path : string;
    cache : bool String.Table.t;
    cache_lookups : int ref;
    cache_hits : int ref;
  }
  let stats t =
    Printf.sprintf "KaminoEquiv.cache: %d/%d hits (%.2f%% hit rate)"
      !(t.cache_hits) !(t.cache_lookups)
      (100. *. (Float.of_int !(t.cache_hits)) /.
       (Float.of_int !(t.cache_lookups)))

  let create path =
    {
      path = make_executable_copy path;
      cache = String.Table.create () ~size:10000;
      cache_lookups = ref 0;
      cache_hits = ref 0;
    }
  let comparison_key ~s1 ~s2 =
    match List.sort Subject.compare [s1; s2] with
    | [s1; s2] ->
      Printf.sprintf "%s--%s" (Subject.to_key s1) (Subject.to_key s2)
    | _ ->
      failwith "can't possibly happen"

  let find_in_cache t ~s1 ~s2 =
    let ret = String.Table.find t.cache (comparison_key ~s1 ~s2) in
    t.cache_lookups := !(t.cache_lookups) + 1;
    if Option.is_some ret then begin
      t.cache_hits := !(t.cache_hits) + 1;
    end;
    ret

  let add_to_cache t ~s1 ~s2 value =
    String.Table.change t.cache (comparison_key ~s1 ~s2) (function
        | Some prev ->
          failwith "Comparison was already cached"
        | None ->
          Some value)

  let do_equivalent t s1 s2 =
    let comparison = Printf.sprintf "kamino+%s--%s" (Subject.to_s s1) (Subject.to_s s2) in
    debug_f "kamino %s\n" comparison >>= (fun () ->
        let batchpath = write_batch "kamino" s1 s2 in
        Lwt.finalize (fun () ->
            with_dir_in_debugdir comparison (fun outdir ->
                let logpath = Printf.sprintf "%s/%s" outdir "kamino.log" in
                let logfd = Unix.openfile
                    ~mode:[Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] logpath
                in
                let cmd = (t.path,
                           [|
                             t.path;
                             "-no-fork";
                             "-timeout"; "30m";
                             "-batch"; batchpath;
                             "-outdir"; outdir;
                           |])
                in
                Lwt_process_runner.run_cmd
                    ~stdin:`Keep
                    ~stdout:(`FD_move logfd)
                    ~stderr:(`FD_move (Unix.dup logfd))
                    cmd
                >>= (check_process_status cmd)
                >>= (function
                    | Error _ ->
                      (* Kamino exited with a non-zero status, likely b/c it hit an
                       * exception. Count this as "not able to prove equivalence"
                       * and keep going.
                       *)
                      Lwt.return false
                    | Ok () ->
                      begin
                        kamino_finished outdir >>= (fun kamino_finished ->
                            if not kamino_finished then begin
                              Lwt.return false
                            end else begin
                              let open FileUtil in
                              let overviewpath = Printf.sprintf "%s/results/0/overview"
                                  outdir
                              in
                              if not (test Is_file overviewpath) then begin
                                warning_f "No overview %s\n" overviewpath >|= (fun () ->
                                false)
                              end else begin
                                let lines = In_channel.read_lines overviewpath in
                                let re = Str.regexp ".*[ ]ExactOnly[ ]*(OverlapTotal[ ]+" in
                                Lwt.return (List.exists lines ~f:(fun l ->
                                    Str.string_match re l 0
                                  ))
                              end
                            end)
                      end
                  )
              )
          ) (fun () ->
            Lwt.return (FileUtil.rm ~force:FileUtil.Force [batchpath])))
  let equivalent t s1 s2 =
    match find_in_cache t s1 s2 with
    | Some x -> Lwt.return x
    | None ->
      do_equivalent t s1 s2
      >>= (fun res ->
          add_to_cache t s1 s2 res;
          Lwt.return res)
end

let equiv_kamino =
  let base = Filename.dirname (Filename.realpath Sys.executable_name) in
  let triv = Printf.sprintf
      "%s/../../_obuild/kamino/kamino.asm" base
  in
  KaminoEquiv.create triv

module Cluster : sig
  type t
  val to_s : t -> string
  val short : t -> string
  val create : Subject.t -> t
  val merge : t -> t -> t
  val any_subject : t -> Subject.t
  val reduce_parallel : (t -> t -> bool Lwt.t) -> t list -> t list Lwt.t
  val equivalent_single : (Subject.t -> Subject.t -> bool Lwt.t) -> t -> t -> bool Lwt.t
  val equivalent_exhaustive : (Subject.t -> Subject.t -> bool Lwt.t) -> t -> t -> bool Lwt.t
end  =
struct
  type t = {
    subjects : (Subject.t, Comparator.Poly.comparator) Set.t;
  }
  let stringize f t =
    let s = String.concat ~sep:", "
      (List.map (Set.to_list t.subjects) ~f) in
    Printf.sprintf "<%s>" s
  let to_s = stringize Subject.to_s
  let short = stringize Subject.short
  let create s = { subjects = Set.singleton ~comparator:Comparator.Poly.comparator s}
  let merge t other =
    {subjects = Set.union t.subjects other.subjects}

  let any_subject {subjects} = match Set.min_elt subjects with
    | None -> failwith "Empty cluster!" (* Clusters are non-empty by construction *)
    | Some s -> s
  let reduce tester clusters : t list Lwt.t =
    let rec find_add ~equiv acc buckets cl : t list Lwt.t =
      Lwt.bind buckets (function
      | bucket :: rest ->
        Lwt.bind (equiv cl bucket) (fun equivalent ->
            if equivalent then begin
              Lwt.return (rest @ ((merge cl bucket) :: acc))
            end else begin
              find_add ~equiv (bucket :: acc) (Lwt.return rest) cl
            end)
      | [] ->
        Lwt.return (cl :: acc))
    in
    let rec do_cluster ~equiv buckets clusters : t list Lwt.t =
      match clusters with
      | [] ->
        buckets
      | cl :: rest ->
        let buckets = find_add ~equiv [] buckets cl in
        do_cluster ~equiv buckets rest
    in
    debug_f "Cluster.reduce %d\n" (List.length clusters) >>= (fun () ->
        do_cluster ~equiv:tester (Lwt.return []) clusters)

  let reduce_parallel tester clusters =
    let rec inner clusters =
      let len = List.length clusters in
      assert (len > 0);
      if len = 1 then begin
        Lwt.return clusters
      end else if len = 2 then begin
        reduce tester clusters
      end else begin
        let a, b = List.split_n clusters (len / 2) in
        Lwt.bind (Lwt_list.map_p inner [a; b;])
          (function
            | [a; b] ->
              reduce tester (a @ b)
            | _ ->
              failwith "Can't possibly happen")
      end
    in
    debug_f "reduce_parallel\n" >>= (fun () ->
        inner clusters)

  let equivalent_single equiv cl1 cl2 =
    let el1 = any_subject cl1 in
    let el2 = any_subject cl2 in
    equiv el1 el2 >>=
    (fun ret ->
       debug_f "Cluster.equivalent_single: %s VS %s: %b"
         (short cl1) (short cl2) ret
       >>= (fun () ->
           Lwt.return ret))

  let equivalent_exhaustive equiv cl1 cl2 =
    List.cartesian_product (Set.to_list cl1.subjects) (Set.to_list cl2.subjects)
    |! (Lwt_list.exists_s (fun (s1, s2) ->
        equiv s1 s2))
end

let subjects_of_config ~configpath ~builddir ~cc ~ccv ~prim ~impl ~param =
  let cfg = Yojson.Basic.from_file configpath in
  let open Yojson.Basic.Util in
  let param_json =
    cfg |> member "available_parameters" |> member param
  in
  let param_space = param_json |> member "space" |> (function
      | `List values -> List.map values to_string
      | _ -> failwith "bad param")
  in
  List.map param_space (fun param ->
      Subject.create ~builddir ~cc ~ccv ~prim ~impl ~param)

let subjects_of_config2 ~configpath ~builddir ~prim ~impl ~param =
  let cfg = Yojson.Basic.from_file configpath in
  let open Yojson.Basic.Util in
  let param_json =
    cfg |> member "available_parameters" |> member param
  in
  let descr_fmt = param_json |> member "descr_fmt" |> to_string in
  let param_values = param_json |> member "space" |> to_list |>
                     List.map ~f:(fun value ->
                         Str.global_replace (Str.regexp "@") (to_string value) descr_fmt)
  in
  let compilers = cfg |> member "compilers" |> to_list in
  let ccvs = List.concat_map compilers ~f:(fun compiler_json ->
      let ccname = compiler_json |> member "name" |> to_string in
      let ccversions = compiler_json |> member "versions" |> to_list in
      List.filter_map ccversions (fun ccv_json ->
          let maj = ccv_json |> member "major" |> to_string in
          let min = ccv_json |> member "minor" |> to_string in
          let patch = ccv_json |> member "patch" |> to_string in
          if String.equal patch "0" then begin
                Some (ccname, Printf.sprintf "%s.%s.0" maj min)
          end else begin
            None
          end))
  in
  let primitives_json =
    cfg |> member "primitives" |> to_list |>
    List.filter ~f:(fun prim_json ->
        match prim with
        | None ->
          true
        | Some prim ->
          begin
            let prim_name = prim_json |> member "name" |> to_string in
            String.equal prim_name prim
          end)
  in
  primitives_json |> List.concat_map ~f:(fun prim_json ->
      let prim = prim_json |> member "name" |> to_string in
      let impls = prim_json |> member "implementations" |>
                  to_list |> List.map ~f:to_string in
      let impls = match impl with
        | None -> impls
        | Some impl -> List.filter impls ~f:(String.equal impl)
      in
      List.concat_map impls ~f:(fun impl ->
          List.map ccvs ~f:(fun (cc, ccv) ->
              List.map param_values ~f:(fun param ->
                  Subject.create ~builddir ~cc ~ccv ~prim ~impl ~param))))

let print_clusters subjects clusters =
  info_f "%d clusters from %d subjects\n"
    (List.length clusters) (List.length subjects)
  >>= (fun () ->
      Lwt_list.iter_s (fun cl ->
          info_f "%s" (Cluster.short cl)) clusters)
  >>= (fun () ->
      Lwt.return clusters)

type subject_set_result = {
  nr_clusters_initial : int;
  nr_clusters_after_trivial : int;
  nr_clusters_after_kamino : int;
}

let subject_set_result_to_s r =
  Printf.sprintf "%d\t%d\t%d" r.nr_clusters_initial
    r.nr_clusters_after_trivial r.nr_clusters_after_kamino

let do_subject_set cluster_equivalent subjects =
  let clusters = List.filter_map subjects
      ~f:(fun s -> Option.map s Cluster.create) in
  let result = {
    nr_clusters_initial = List.length clusters;
    nr_clusters_after_trivial = 0;
    nr_clusters_after_kamino = 0;
  } in
  info_f "%d clusters from %d subjects\n"
    (List.length clusters) (List.length subjects)
  >>= (fun () ->
      Cluster.reduce_parallel
        (cluster_equivalent (TrivialEquiv.equivalent equiv_trivial))
        clusters)
  >>= (print_clusters subjects)
  >>=
  (fun clusters ->
     let result = {result with nr_clusters_after_trivial = List.length clusters;} in
     let clusters = Cluster.reduce_parallel
         (cluster_equivalent (KaminoEquiv.equivalent equiv_kamino))
         clusters
     in
     Lwt.return (clusters, result)
  )
  >>= (fun (clusters, result) ->
      clusters >>=
      (print_clusters subjects)
      >>=
      (fun clusters ->
         Lwt.return (clusters,
                     {result with
                      nr_clusters_after_kamino = List.length clusters;})))


let print_stats kamino = notice_f "%s\n" (KaminoEquiv.stats kamino)

let do_verbosity_flags ~verbose ~debug =
  if debug then begin
    Lwt_log.add_rule "*" Lwt_log.Debug
  end else if verbose then begin
    Lwt_log.add_rule "*" Lwt_log.Info
  end else begin
    Lwt_log.add_rule "*" Lwt_log.Notice
  end

let select_cluster_equivalence strategy =
  if String.equal "single" strategy then begin
    Cluster.equivalent_single
  end else if String.equal "exhaustive" strategy then begin
    Cluster.equivalent_exhaustive
  end else begin
    Printf.eprintf "Invalid equivalence strategy: '%s'" strategy;
    exit 2
  end

let do_single verbose debug strategy configpath cc ccv prim impl
    builddir param opt_debugdir () =
  do_verbosity_flags ~verbose ~debug;
  let cluster_equivalence = select_cluster_equivalence strategy in
  (match opt_debugdir with
  | None -> ()
  | Some p -> debugdir := Some p);
  let subjects = subjects_of_config ~configpath ~builddir ~cc ~ccv ~prim ~impl ~param in
  do_subject_set cluster_equivalence subjects
  >>=
  (fun (clusters, result) ->
     print_stats equiv_kamino
     >>= (fun () ->
         Lwt_io.printf "%s\t%s\t%s-%s\t%s\n"
           prim impl cc ccv
           (subject_set_result_to_s result)))
  |!
  Lwt_main.run

let single_command =
  Command.basic ~summary:"Eval a single primitive, implementation"
    Command.Spec.(
      empty
      +> flag "-v" no_arg ~doc:" Produce verbose output"
      +> flag "-d" no_arg ~doc:" Produce debug output"
      +> flag "-e" (optional_with_default "single" string)
        ~doc:"<strategy Cluster equivalence testing strategy [single|exhaustive]"
      +> flag "-C" (required string) ~doc:"<path> Path to config file"
      +> flag "-c" (required string) ~doc:"<cc> Compiler (e.g. gcc)"
      +> flag "-V" (required string) ~doc:"<ccver> Compiler version (e.g. 3.4.0)"
      +> flag "-p" (required string) ~doc:"<prim> Primitive (e.g. memcpy)"
      +> flag "-i" (required string) ~doc:"<impl> Implementation (e.g. musl)"
      +> flag "-b" (required string) ~doc:"<path> Path to build dir"
      +> flag "-P" (required string) ~doc:"<param> Parameter name (e.g. march)"
      +> flag "-D" (optional string) ~doc:"<path> Path to dump debug info in"
    )
    do_single

let do_multi verbose debug strategy configpath prim impl builddir param opt_debugdir () =
  do_verbosity_flags ~verbose ~debug;
  let cluster_equivalence = select_cluster_equivalence strategy in
  (match opt_debugdir with
  | None -> ()
  | Some p -> debugdir := Some p);
  let subjects : Subject.t option list list = subjects_of_config2 ~configpath ~builddir ~prim ~impl ~param in
  Lwt_list.map_p (fun (subjects : Subject.t option list) ->
      do_subject_set cluster_equivalence subjects
      >>= (fun (final_clusters, result) ->
          let a_subject = List.hd_exn final_clusters |! Cluster.any_subject in
          Lwt_io.printf "%s\t%s\t%s-%s\t%s\n"
            a_subject.Subject.prim a_subject.Subject.impl
            a_subject.Subject.cc a_subject.Subject.ccv
            (subject_set_result_to_s result)
          >>= (fun () ->
            Lwt.return (final_clusters, result)))
    ) subjects
  >>= (fun _ ->
      Lwt.return ())
  |!
  Lwt_main.run

let multi_command =
  Command.basic ~summary:"Eval multiple (cc, ccv, primitive, implementation) combos"
    Command.Spec.(
      empty
      +> flag "-v" no_arg ~doc:" Produce verbose output"
      +> flag "-d" no_arg ~doc:" Produce debug output"
      +> flag "-e" (optional_with_default "single" string)
        ~doc:"<strategy Cluster equivalence testing strategy [single|exhaustive]"
      +> flag "-C" (required string) ~doc:"<path> Path to config file"
      +> flag "-p" (optional string) ~doc:"<prim> Primitive (e.g. memcpy)"
      +> flag "-i" (optional string) ~doc:"<impl> Implementation (e.g. musl)"
      +> flag "-b" (required string) ~doc:"<path> Path to build dir"
      +> flag "-P" (required string) ~doc:"<param> Parameter name (e.g. march)"
      +> flag "-D" (optional string) ~doc:"<path> Path to dump debug info in"
    )
    do_multi

let suite =
  Command.group ~summary:"Cross-march evaluator"
    [
      ("single", single_command);
      ("multi", multi_command);
    ]

let () =
  Command.run ~version:"0.1" suite
