open Core.Std
open Core_extended.Std

open Cmpres
open Eval_cluster

type reference = Path of string | Commit of string


let result_to_string = function
  | Some res -> Cmpres.cfgcmp_res_to_string res
  | None -> "FAIL"

let float_of_rational (n, d) =
  let open Float in
  let n = of_int n in
  let d = of_int d in
  n /. d

let cmp_rational (n1, d1) (n2, d2) =
  (*
   * If we multiply each fraction with the other's denominator,
   * then we can just subtract the transformed nominators.
   *)
  n1 * d2 - n2 * d1

let cmp_result r1 r2 =
  (*
   * Fails are small, successes are large. Subset and Superset
   * rank equal, the #BBs breaks ties.
   *)
  let cmp_overlap o1 o2 = match o1, o2 with
    | OverlapTotal n1, OverlapTotal n2 -> n1 - n2
    | OverlapTotal _, _ -> 1
    | OverlapSuperset _, OverlapTotal _ -> -1
    | OverlapSuperset n1, OverlapSuperset n2 -> n1 - n2
    | OverlapSuperset n1, OverlapSubset n2 -> n1 - n2
    | OverlapSuperset _, OverlapPartial _ -> 1
    | OverlapSubset _, OverlapTotal _ -> -1
    | OverlapSubset n1, OverlapSuperset n2 -> n1 - n2
    | OverlapSubset n1, OverlapSubset n2 -> n1 - n2
    | OverlapSubset _, OverlapPartial _ -> 1
    | OverlapPartial r1, OverlapPartial r2 -> cmp_rational r1 r2
    | OverlapPartial _, _ -> -1
  in
  match r1, r2 with
  | None, Some _ -> -1
  | Some _, None -> 1
  | None, None -> 0
  | Some {fuzziness = fuzziness1; overlap = overlap1},
    Some {fuzziness = fuzziness2; overlap = overlap2} ->
    begin
      match fuzziness1, fuzziness2 with
      | ExactOnly, ExactOnly ->
        cmp_overlap overlap1 overlap2
      | ExactOnly, _ ->
        1
      | SupersetAndExact, ExactOnly ->
        -1
      | SupersetAndExact, SupersetAndExact
      | SupersetAndExact, SubsetAndExact ->
        cmp_overlap overlap1 overlap2
      | SupersetAndExact, Fuzzy _ ->
        1
      | SubsetAndExact, ExactOnly ->
        -1
      | SubsetAndExact, SupersetAndExact
      | SubsetAndExact, SubsetAndExact ->
        cmp_overlap overlap1 overlap2
      | SubsetAndExact, Fuzzy _ ->
        1
      | Fuzzy f1, Fuzzy f2 -> compare f1 f2
      | Fuzzy _, _ -> -1
    end


let float_of_string s = Scanf.sscanf s "%f" Fn.id
let int_of_string s = Scanf.sscanf s "%i" Fn.id
let list_to_pair l =
  assert (List.length l = 2);
  (List.nth_exn l 0, List.nth_exn l 1)
let rational_of_string s = list_to_pair (List.map ~f:int_of_string (String.split ~on:'/' s))

let parse_validated = function
  | "-"  -> Result.Ok  `Unvalidated
  | "V" -> Result.Ok `Satisfiable
  | "X" -> Result.Ok `Unsatisfiable
  | _ as s -> Result.Error (Error.of_string (Printf.sprintf "Invalid validation flag %s" s))

let progmap_of_workdir path =
  let open FileUtil in
  (* We're interested in both executables and libraries *)
  let elf_magic_re = Str.regexp "^ELF 32-bit LSB.*not stripped$" in

  let is_elf path =
    let m = Magic.make [] in
    let descr = Magic.file m path in
    Str.string_match elf_magic_re descr 0
  in
  let binary_paths = find (And (Is_file, Custom is_elf)) path
      (fun acc binpath ->
         binpath :: acc) []
  in
  let map = Map.empty ~comparator:String.comparator in
  let map = List.fold_left ~init:map ~f:(fun map path ->
      let base = FilePath.basename path in
      match Map.find map base with
      | Some prevpath ->
        let s = Printf.sprintf "Duplicate binaries: %s %s" prevpath path in
        failwith s
      | None ->
        Map.add map base path) binary_paths
  in
  Map.find map

let progmap_of_clusters getpaths clusters =
  let add map path =
    let base = FilePath.basename path in
      match Map.find map base with
      | Some prevpath ->
        if String.compare prevpath path <> 0 then begin
          let s = Printf.sprintf "Duplicate binaries: %s %s" prevpath path in
          failwith s
        end else begin
          map
        end
      | None ->
        Map.add map base path
  in
  let map = Map.empty ~comparator:String.comparator in
  let map = List.fold_left ~init:map ~f:(fun map cluster ->
      let p1, p2 = getpaths cluster in
      let map = add map p1 in
      add map p2) clusters
  in
  Map.find map

module type BaseSig =
sig
  type cluster
  type overview = {
    result: cfgcmp_res option;
    cluster: cluster;
    validated: [ `Satisfiable | `Unsatisfiable | `Unvalidated ];
    flags : func_cmp_flags list
  }
  val collect_overviews : string -> (overview list, Error.t) Result.t
  val create_cluster_table_from_overviews : overview list -> overview Int.Table.t
end

module Base(Cluster : ClusterSig) =
struct
  type cluster = Cluster.t
  type overview = {
    result: cfgcmp_res option;
    cluster: Cluster.t;
    validated: [ `Satisfiable | `Unsatisfiable | `Unvalidated ];
    flags : func_cmp_flags list
  }

  let parse_overview_line progmap line =
    let open Sexplib.Sexp in
    let sexp = of_string line in
    match sexp with
    | List [Atom "res";
            cfgcmp;
            List [Atom "cluster"; Atom cluster];
            flags;
            Atom validated] ->
      begin
        let open Result in
        match (Cluster.parse progmap cluster, parse_validated validated) with
        | Ok cluster, Ok validated ->
          Ok {
            result = Some (Cmpres.cfgcmp_res_of_sexp cfgcmp);
            cluster;
            validated;
            flags = Sexplib.Std.list_of_sexp Cmpres.func_cmp_flags_of_sexp flags;
          }
        | (Error _ as err), _
        | _, (Error _ as err) ->
          err
      end
    | _ ->
      let s = Printf.sprintf "Invalid overview line: %s" line in
      Result.Error (Error.of_string s)

  let parse_batch path =
    let batch = Batch.from_file path in
    let collect_clusters_from_run acc run =
      let paths = List.map ~f:(fun spec -> Input.BinaryPath.to_string spec.Input.path)
          (Batch.Run.binaries run) in
      let _, ipaths = List.fold_left ~init:(0, []) ~f:(fun (i, acc) path ->
          (i + 1, ((i, path) :: acc))) paths in
      let pathmap = Map.of_alist_exn ~comparator:Int.comparator ipaths in
      let inline_to_cluster = Cluster.of_inline (Map.find_exn pathmap) in
      acc @ (List.map ~f:inline_to_cluster (Batch.Run.inlines run))
    in
    Or_error.combine_errors (List.fold_left ~init:[] ~f:collect_clusters_from_run
                               (Batch.runs batch))

  let clusters_for_batch batches batchname =
    let ret = match Shell.sh_lines "find -L %s -name %s" batches batchname with
      | [single] ->
        parse_batch single
      | _ ->
        Error (Error.of_string
                 (Printf.sprintf "Not a single batchfile for %s in %s" batchname batches))
    in
    match ret with
    | Ok clusters -> clusters
    | Error err -> failwith (Error.to_string_hum err)

  let collect_overviews progmap path =
    let lines = Shell.sh_lines "find -L %s -name overview | xargs cat | sort -u" path in
    Or_error.combine_errors (List.map ~f:(parse_overview_line progmap) lines)

  let collect_cluster_completed_info resultspath progmap batches =
    let results = Shell.sh_lines
        "find -L %s -type f -name result.log -printf '%%h\\n' | xargs -L1 basename"
        resultspath
    in
    List.fold_left results ~init:(Map.empty ~comparator:Cluster.comparator)
      ~f:(fun acc resultdir ->
          let dirpath = Printf.sprintf "%s/%s" resultspath resultdir in
          let result_log_path = Printf.sprintf "%s/result.log" dirpath in
          let ok =
            match In_channel.with_file result_log_path
                    ~f:In_channel.input_lines with
            | [line] when String.equal line "success!" -> true
            | _ -> false
          in
          List.fold_left (clusters_for_batch batches resultdir) ~init:acc
            ~f:(fun acc cl ->
                let ok = match ok with
                | false ->
                  false
                | true ->
                  (* The kamino run finished. We still need to look if there's a
                   * relevant overview; it could be that one of the functions
                   * was Confusing.
                   * XXX: We're assuming that, if neither function was Confusing, we got
                   * /some/ match as we're only comparing functions known to be
                   * equivalent.
                  *)
                  let overviews = collect_overviews progmap dirpath in
                  match overviews with
                  | Ok overviews ->
                    List.exists overviews
                      ~f:(fun o -> Cluster.compare cl o.cluster = 0)
                  | _ ->
                    false
                in
                Map.add acc cl ok
              ))

  let collect_clusters_from_batches dir =
    let paths = Shell.sh_lines "find -L %s -name '*.batch'" dir in
    Or_error.combine_errors (List.map ~f:parse_batch paths)

  let create_cluster_table_from_overviews l =
    List.fold_left
      ~f:(fun acc overview -> begin
            (* Only consider the best match *)
            let key = Cluster.to_key overview.cluster in
            match String.Table.find acc key with
            | Some overview' ->
              if cmp_result overview.result overview'.result > 0 then
                String.Table.replace acc ~key ~data:overview
            | None ->
              String.Table.set acc ~key ~data:overview
          end;
          acc)
      ~init:(String.Table.create ~size:(List.length l) ()) l

  let build_result_tables clusters progmap overviews =
    let cluster_table =
      begin
        match (String.Table.of_alist
                 (List.map ~f:(fun cl ->
                      (Cluster.to_key cl, cl)) clusters)) with
        | `Ok ct ->
          ct
        | `Duplicate_key s ->
          failwith (Printf.sprintf "dupkey: %s" s)
      end
    in
    let cluster_with_result_table = create_cluster_table_from_overviews overviews in
    let clusters = String.Set.of_list (String.Table.keys cluster_table) in
    let clusters_with_results = String.Set.of_list
        (String.Table.keys cluster_with_result_table) in
    let failed_clusters = String.Set.diff clusters
        clusters_with_results in
    let failed_overviews = String.Set.fold_right ~init:[]
        ~f:(fun cluster acc ->
            {result=None;
             cluster=String.Table.find_exn cluster_table cluster;
             validated=`Unvalidated; flags=[]} :: acc
          ) failed_clusters in
    let updated_overviews = List.fold_left ~init:[]
        ~f:(fun acc overview ->
            let key = Cluster.to_key overview.cluster in
            let cluster_from_batch = String.Table.find_exn
                cluster_table key in
            {overview with cluster = cluster_from_batch} :: acc
          ) overviews in
    (updated_overviews, failed_overviews)

  let collect_overviews_from_path clusters progmap resultspath =
    match collect_overviews progmap resultspath with
    | Ok overviews -> build_result_tables clusters progmap overviews
    | Error err -> failwith (Core.Error.to_string_hum err)

  let collect_results_from_path resultspath batchesloc =
    match batchesloc with
    | Path batchespath ->
      begin
        match collect_clusters_from_batches batchespath with
        | Error err ->
          failwith (Core.Error.to_string_hum err)
        | Ok clusters ->
          let clusters = List.concat clusters in
          let progmap = progmap_of_clusters Cluster.paths clusters in
          collect_overviews_from_path clusters progmap resultspath
      end
    | Commit _ ->
      failwith "Referencing a commit is not implemented!"

  (*
   * Given the location of a directory which contains the .batch files for a
   * run and the location of an output directory (which contains the generated
   * result overview files (conveniently named "overview")
   * 1. Collect all clusters (clusters are 1:1 to pairs of functions) that the
   *    run is supposed to compare
   * 2. Build a progmap which maps a binary basename to the full path
   * 3. Collect the produced results from the overview files
   *)
  let collect_results runloc batchesloc () =
    match runloc with
    | Path p -> collect_results_from_path p batchesloc
    | Commit c -> failwith "Referencing a commit is not implemented!"

  let parse_identicals path =
    let lines = In_channel.with_file path ~f:In_channel.input_lines in
    let re = Str.regexp "\\([^:]+\\): \\(.*\\)" in
    List.fold_left lines ~init:(Map.empty ~comparator:Cluster.comparator)
      ~f:(fun acc line ->
          if Str.string_match re line 0 then begin
            let cluster = Str.matched_group 1 line in
            let identical = Str.matched_group 2 line in
            let identical = String.equal identical "identical" in
            match Cluster.of_key cluster with
            | Error err ->
              let s = Printf.sprintf "Couldn't parse cluster '%s': %s"
                  cluster (Error.to_string_hum err) in
              failwith s
            | Ok cluster ->
              Map.add acc cluster identical
          end else begin
            failwith (Printf.sprintf "Invalid identicals line: %s" line)
          end)

  let is_isomorphic_vanilla o = List.mem o.flags FIsomorphicVanilla
  let is_isomorphic o = List.mem o.flags FIsomorphicFinal
  let is_exact o = match o.result with
    | Some {fuzziness = ExactOnly; overlap = OverlapTotal _} -> true | _ -> false

  let subjects_of_clusters clusters =
    let subjects = Set.empty ~comparator:Cluster.Subject.comparator in
    List.fold_left clusters ~init:subjects ~f:(fun subjects cl ->
        let left = Cluster.left cl in
        let right = Cluster.right cl in
        Set.add (Set.add subjects left) right)

  let to_map map ~f set =
    Set.fold set ~init:map ~f:(fun map el ->
        Map.add_multi map ~key:(f el) ~data:el)

  let clusters_by_compiler_version_pair clusters =
    let map = Map.empty ~comparator:String.comparator in
    let ccv = Cluster.Subject.version in
    to_map map clusters ~f:(fun cl ->
        match List.dedup ~compare:String.compare (Cluster.compilers cl) with
        | [cc] ->
          Printf.sprintf "%s-%s vs %s-%s"
            cc (ccv (Cluster.left cl))
            cc (ccv (Cluster.right cl))
        | _ ->
          failwith "cluster with different compilers!")

  let print_maps ~sub ~full ~f =
    Map.iter full ~f:(fun ~key ~data ->
        match Map.find sub key with
        | None ->
          let s = Printf.sprintf "Couldn't find key in sub map" in
          failwith s
        | Some sub ->
          f ~key ~sub ~full:data)

  let print_maps2 full maps f =
    Map.iter full ~f:(fun ~key ~data ->
        let els = List.fold_left maps ~init:[] ~f:(fun acc map ->
            match Map.find map key with
            | Some x -> x :: acc
            | None -> acc)
        in
        f key data (List.rev els))

  let ccmaj version =
    String.concat ~sep:"." (List.take (String.split ~on:'.' version) 2)

  let subjects_of_clusters_by_compiler_version clusters =
    let add_subj map subj =
      Map.add_multi map
        ~key:((Cluster.Subject.compiler subj) ^ "-" ^ (ccmaj (Cluster.Subject.version subj)))
        ~data:(Cluster.Subject.to_key subj)
    in
    let map = Map.empty ~comparator:String.comparator in
    List.fold_left clusters ~init:map ~f:(fun map cl ->
        let map = add_subj map (Cluster.left cl) in
        add_subj map (Cluster.right cl))

  let compilers_of_clusters clusters =
    let compilers = Set.empty ~comparator:String.comparator in
    List.fold_left clusters ~init:compilers ~f:(fun compilers cl ->
        let ccs = Cluster.compilers cl in
        Set.union compilers
          (Set.of_list ~comparator:String.comparator ccs))

  let matched_subjects_of_overviews overviews =
    let matched_clusters = List.filter_map overviews ~f:(fun o ->
        match is_exact o with
        | false -> None
        | true -> Some o.cluster) in
    subjects_of_clusters matched_clusters

  let doit identicalspath resultspath batchespath =
    let clusters_identical = parse_identicals identicalspath in
    let clusters = match collect_clusters_from_batches batchespath with
      | Error err -> failwith (Error.to_string_hum err)
      | Ok clusters -> List.concat clusters
    in
    let progmap = progmap_of_clusters Cluster.paths clusters in
    let overviews = match collect_overviews progmap resultspath with
      | Error err -> failwith (Error.to_string_hum err)
      | Ok overviews -> overviews
    in
    let overviews = List.fold_left ~init:(Map.empty ~comparator:Cluster.comparator)
        ~f:(fun acc o ->
            Map.add acc o.cluster o) overviews
    in
    let clusters_completed = collect_cluster_completed_info resultspath progmap batchespath in
    let clusters_completed_set = Map.fold
        ~init:(Set.empty ~comparator:Cluster.comparator)
        ~f:(fun ~key ~data acc ->
            match data with
            | true -> Set.add acc key
            | false -> acc
          ) clusters_completed
    in

    List.iter clusters ~f:(fun cl ->
        let overview = Map.find overviews cl in
        let identical =
          match Map.find clusters_identical cl with
          | None ->
            let s = Printf.sprintf "No trivial-equiv info for %s" (Cluster.to_key cl) in
            failwith s
          | Some (tf) ->
            if tf then "TrivEq" else "NotTrivEq"
        in
        let did_complete = match Map.find clusters_completed cl with
          | Some true -> "Completed"
          | Some false | None -> "DidNotComplete"
        in
        let isomorphized, exact, cmpres = match overview with
          | Some o ->
            begin
              let iso = match is_isomorphic o with
                | true -> "IsomorphicFinal"
                | false -> "NonIsomorphicFinal"
              in
              let exact = match is_exact o with
                | true -> "Exact"
                | false -> "NotExact"
              in
              let cmpres = match o.result with
                | Some res -> Cmpres.cfgcmp_res_to_string res
                | None -> "-"
              in
              (iso, exact, cmpres)
            end
          | None ->
            ("-", "-", "-")
        in
        Printf.printf "%s\t%s\t%s\t%s\t%s\t%s\n" (Cluster.to_key cl) identical did_complete
          isomorphized exact cmpres
      );


    let cluster_set = Set.of_list ~comparator:Cluster.comparator clusters in

    let total_clusters = List.length clusters in
    let nidentical = Map.fold clusters_identical ~init:0
        ~f:(fun ~key ~data acc ->
            match data with
            | true -> acc + 1
            | false -> acc
          )
    in

    let clusters_identical, clusters_non_identical =
      Set.partition_tf cluster_set
        ~f:(fun cl ->
            match Map.find clusters_identical cl with
            | None -> failwith "unknown cluster"
            | Some identical -> identical)
    in
    let nnon_identical = total_clusters - nidentical in
    assert((Set.length clusters_non_identical) = nnon_identical);

    Printf.printf "Got %d clusters, %d overviews\n"
      (total_clusters) (Map.length overviews);


    Printf.printf "%d/%d (%.2f%%) clusters were identical\n"
      nidentical total_clusters
      (100. *. (Float.of_int nidentical) /. (Float.of_int total_clusters));


    let clusters_completed_nonidentical =
      Set.inter clusters_non_identical clusters_completed_set in
    let ncompleted = Set.length clusters_completed_nonidentical in

    Printf.printf "%d/%d (%.2f%%) of the non-identical ones completed\n"
      ncompleted nnon_identical
      (100. *. (Float.of_int ncompleted) /. (Float.of_int nnon_identical));

    let clusters_isomorphic_vanilla =
      Set.filter clusters_completed_nonidentical
        ~f:(fun  k ->
            match Map.find overviews k with
            | Some o when is_isomorphic_vanilla o -> true
            | _ -> false)
    in
    let nisomorphic_vanilla = Set.length clusters_isomorphic_vanilla in
    Printf.printf "%d/%d (%.2f%%) of the completed non-identical ones were isomorphicV\n"
      nisomorphic_vanilla ncompleted
      (100. *. (Float.of_int nisomorphic_vanilla) /. (Float.of_int ncompleted));

    let clusters_isomorphic_final =
      Set.filter clusters_completed_nonidentical
        ~f:(fun  k ->
            match Map.find overviews k with
            | Some o when is_isomorphic o -> true
            | _ -> false)
    in
    let nisomorphic_final = Set.length clusters_isomorphic_final in
    Printf.printf "%d/%d (%.2f%%) of the completed non-identical ones were isomorphicF\n"
      nisomorphic_final ncompleted
      (100. *. (Float.of_int nisomorphic_final) /. (Float.of_int ncompleted));

    let clusters_exact = Set.filter clusters_isomorphic_final
        ~f:(fun  cl ->
            match Map.find overviews cl with
            | Some o when is_exact o -> true
            | _ -> false)
    in
    let nexact = Set.length clusters_exact in
    Printf.printf "%d/%d (%.2f%%) of the isomorphicF ones were EXACT\n"
      nexact nisomorphic_final
      (100. *. (Float.of_int nexact) /. (Float.of_int nisomorphic_final));

    let exact_by_ccv_pair = clusters_by_compiler_version_pair clusters_exact in
    let isomorphic_vanilla_by_ccv_pair = clusters_by_compiler_version_pair clusters_isomorphic_vanilla in
    let isomorphic_final_by_ccv_pair = clusters_by_compiler_version_pair clusters_isomorphic_final in
    let identical_by_ccv_pair = clusters_by_compiler_version_pair clusters_identical in
    let clusters_by_ccv_pair = clusters_by_compiler_version_pair cluster_set in

    Printf.printf "Compared clusters\nTotal\tTrivial\tIsoV\tIsoF\tExact\n";
    let maps_by_ccv = [
      identical_by_ccv_pair;
      isomorphic_vanilla_by_ccv_pair;
      isomorphic_final_by_ccv_pair;
      exact_by_ccv_pair;
    ] in
    print_maps2 clusters_by_ccv_pair
      maps_by_ccv (fun key all_clusters_of_pair elems ->
          let elems = Misc.list_pad (List.length maps_by_ccv) [] elems in
          let n = List.length all_clusters_of_pair in
          let nums = List.map elems ~f:(fun l ->
              Printf.sprintf "%d" (List.length l)) in
          Printf.printf "\"%s\"\t%d\t%s\n" key n (String.concat ~sep:"\t" nums));

    (* Subject stats. Only meaningful for unique pairs *)

(*    let clusters_identical = Map.fold clusters_identical ~init:[]
        ~f:(fun ~key ~data acc ->
            match data with
            | false -> acc
            | true -> (key :: acc))
    in
*)
    let subjects = subjects_of_clusters clusters in
    let kamino_matched_subjects = matched_subjects_of_overviews (Map.data overviews) in

    (* Both of the subjects of a cluster that was declared trivially
     * equivalent (a.k.a. identical) /have/ a match. In other words,
     * they are each other's match.
    *)
    let identical_matched_subjects = subjects_of_clusters (Set.to_list clusters_identical) in
    let nonidentical_subjects = Set.diff subjects identical_matched_subjects in

    let nsubjects = Set.length subjects in
    (* Only matched by kamino *)
    let nonly_kamino_matched_subjects =
      Set.length (Set.diff kamino_matched_subjects identical_matched_subjects)
    in
    let nidentical_matched_subjects = Set.length identical_matched_subjects in

    let matched_subjects = Set.union kamino_matched_subjects identical_matched_subjects in

    let subjects_by_compiler_version = subjects_of_clusters_by_compiler_version clusters in
    let matched_subjects_by_compiler_version =
      to_map (Map.empty ~comparator:String.comparator) matched_subjects
        ~f:(fun s -> (Cluster.Subject.compiler s) ^ "-" ^ (ccmaj (Cluster.Subject.version s)))
    in
    Printf.printf "Subjects:\nccv\tmatched\ttotal\n";
    print_maps ~f:(fun ~key ~sub ~full ->
        let count ~comparator subjs = Set.length
            (Set.of_list ~comparator subjs) in
        Printf.printf "%s\t%d\t%d\n" key
          (count ~comparator:Cluster.Subject.comparator sub)
          (count ~comparator:String.comparator full)
      ) ~sub:matched_subjects_by_compiler_version ~full:subjects_by_compiler_version;

    let nmatched_subjects = Set.length matched_subjects in
    let nnonidentical_subjects = Set.length nonidentical_subjects in

    Printf.printf "%d/%d subjects (%.2f%%) matched at least once\n"
      nmatched_subjects nsubjects
      (100. *. (Float.of_int nmatched_subjects) /. (Float.of_int nsubjects));

    Printf.printf "%d/%d (%.2f%%) were matched by trivial equivalence alone\n"
      nidentical_matched_subjects nsubjects
      (100. *. (Float.of_int nidentical_matched_subjects) /. (Float.of_int nsubjects));

    Printf.printf "%d/%d (%.2f%%) not trivially equivalent ones were matched by kamino\n"
      nonly_kamino_matched_subjects nnonidentical_subjects
      (100. *. (Float.of_int nonly_kamino_matched_subjects) /. (Float.of_int nnonidentical_subjects))
end

let create_table_of_list ~f l = List.fold_left
  ~init:(String.Table.create ~size:(List.length l) ())
  ~f:(fun table overview ->
    String.Table.add_multi table ~key:(f overview)
      ~data:overview; table) l

let empty_list () = []

let to_percentage nom denom =
  let open Float in
  ((of_int nom) * 100.0) / (of_int denom)

module Diff(Subject : ClusterSubject) =
struct
  module Cluster = BaseCluster(Subject)
  module Base = Base(Cluster)
  open Base
  type diffstats = {
    better : int ref;
    worse : int ref;
    same : int ref;
    appeared : int ref;
    disappeared : int ref;
  }

  let diffstats_to_str {better; worse; same; appeared; disappeared} =
    Printf.sprintf
      "%d improved(<), %d worsened(>), %d new(+), %d disappeared(-), %d unchanged(=)"
      !better !worse !appeared !disappeared !same

  let do_diff output_same produce_stats lhs rhs () =
    let open Result in
    let diffstats = {
      better = ref 0; worse = ref 0; same = ref 0; appeared = ref 0; disappeared = ref 0;
    } in
    let open Base in
    match lhs, rhs with
    | Path p, Path p' -> begin
        let progmap _ = failwith "This progmap not implemented" in
        match (collect_overviews progmap p) >>= (fun lhs ->
            (collect_overviews progmap p') >>= (fun rhs ->
                Ok (lhs, rhs))) with
        | Ok (lhs, rhs) ->
          let table = create_cluster_table_from_overviews lhs in
          let table' = create_cluster_table_from_overviews rhs in
          let keys = String.Set.of_list (String.Table.keys table) in
          let keys' = String.Set.of_list (String.Table.keys table') in
          String.Set.iter2 keys keys' ~f:(function
              | `Both (lhs, rhs) -> begin
                  let overview  = String.Table.find_exn table lhs in
                  let overview' = String.Table.find_exn table' rhs in
                  let cmp = cmp_result overview.result overview'.result in
                  if cmp = 0 then begin
                    if output_same then begin
                      Printf.printf "= %s %s\n" (result_to_string overview.result)
                        (Cluster.to_string overview.cluster)
                    end;
                    diffstats.same := !(diffstats.same) + 1
                  end else if cmp < 0 then begin
                    Printf.printf "> %s -> %s %s\n"
                      (result_to_string overview.result) (result_to_string overview'.result)
                      (Cluster.to_string overview.cluster);
                    diffstats.worse := !(diffstats.worse) + 1
                  end else begin
                    assert (cmp > 0);
                    Printf.printf "< %s -> %s %s\n"
                      (result_to_string overview.result) (result_to_string overview'.result)
                      (Cluster.to_string overview.cluster);
                    diffstats.better := !(diffstats.better) + 1
                  end
                end
              | `Left lhs ->
                let overview = String.Table.find_exn table lhs in
                Printf.printf "- %s %s\n" (result_to_string overview.result)
                  (Cluster.to_string overview.cluster);
                diffstats.disappeared := !(diffstats.disappeared) + 1
              | `Right rhs ->
                let overview = String.Table.find_exn table' rhs in
                Printf.printf "+ %s %s\n" (result_to_string overview.result)
                  (Cluster.to_string overview.cluster);
                diffstats.appeared := !(diffstats.appeared) + 1
            );
          if produce_stats then begin
            Printf.printf "%s\n" (diffstats_to_str diffstats)
          end
        | Error err -> failwith (Core.Error.to_string_hum err)
      end
    | _ -> failwith "Unimplemented diff combination!"
end

module PrimitivesStats =
struct
  module Cluster = BaseCluster(PrimitivesSubject)
  module Base = Base(Cluster)
  type overview = Base.overview
  type overview_lists = {
    exact : (overview list) String.Table.t;
    incomplete : (overview list) String.Table.t;
    failed : (overview list) String.Table.t;
    rest : (overview list) String.Table.t;
  }

  let print_stats all_overviews =
    let open Base in
    let is_exact o = match o.result with
      | Some {fuzziness = ExactOnly; overlap = OverlapTotal _} -> true | _ -> false in
    let is_incomplete o = match o.result with
      | Some {fuzziness = ExactOnly; overlap = OverlapTotal _} -> false
      | Some {fuzziness = ExactOnly;} -> true
      | _ -> false
    in
    let is_incomplete_missing_n n o = match o.result with
      | Some {fuzziness = ExactOnly; overlap = OverlapPartial (k,m)}
           when (m-k) = n -> true
      | _ -> false in
    let is_fail o = o.result = None in

    let tabulate_overviews ~f overviews =
      let exact_ovs, overviews = List.partition_tf ~f:is_exact overviews in
      let exact = create_table_of_list ~f exact_ovs in

      let incomplete_ovs, overviews = List.partition_tf ~f:is_incomplete overviews in
      let incomplete = create_table_of_list ~f incomplete_ovs in

      let failed_ovs, overviews = List.partition_tf ~f:is_fail overviews in
      let failed = create_table_of_list ~f failed_ovs in
      {
        exact;
        incomplete;
        failed;
        rest = create_table_of_list ~f overviews;
      }
    in
    let table_get_overview key table =
      String.Table.find_or_add table key ~default:empty_list
    in
    let overview_not_identical o = not (List.mem o.flags FIdenticalFunctions) in
    let print_summary overviews =
      let exact_ovs, overviews = List.partition_tf ~f:is_exact overviews in
      let exacts = List.length exact_ovs in
      let nonidentical_exacts = List.count ~f:overview_not_identical exact_ovs in
      let incomplete_ovs, overviews =
        List.partition_tf ~f:is_incomplete overviews in
      let incompletes = List.length incomplete_ovs in
      let incompletes_missing_n n = (List.filter ~f:(is_incomplete_missing_n n) incomplete_ovs) in
      let incompletes_missing1 = List.length (incompletes_missing_n 1) in
      let incompletes_missing2 = List.length (incompletes_missing_n 2) in
      let failed_ovs, rest_ovs = List.partition_tf ~f:is_fail overviews in
      let fails = List.length failed_ovs in
      let rest = List.length rest_ovs in
      let total = exacts + incompletes + fails + rest in
      let exact_percentage = to_percentage exacts total in
      let nonidentical = to_percentage nonidentical_exacts exacts in
      Printf.printf
        "EXACT: %.2f%% (%d/%d)[%.2f%% non-identical] INCOMPLETE: (%d/%d) \
         INCOMPLETES-1: (%d/%d) INCOMPLETES-2: (%d/%d) REST: (%d/%d) FAILS (%d/%d)\n"
        exact_percentage exacts total nonidentical incompletes total
        incompletes_missing1 total incompletes_missing2 total
        rest total fails total
    in
    let print_per_symbol overviews =
      let to_symbol o = Cluster.symbol o.cluster in
      let symbols = List.map ~f:to_symbol overviews in
      let symbols = String.Set.of_list symbols in
      let overview_table = tabulate_overviews ~f:to_symbol overviews in
      let grand_sum = List.fold ~f:(fun sum symbol ->
          let tgo = table_get_overview symbol in
          let exacts = List.length (tgo overview_table.exact) in
          let nonidentical_exacts = List.count ~f:overview_not_identical (tgo overview_table.exact) in
          let incompletes = List.length (tgo overview_table.incomplete) in
          let fails = List.length (tgo overview_table.failed) in
          let rest = List.length (tgo overview_table.rest) in
          let total = exacts + incompletes + fails + rest in
          let exact_percentage = to_percentage exacts total in
          let nonidentical = to_percentage nonidentical_exacts exacts in
          Printf.printf
            "%s EXACT: %.2f%% (%d/%d) [%.2f%% non-identical] INCOMPLETES: (%d/%d) REST: (%d/%d) FAILS (%d/%d)\n"
            symbol exact_percentage exacts total nonidentical incompletes total rest total fails total;
          sum + total
        ) ~init:0 (String.Set.elements symbols)
      in
      assert (grand_sum = List.length overviews)
    in

    let compute_key (cc, ver) (cc', ver') =
      Printf.sprintf "%s-%s-%s-%s" cc ver cc' ver'
    in
    let get_comp_ver o =
      match Cluster.compilers o.cluster with
      | [compiler1; compiler2] ->
        let ver1, ver2 = Cluster.versions o.cluster in
        ((compiler1, ver1), (compiler2, ver2))
      | _ ->
        failwith "inappropriate number of compilers"
    in
    let compute_key_from_overview o =
      let ccver1, ccver2 = get_comp_ver o in
      compute_key ccver1 ccver2
    in
    let get_ccvers o =
      let ccver1, ccver2 = get_comp_ver o in
      [ccver1; ccver2]
    in

    let do_per_adjacent_compiler ~iter overviews =
      let compilers = List.concat (List.map ~f:get_ccvers overviews) in
      let compilers = Set.Poly.elements (Set.Poly.of_list compilers) in
      let compilers = List.group ~break:(fun (cc, _) (cc',_) ->
          not (String.equal cc cc'))
          (List.sort ~cmp:(fun (cc, ver) (cc', ver') ->
               let res = compare cc cc' in
               if res = 0 then compare ver ver'
               else res
             ) compilers)
      in
      let overview_table = tabulate_overviews ~f:compute_key_from_overview
          overviews
      in
      List.iter ~f:(fun versions ->
          ignore(List.reduce ~f:(fun lhs rhs ->
              iter overview_table lhs rhs;
              rhs
            ) versions)
        ) compilers
    in

    let print_per_adjacent_compiler overviews =
      let iter overview_table (cc, ver) (cc', ver') =
        let key = compute_key (cc, ver) (cc', ver') in
        let tgo = table_get_overview key in
        let exacts = List.length (tgo overview_table.exact) in
        let nonidentical_exacts = List.count ~f:overview_not_identical (tgo overview_table.exact) in
        let incompletes = List.length (tgo overview_table.incomplete) in
        let fails = List.length (tgo overview_table.failed) in
        let rest = List.length (tgo overview_table.rest) in
        let total = exacts + incompletes + fails + rest in
        let exact_percentage = to_percentage exacts total in
        let nonidentical = to_percentage nonidentical_exacts exacts in
        Printf.printf "%s %s vs %s EXACT: %.2f%% (%d/%d) [%.2f%% non-identical] INCOMPLETES: (%d/%d) \
                       REST: (%d/%d) FAILS (%d/%d)\n"
          cc ver ver' exact_percentage exacts total nonidentical incompletes total
          rest total fails total
      in
      do_per_adjacent_compiler ~iter overviews
    in
    let print_per_adjacent_compiler_per_symbol overviews =
      let iter overview_table lhs rhs =
        let key = compute_key lhs rhs in
        Printf.printf "+ %s\n" key;
        let tgo = table_get_overview key in
        let overviews = (tgo overview_table.exact)
                        @ (tgo overview_table.incomplete)
                        @ (tgo overview_table.failed)
        in
        print_per_symbol overviews
      in
      do_per_adjacent_compiler ~iter overviews
    in
    let print_self overviews =
      let is_self {cluster} = Cluster.is_self cluster in
      let overviews = List.filter ~f:is_self overviews in
      print_per_symbol overviews
    in
    let is_isomorphic o = List.mem o.flags FIsomorphicFinal in
    let is_not_failed o = o.result <> None in
    let print_summary_with_headers descr overviews =
      Printf.printf "=====================================%s=====================================\n"
        descr;
      Printf.printf "-----------------------------------SUMMARY-----------------------------------\n";
      print_summary overviews;
      Printf.printf "---------------------------------PER SYMBOL----------------------------------\n";
      print_per_symbol overviews;
      Printf.printf "-------------------------------PER ADJACENT CC-------------------------------\n";
      print_per_adjacent_compiler overviews;
      Printf.printf "-------------------------PER ADJACENT CC PER SYMBOL--------------------------\n";
      print_per_adjacent_compiler_per_symbol overviews
    in

    print_summary_with_headers "ALL" all_overviews;

    let not_failed_overviews = List.filter ~f:is_not_failed all_overviews in
    print_summary_with_headers "WITHOUT FAILED" not_failed_overviews;

    let isomorphic_overviews = List.filter ~f:is_isomorphic all_overviews in
    print_summary_with_headers "ISOMORPHIC" isomorphic_overviews;

    Printf.printf "====================================SELFIE===================================\n";
    print_self isomorphic_overviews

end

module StatsFuzzyInlines =
struct
  module Cluster = BaseCluster(FuzzyInlinesSubject)
  module Base = Base(Cluster)

  let print_groundtruth ~successful_overviews ~failed_overviews =
    let open Base in
    let exists p = Sys.is_file p = `Yes in
    let inline_info_tbl = String.Table.create () in
    let lookup p = String.Table.find_exn inline_info_tbl p in
    let with_inline_info = List.filter ~f:(fun overview ->
        let p1, p2 = Cluster.paths overview.cluster in
        (* Only consider the case where the inline site and callee are
           part of the same binary *)
        if String.compare p1 p2 = 0 then begin
          if exists p1 then begin
            let inlinespath = Printf.sprintf "%s.inlines" p1 in
            if not (String.Table.mem inline_info_tbl p1) then
              String.Table.add_exn ~key:p1
                ~data:(Batchspec.binary_inline_info_from_file inlinespath)
                inline_info_tbl;
            true
          end else begin
            false
          end
        end else begin
          false
        end
      ) successful_overviews
    in
    (*
     * We've identified a caller, callee pair. Check if the compiler
     * says it actually was an inline site.
     *)
    let inline_instance_by_addr instances addr addr' =
      let is_match instance =
        let open Batchspec in
        let caller_is_match = List.exists ~f:(fun (b, _) -> b = addr)
            instance.caller.range in
        let callee_is_match = List.exists ~f:(fun range ->
            List.exists ~f:(fun (b, _) -> b = addr') range) instance.callees.ranges in
        caller_is_match && callee_is_match
      in
      List.find ~f:is_match instances in

    let total_inlining_sites = List.fold_left ~init:0 ~f:(fun acc bininfo ->
        let inlines = bininfo.Batchspec.inlines in
        acc + (List.length inlines)) (String.Table.data inline_info_tbl)
    in
    let fp, tp = List.fold_left ~init:([], [])
        ~f:(fun (fp, tp) overview ->
            let path = match Cluster.paths overview.cluster with
              | p1, p2 when p1 = p2 -> p1
              | _ -> failwith "Unexpectedly different paths"
            in
            let inline_info = lookup path in
            (* Assume lhs is the caller and the rhs is the callee *)
            let caller, callee = Cluster.addresses overview.cluster in
            match inline_instance_by_addr inline_info.Batchspec.inlines caller callee
            with
            | Some _ -> (fp, overview :: tp)
            | _ -> (overview :: fp, tp)
          ) with_inline_info in
    let tp = List.length tp in
    let fp = List.length fp in
    let fn = total_inlining_sites - tp in
    let total = (List.length successful_overviews) + (List.length failed_overviews) in
    let tn = total - fp - tp - fn in
    let missing = (List.length successful_overviews) - (List.length with_inline_info) in
    if missing <> 0 then begin
      failwith (Printf.sprintf "There were %d clusters in binaries that we \
                                didn't have inline info for" missing)
    end;
    Printf.printf "TP:%i/%i (%f%%) FN:%i/%i (%f%%) FP:%i/%i  TN:%d/%d\n"
      tp total
      (100. *. (float tp) /. (float total_inlining_sites))
      fn total
      (100. *. (float fn) /. (float total_inlining_sites))
      fp total
      tn total
end

let print_batch_clusters batchpath =
  let module P = PrimitivesStats in
  match P.Base.parse_batch batchpath with
  | Error err ->
    failwith (Error.to_string_hum err)
  | Ok clusters ->
    let bn = FilePath.basename batchpath in
    List.iter clusters ~f:(fun cl ->
        Printf.printf "%s\t%s\n" (P.Cluster.to_key cl) bn)

let do_batch_clusters batchlist () =
  List.iter ~f:print_batch_clusters batchlist

let do_stats_primitives identicalspath run batches () =
  let run = match run with
    | Path p -> p
    | Commit _ -> failwith "Commit?"
  in
  let batches = match batches with
    | Path p -> p
    | Commit _ -> failwith "Commit?"
  in
  PrimitivesStats.Base.doit identicalspath run batches

let do_old_stats_primitives run batches () =
  let overviews_with_results, overviews_without_results =
    PrimitivesStats.Base.collect_results run batches ()
  in
  PrimitivesStats.print_stats (overviews_with_results @ overviews_without_results)

let do_stats_fuzzy_inlines run batches () =
  let successful_overviews, failed_overviews =
    StatsFuzzyInlines.Base.collect_results run batches ()
  in
  StatsFuzzyInlines.print_groundtruth ~successful_overviews ~failed_overviews

let dir_or_commit =
  Command.Spec.Arg_type.create
    (fun dir_or_commit ->
      match Sys.is_directory ~follow_symlinks:true dir_or_commit with
      | `Yes -> Path dir_or_commit
      | `No | `Unknown ->
         let regexp = Str.regexp "^[0-9a-fA-F]+$" in
         if Str.string_match regexp dir_or_commit 0 then
           Commit dir_or_commit
         else begin
           eprintf "'%s' is neither an existing dir nor a git commit id.\n%!"
             dir_or_commit;
           exit 1
         end
    )

let diff_command =
  let module Diff = Diff(FuzzyInlinesSubject) in
  Command.basic
    ~summary:"diff results of two runs"
    Command.Spec.(
      empty
      +> flag "-u" no_arg ~doc:" also output clusters with no changes"
      +> flag "-s" no_arg ~doc:" produce diff stats"
      +> anon ("run" %: dir_or_commit)
      +> anon ("run" %: dir_or_commit)
    )
    (Diff.do_diff)

let batch_clusters_command =
  Command.basic
    ~summary:"Print out the clusters of batches"
    Command.Spec.(
      empty
      +> anon (sequence ("batch" %: file))
    )
    do_batch_clusters

let stats_primitives_command =
  Command.basic
    ~summary:"show stats of a run"
    Command.Spec.(
      empty
      +> flag "-e" (required string) ~doc:" Path of clusters and 'identicity' information"
      +> anon ("run" %: dir_or_commit)
      +> anon ("batches" %:dir_or_commit)
    )
    do_stats_primitives

let old_stats_primitives_command =
  Command.basic
    ~summary:"show stats of a run"
    Command.Spec.(
      empty
      +> anon ("run" %: dir_or_commit)
      +> anon ("batches" %:dir_or_commit)
    )
    do_old_stats_primitives

let stats_fuzzy_inlines_command =
  Command.basic
    ~summary:"show stats of a run"
    Command.Spec.(
      empty
      +> anon ("run" %: dir_or_commit)
      +> anon ("batches" %:dir_or_commit)
    )
    do_stats_fuzzy_inlines

let suite =
  Command.group ~summary:"The evaluator's swiss-knife"
    [
      ("diff", diff_command);
      ("batch-clusters", batch_clusters_command);
      ("stats-primitives", stats_primitives_command);
      ("stats-fuzzy-inlines", stats_fuzzy_inlines_command);
      ("batch", Eval_batch.command);
    ]

let () =
  Command.run ~version:"0.1" suite
