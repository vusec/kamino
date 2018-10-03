open Core.Std
open Core_extended

type grouping =
  | GroupByMajor
  | GroupByMinor
  | GroupAll

type pair_mode =
  | AdjacentPairs
  | UniquePairs

type compiler_version = {
  major : (int * int);
  minor : int;
} with sexp

let opt_outdir = ref "eval/batches"

type compiler = {
  ccname : string;
  versions : compiler_version list
}

type primitive = {
  primname : string;
  implementations : string list;
}

type comparison_item = {
  implementation : string;
  primitive : string;
  compilername : string;
  version : compiler_version;
  olvl : string;
  binarypath : string;
} with sexp

type comparison_pair = {
  left : comparison_item;
  right : comparison_item;
} with sexp

module Manifest =
struct
  type t = comparison_pair list

  let empty = []
  let add t it = it :: t
  let sexp_of_t t =
    Sexp.List [Sexp.Atom "manifest";
               Sexp.List (List.map ~f:sexp_of_comparison_pair t)]
end

let ccv2s {major; minor;} =
  let m1, m2 = major in
  Printf.sprintf "%d.%d.%d" m1 m2 minor

let unexpected_type ~descr ~t json =
  let s = Printf.sprintf "%s should be a %s but got %s"
      descr t (Yojson.Safe.to_string json) in
  Or_error.error_string s

let parse_compiler_version map =
  let f = Map.find map in
  match (f "major", f "minor", f "patch") with
  | Some (`Int maj), Some (`Int min), Some (`Int patch) ->
    Some {
      major = (maj, min);
      minor = patch;
      }
  | Some (`String maj), Some (`String min), Some (`String patch) ->
     Some {
         major = (Int.of_string maj, Int.of_string min);
         minor = Int.of_string patch;
       }
  | _ ->
    None

let parse_compiler_version_json name json =
  match json with
  | `Assoc alist ->
    begin
      match Map.of_alist String.comparator alist with
      | `Duplicate_key key ->
        let s = Printf.sprintf "Duplicate key %s in compiler version %s"
            key (Yojson.Safe.to_string json) in
        Or_error.error_string s
      | `Ok map ->
        begin
          match parse_compiler_version map with
          | None ->
            let s = Printf.sprintf "Could not parse version %s for compiler %s"
                (Yojson.Safe.to_string json) name in
            Or_error.error_string s
          | Some v ->
            Result.Ok v
        end
    end
  | _ ->
    unexpected_type ~descr:"Version" ~t:"hash" json

let parse_compiler_versions ccname json =
  match json with
  | `List jsons ->
    let versions = List.map ~f:(parse_compiler_version_json ccname) jsons in
    let versions = Or_error.combine_errors versions in
    Result.bind versions (fun versions ->
        Result.Ok {
          ccname;
          versions;
        })
  | _ ->
    unexpected_type ~descr:"Versions" ~t:"array" json

let parse_compiler map =
  match Map.find map "name" with
  | None ->
    Or_error.error_string "Compiler without a name"
  | Some (`String name) ->
    begin
      match Map.find map "versions" with
      | None ->
        let s = Printf.sprintf "No versions for compiler %s" name in
        Or_error.error_string s
      | Some versions ->
        parse_compiler_versions name versions
    end
  | Some json ->
    unexpected_type ~descr:"Compiler name" ~t:"string" json

let parse_compiler_json configpath json =
  match json with
  | `Assoc alist ->
    begin
      match Map.of_alist String.comparator alist with
      | `Duplicate_key key ->
        let s = Printf.sprintf "Duplicate key %s in compiler version %s"
            key (Yojson.Safe.to_string json) in
        Or_error.error_string s
      | `Ok map ->
        parse_compiler map
    end
  | _ ->
    unexpected_type ~descr:"Compiler" ~t:"hash" json

let parse_compilers configpath map =
  match Map.find map "compilers" with
  | None ->
    let s = Printf.sprintf "No compilers specified in %s" configpath in
    Or_error.error_string s
  | Some (`List compilers) ->
    Or_error.combine_errors (List.map ~f:(parse_compiler_json configpath) compilers)
  | Some json ->
    unexpected_type ~descr:"Compilers" ~t:"list" json

let parse_implementation json =
  match json with
  | `String str ->
    Result.Ok str
  | _ ->
    let s = Printf.sprintf "Expected string but got %s" (Yojson.Safe.to_string json) in
    Or_error.error_string s

let parse_primitive map =
  match Map.find map "name" with
  | None ->
    Or_error.error_string "No name for primitive"
  | Some (`String name) ->
    begin
      match Map.find map "implementations" with
      | None ->
        Or_error.error_string (Printf.sprintf "No implementations for %s" name)
      | Some (`List implementations) ->
        begin
          let impls = List.map ~f:parse_implementation implementations in
          let impls = Or_error.combine_errors impls in
          Result.bind impls (fun implementations ->
            Result.Ok {primname = name; implementations})
        end
      | Some json ->
        unexpected_type ~descr:"Implementations" ~t:"array" json

    end
  | Some json ->
    unexpected_type ~descr:"Primitive name" ~t:"string" json

let parse_primitive_json json =
  match json with
  | `Assoc kvs ->
    begin
      match Map.of_alist String.comparator kvs with
      | `Duplicate_key key ->
        Or_error.error_string (Printf.sprintf "Duplicate key %s in hash: %s"
                                 key (Yojson.Safe.to_string json))
      | `Ok map ->
        parse_primitive map
    end
  | _ ->
    Or_error.error_string (Printf.sprintf "Primitive is not a hash: %s"
                             (Yojson.Safe.to_string json))

let parse_primitives map =
  match Map.find map "primitives" with
  | None ->
    Or_error.error_string "No primitives"
  | Some (`List primitives) ->
    Or_error.combine_errors (List.map ~f:parse_primitive_json primitives)
  | Some json ->
    unexpected_type ~descr:"Primitives" ~t:"array" json

let parse_config configpath =
  let json = Yojson.Safe.from_file configpath in
  match json with
  | `Assoc kvs ->
    begin
      match Map.of_alist String.comparator kvs with
      | `Duplicate_key key ->
        let s = Printf.sprintf "Duplicate key in %s: %s" configpath key in
        failwith s
      | `Ok map ->
        begin
          match (parse_compilers configpath map,
                 parse_primitives map) with
          | Result.Ok compilers, Result.Ok primitives ->
            Printf.printf "Config parsed successfully\n%!";
            (compilers, primitives)
          | Result.Error err, _
          | _, Result.Error err ->
            failwith (Error.to_string_hum err)
        end
    end
  | _ ->
    let s = Printf.sprintf "Expected hash as the toplevel object in %s" configpath in
    failwith s

let ccverfilt ccver cc =
  let re = Str.regexp ccver in
  let matches_re str = Str.string_match re str 0 in
  let filt ver = matches_re (ccv2s ver) in
  let versions = List.filter ~f:filt cc.versions in
  {cc with versions}

let ccfilt name compilers =
    List.filter ~f:(fun cc -> cc.ccname = name) compilers

(*
 * Filter the compilers (and corresponding versions) according
 * to the command line arguments.
 *)
let prune_compilers compilers cc ccver =
  match cc, ccver with
  | None, None ->
    compilers
  | None, Some _ ->
    Printf.eprintf "Cannot filter by compiler version w/o specifying the compiler\n%!";
    exit 2
  | Some cc, None ->
    ccfilt cc compilers
  | Some cc, Some ccver ->
    List.map ~f:(ccverfilt ccver) (ccfilt cc compilers)

(* Generate adjacent version pairs *)
let adjacent_pairs_of_versions versions =
  let (pairs, _) = List.fold_left ~f:(fun (acc, prev) curr ->
      match prev with
      | None ->
        (acc, Some curr)
      | Some prev ->
        ((prev, curr) :: acc), Some curr)
      ~init:([], None) versions in
  pairs

let unique_pairs_of_versions versions =
  Misc.list_unique_pairs versions

let gen_group_pairs pair_mode versions =
  match pair_mode with
  | AdjacentPairs -> adjacent_pairs_of_versions versions
  | UniquePairs -> unique_pairs_of_versions versions

(* Group compiler versions according to what the user requested *)
let group_versions grouping versions =
  let group_name version = match grouping with
    |  GroupByMajor ->
      let m1, m2 = version.major in
      Printf.sprintf "%d.%d" m1 m2
    | GroupByMinor ->
      failwith "Nonsensical?"
    | GroupAll -> "All"
  in
  let alist = List.map ~f:(fun vers -> (group_name vers, vers)) versions in
  Map.of_alist_multi String.comparator alist

let print_group_pairs ~key:group ~data:vpairs =
  Printf.printf "Group %s\n" group;
  List.iter ~f:(fun (v1, v2) ->
      Printf.printf "  %s vs %s\n" (ccv2s v1) (ccv2s v2)) vpairs

let do_impl ~binidx1 ~binidx2 ~binspec1 ~binspec2 run symbol =
  let open Batch.Run in
  let bp bspec = Input.BinaryPath.to_string bspec.Input.path in
  let addr1 = Sym_resolver.symbol_address (bp binspec1) symbol in
  let addr2 = Sym_resolver.symbol_address (bp binspec2) symbol in
  let lhs = {binary_idx = binidx1; name = symbol; addr = addr1} in
  let rhs = {binary_idx = binidx2; name = symbol; addr = addr2} in
  let inline_info = {parent = lhs; out_of_line_copy = rhs} in
  add_inline inline_info run

let batchpath cc prim olvl (v1, v2)  =
  Printf.sprintf "%s/%s/%s-%s-%s_vs_%s-%s-%s-%s.batch" !opt_outdir prim.primname
    cc.ccname (ccv2s v1) olvl
    cc.ccname (ccv2s v2) olvl
    prim.primname

let add_cpair_to_manifest cc prim ~v1 ~v2 ~binspec1 ~binspec2 olvl manifest implementation =
  let bp bspec = Input.BinaryPath.to_string bspec.Input.path in
  let pair = {
    left = {
      implementation;
      primitive = prim.primname;
      compilername = cc.ccname;
      version = v1;
      olvl = olvl;
      binarypath = bp binspec1;
    };
    right = {
      implementation;
      primitive = prim.primname;
      compilername = cc.ccname;
      version = v2;
      olvl = olvl;
      binarypath = bp binspec2;
    };
  } in
  Manifest.add manifest pair

let mpair f (a, b) = (f a, f b)

let path_exists p =
  let open FileUtil in
  match test (And (Is_file, Is_exec)) p with
  | true -> Some p
  | false -> None

let paths_both_exist p1 p2 =
  match (path_exists p1, path_exists p2) with
  | Some p1, Some p2 -> Some (p1, p2)
  | _ -> None

let generate_batch_for_binaries builddir cc prim (binspec1, binspec2) =
  let impl2sym impl = Printf.sprintf "%s_%s" impl prim.primname in
  (* 7.1. Add the two binaries *)
  let binidx1, run = Batch.Run.add_binary binspec1 (Batch.Run.empty ()) in
  let binidx2, run = Batch.Run.add_binary binspec2 run in
  let do_impl = do_impl ~binidx1 ~binidx2 ~binspec1 ~binspec2 in
  let symbols = List.map ~f:impl2sym prim.implementations in
  (* 7.2. Add all symbol pairs, one pair for each implementation of a primitive *)
  let run = List.fold_left ~init:run ~f:do_impl symbols in
  Batch.add_run run (Batch.empty ())

let generate_batch_for_olvl builddir cc prim (v1, v2) manifest olvl =
  (* 7. Generate batch file *)
  let binpath v = Printf.sprintf "%s/%s/%s-%s-%s-%s" builddir prim.primname
        cc.ccname (ccv2s v) olvl prim.primname
  in
  let bspec binpath = Input.create_binary_spec binpath in
  let paths = paths_both_exist (binpath v1) (binpath v2) in
  Option.value_map paths  ~default:manifest ~f:(fun paths ->
      let bs = mpair bspec paths in
      let batch = generate_batch_for_binaries builddir cc prim bs in
      let batchpath = batchpath cc prim olvl (v1, v2)  in
      FileUtil.mkdir ~parent:true (FilePath.dirname batchpath);
      Sexp.save_hum batchpath (Batch.sexp_of_t batch);
      let (binspec1, binspec2) = bs in
      List.fold_left ~init:manifest prim.implementations
        ~f:(add_cpair_to_manifest cc prim ~v1 ~v2 ~binspec1 ~binspec2 olvl))

let generate_batch_for_vpair builddir cc prim manifest vpair =
  (* 6. For each optimization level *)
  let olvls = ["O0"; "O1"; "O2"; "O3"; "Os"] in
  List.fold_left ~init:manifest olvls
    ~f:(generate_batch_for_olvl builddir cc prim vpair)

let generate_batch_for_group builddir compiler prim ~key:_ ~data:vpairs manifest =
  (* 5. For each version pair *)
  List.fold_left ~init:manifest vpairs
    ~f:(generate_batch_for_vpair builddir compiler prim)

let generate_batch_for_ccprim builddir grouping pair_mode primitive manifest compiler =
  (* 3. Group the compiler versions as requested *)
  let groups = group_versions grouping compiler.versions in
  let print_group ~key:group ~data:versions =
    Printf.printf "%s\n" group;
    List.iter ~f:(fun v -> Printf.printf "  %s\n" (ccv2s v)) versions
  in
  Printf.printf "-- Groupings ---\n";
  Map.iter ~f:print_group groups;
  let groups = Map.map ~f:(gen_group_pairs pair_mode) groups in
  Printf.printf "-- Comparisons ---\n";
  Map.iter ~f:print_group_pairs groups;
  (* 4. For each group of compiler versions *)
  Map.fold ~init:manifest groups
    ~f:(generate_batch_for_group builddir compiler primitive)

let do_primitive builddir grouping pair_mode compilers manifest primitive =
  (* 2. For each compiler *)
  List.fold_left ~init:manifest compilers
    ~f:(generate_batch_for_ccprim builddir grouping pair_mode primitive)

let do_generate_batches builddir grouping pair_mode compilers primitives =
  (* 1. For each primitive *)
  List.fold_left ~init:Manifest.empty
    ~f:(do_primitive builddir grouping pair_mode compilers) primitives

let grouping str = match str with
  | "major" -> GroupByMajor
  | "minor" -> GroupByMinor
  | "all" -> GroupAll
  | _ -> Printf.eprintf "Unknown grouping policy '%s'\n%!" str;
         exit 2

let pairing str = match str with
  | "adjacent" -> AdjacentPairs
  | "unique" -> UniquePairs
  | _ ->
    Printf.eprintf
      "Unknown pairing mode '%s' (want one of adjacent|unique)\n%!" str;
    exit 2

let filter_primitives selected =
  let is_selected p = match selected with
    | [] -> true
    | _ -> List.mem ~equal:String.equal selected p.primname
  in
  List.filter ~f:is_selected

let dump_manifest mp manifest =
  match mp with
  | None -> ()
  | Some path -> Sexp.save_hum path (Manifest.sexp_of_t manifest)

let generate_batches outdir builddir configpath cc ccver group_by pair_mode
    selected_primitives manifestpath verbose () =
  match outdir with
  | None -> ()
  | Some path ->
    begin
      match Sys.is_directory ~follow_symlinks:true path with
      | `No | `Unknown ->
        Printf.eprintf "Output path '%s' is not a directory" path;
        exit 2
      | `Yes ->
        opt_outdir := path
    end;
  let compilers, primitives = parse_config configpath in
  let compilers = prune_compilers compilers cc ccver in
  let primitives = filter_primitives selected_primitives primitives in
  let group_by = grouping group_by in
  let pair_mode = pairing pair_mode in
  let manifest = do_generate_batches builddir group_by pair_mode compilers primitives in
  dump_manifest manifestpath manifest

let command =
  Command.basic
    ~summary:"generated batch files"
    Command.Spec.(
      empty
      +> flag "-o" (optional string) ~doc:"output directory"
      +> flag "-b" (required string) ~doc:"build artifacts directory"
      +> flag "-c" (required string) ~doc:"config file"
      +> flag "-C" (optional string) ~doc:"compiler compiler specification"
      +> flag "-V" (optional string)
              ~doc:"ccver compiler version regexp (requires -C)"
      +> flag "-G" (optional_with_default "all" string)
              ~doc:"group Group by [major|minor|all(default)]"
      +> flag "-p" (optional_with_default "adjacent" string)
        ~doc:"how to pair compiler versions within a group"
      +> flag "-P" (listed string) ~doc:"primitive Limit to specified primitives"
      +> flag "-m" (optional string)
        ~doc:"path Path for outputting a manifest of generated comparisons"
      +> flag "-v" no_arg ~doc:" enable verbose output")
    generate_batches
