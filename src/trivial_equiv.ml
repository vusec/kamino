open Core.Std
open Core_extended.Std
open Sexplib.Std

module Cluster = Eval_cluster.BaseCluster(Eval_cluster.PrimitivesSubject)

type binary = {
  path : string;
  asmprog : Asmir.asmprogram;
  ranges : (string list * Int64.t * Int64.t) list;
}

type func = {
  low : Int64.t;
  high : Int64.t;
  names : string list;
  astcfg : Cfg.AST.G.t;
}

let func_name f = match f.names with
  | n :: _ -> n
  | _ -> failwith (Printf.sprintf "No name for function at addr %#Lx" f.low)

let load_binary path =
  let asmprog = Asmir.open_program path in
  let ranges = Asmir.get_function_ranges asmprog in
  let ranges = Misc.demangle_franges ranges in
  let ranges = Misc.dedup_franges ranges in
  {
    path;
    asmprog;
    ranges;
  }

let find_func binary addr =
  try
    List.find_exn ~f:(fun (_, s, _) -> Int64.equal s addr) binary.ranges
  with Not_found ->
    let s =  Printf.sprintf "Requested function address %#Lx not found in %s"
        addr binary.path
    in
    failwith s

let load_func binary addr =
  let (names, s, e) = find_func binary addr in
  let ast = Asmir.asmprogram_to_bap_range binary.asmprog s e in
  {
    low = s;
    high = e;
    names;
    astcfg = Cfg_ast.of_prog ast;
  }

let load_func_info binaries fi =
  let idx = fi.Batch.Run.binary_idx in
  let binary =
    try
      List.nth_exn binaries idx
    with Not_found ->
      let s = Printf.sprintf "Requested binary not there (%d)" idx in
      failwith s
  in
  load_func binary fi.Batch.Run.addr

let do_inline_info pathmap binaries ii =
  let left = load_func_info binaries ii.Batch.Run.parent in
  let right = load_func_info binaries ii.Batch.Run.out_of_line_copy in
  let res = match Misc.astcfgs_identical left.astcfg right.astcfg with
    | BatResult.Ok () -> "identical"
    | BatResult.Bad s -> s
  in
  match Cluster.of_inline (Map.find_exn pathmap) ii with
  | Ok cluster ->
    Printf.printf "%s: %s\n" (Cluster.to_key cluster) res
  | Error err ->
    let s = Printf.sprintf "Couldn't parse cluster: %s" (Error.to_string_hum err) in
    failwith s

let build_pathmap binaries =
  let paths = List.map binaries
      ~f:(fun spec -> Input.BinaryPath.to_string spec.Input.path)
  in
  let _, ipaths = List.fold_left ~init:(0, []) ~f:(fun (i, acc) path ->
      (i + 1, ((i, path) :: acc))) paths in
  Map.of_alist_exn ~comparator:Int.comparator ipaths

let do_trivial_equiv batchpath () =
  let batch = Batch.from_file batchpath in
  match Batch.runs batch with
  | [run] ->
    begin
      let binaries = Batch.Run.binaries run in
      if List.length binaries <> 2 then begin
        failwith "Expected exactly two binaries"
      end;
      let pathmap = build_pathmap binaries in
      let binaries = List.map binaries
          ~f:(fun spec -> load_binary (Input.BinaryPath.to_string spec.Input.path))
      in
      let inline_infos = Batch.Run.inlines run in
      List.iter ~f:(do_inline_info pathmap binaries) inline_infos 
    end
  | _ ->
    failwith "Expected exactly one run in the batch file"

let command =
  Command.basic
    ~summary:"Check for trivial equivalence"
    Command.Spec.(
      empty
      +> flag "-b" (required string) ~doc:" Path to batch file"
    )
    do_trivial_equiv

let () =
  Command.run ~version:"0.1" command

