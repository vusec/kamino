open Sexplib.Std

module StringSet = BatSet.Make(String)

let hash_append tbl key value =
  let () = match Misc.bathashtbl_find_option tbl key with
  | Some list -> BatHashtbl.replace tbl key (value :: list)
  | None -> BatHashtbl.add tbl key [value]
  in
  tbl

let binopt_filter_funcs funcs =
  let opts = Input.BinaryParameters.create 1 in
  let funcs = BatEnum.map (Printf.sprintf "%#Lx") funcs in
  Input.BinaryParameters.add opts "funcs" (BatList.of_enum funcs);
  opts

type range = (int64 * int64) list with sexp

type fn_loc = {
  name: string;
  range: range;
} with sexp

type ranges = {
  ranges: range list;
} with sexp

type inline_instance = {
  caller: fn_loc;
  inline: fn_loc;
  callees: ranges;
} with sexp

type binary_inline_info = {
  binary: string;
  inlines: inline_instance list;
} with sexp

let dump_example () =
  Printf.printf "%s\n" (Sexplib.Sexp.to_string_hum (sexp_of_binary_inline_info
  {
    binary="binary";
    inlines=[{
      caller={
        name="caller";
        range=[(Int64.zero, Int64.zero)];
      };
      inline={
        name="inline";
        range=[(Int64.zero, Int64.zero)];
      };
      callees={
        ranges=[[(Int64.zero, Int64.zero)];[(Int64.zero, Int64.zero)]];
      };
   }]}))

let binary_inline_info_from_file file =
  binary_inline_info_of_sexp (Sexplib.Sexp.load_sexp file)

let spec_of_inline_info input =
  let info = binary_inline_info_of_sexp (Sexplib.Sexp.load_sexp input) in
  let funcs = List.fold_left (fun acc inline ->
    BatSet.add (fst(List.hd inline.caller.range)) acc
  ) BatSet.empty info.inlines in
  let binopts = binopt_filter_funcs (BatSet.enum funcs) in
  let binary_spec = Input.create_binary_spec ~parameters:binopts info.binary in
  let _,run = Batch.Run.add_binary binary_spec (Batch.Run.empty ()) in
  let _,run = Batch.Run.add_binary binary_spec run in
  let add_pair run inline_instance =
    let module R =  Batch.Run in
    let parent = {
      R.binary_idx=0;
      R.name=inline_instance.caller.name;
      R.addr=fst(List.hd inline_instance.caller.range)} in
    let out_of_line_copy = {
      R.binary_idx=1;
      R.name=inline_instance.inline.name;
      R.addr=fst(List.hd (List.hd inline_instance.callees.ranges))} in
    R.add_inline {R.parent=parent; R.out_of_line_copy=out_of_line_copy} run in
  let run = List.fold_left add_pair run info.inlines in
  let batch = Batch.add_run run (Batch.empty ()) in
  Some (Sexplib.Sexp.to_string_hum (Batch.sexp_of_t batch))

let spec_for_binary_self_scan binpath =
  (*
   * Generate a batch file to scan every function of this binary
   * with every other function. But if we compare functions A, B
   * we don't want to consider the pair B, A.
   *)
  let asm_prog = Asmir.open_program binpath in
  let arch = Asmir.get_asmprogram_arch asm_prog in
  let franges = Asmir.get_function_ranges asm_prog in
  let franges = Misc.demangle_franges franges in
  let franges = Misc.dedup_franges franges in
  (*
   * Because of the way we compile some packages, the compiler might
   * emit multiple standalone copies of an inlined function, each with
   * the same name. We only want to consider one of those for comparison
   * purposes.
   *)
  let franges = BatList.sort_unique (fun (names1, s1, e1) (names2, s2, e2) ->
      let module SS = StringSet in
      let ss1 = SS.of_enum (BatList.enum names1) in
      let ss2 = SS.of_enum (BatList.enum names2) in
      let inter = SS.inter ss1 ss2 in
      match SS.is_empty inter with
      | false ->
        if Int64.compare (Int64.sub e1  s1) (Int64.sub e2 s2) <> 0 then begin
          let syms = Print.enum_to_string ~enclosing:("", "") ~sep:(", ")
              (fun x -> x) (SS.enum inter) in
          let s = Printf.sprintf
              "Functions @%#Lx, @%#Lx share some symbol names (%s), \
              but don't have the same size" s1 s2 syms in
          failwith s
        end;
        0
      | true ->
        (* Just need a consistent ordering *)
        let s1 = Print.list_to_string (fun x -> x) names1 in
        let s2 = Print.list_to_string (fun x -> x) names2 in
        String.compare s1 s2
    ) franges
  in
  let frpairs = Misc.list_unique_pairs franges in
  let funcs = BatEnum.map (fun (name, s, e) -> s) (BatList.enum franges) in
  let binopts = binopt_filter_funcs funcs in
  let binspec = Input.create_binary_spec ~parameters:binopts binpath in
  let open Batch.Run in
  let _, run = add_binary binspec (Batch.Run.empty ()) in
  let _, run = add_binary binspec run in
  let run = List.fold_left (fun run (frange1, frange2) ->
      let nameaddr frange =
        match frange with
        | (name :: _, s, _) -> name, s
        | ([], s, e) ->
          failwith (Printf.sprintf "No name for frange (%#Lx, %#Lx)" s e)
      in
      let name1, addr1 = nameaddr frange1 in
      let name2, addr2 = nameaddr frange2 in
      let left = {binary_idx = 0; name = name1; addr = addr1} in
      let right = {binary_idx = 1; name = name2; addr = addr2} in
      add_inline {parent = left; out_of_line_copy = right} run
    ) run frpairs in
  let batch = Batch.add_run run (Batch.empty ()) in
  Some (Sexplib.Sexp.to_string_hum (Batch.sexp_of_t batch))
