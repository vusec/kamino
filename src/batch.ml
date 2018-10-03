module Batch :
sig
  type t

  module Run : sig
    type t
    type func_info = {
      binary_idx: int;
      name: string;
      addr: int64;
    } with sexp

    type inline_info = {
      parent: func_info;
      out_of_line_copy: func_info;
    } with sexp

    val sexp_of_t: t -> Sexplib.Sexp.t

    val empty: unit -> t

    val add_binary: Input.binary_spec -> t -> int * t
    val add_inline: inline_info -> t -> t

    val binaries: t -> Input.binary_spec list
    val inlines: t -> inline_info list
  end

  val empty: unit -> t
  val add_run: Run.t -> t -> t

  val from_file: string -> t
  val sexp_of_t: t -> Sexplib.Sexp.t

  val runs: t -> Run.t list

  val dump_example: unit -> Sexplib.Sexp.t
end = struct
  (* Required to open Sexplib.Std to expose the converters
     http://article.gmane.org/gmane.comp.lang.caml.general/52962
  *)
  open Sexplib.Std

  module Run = struct
    type func_info = {
      binary_idx: int;
      name: string;
      addr: int64;
    } with sexp

    type inline_info = {
      parent: func_info;
      out_of_line_copy: func_info;
    } with sexp

    type t = {
      (* A binary consists of a path and parameters *)
      binaries: Input.binary_spec list;
      inlines : inline_info list;
    } with sexp

    let empty () = {binaries = []; inlines = []}

    let add_binary binary t = let {binaries=binaries} = t in
      let t' = {t with binaries = binaries @ [binary]} in
      (List.length binaries, t')

    let add_inline inline t = let {inlines=inlines} = t in
      {t with inlines = inlines @ [inline]}

    let binaries {binaries} = binaries
    let inlines {inlines} = inlines
  end

  type t = {version:int; runs: Run.t list} with sexp

  let empty () = {version=1; runs=[]}
  let add_run run t = let {runs=runs} = t in
    {t with runs=runs @ [run]}

  let from_file file =
    t_of_sexp (Sexplib.Sexp.load_sexp file)

  let runs {runs} = runs

  let dump_example () =
    let parameters = Input.BinaryParameters.create 2 in
    Input.BinaryParameters.add parameters "key1" ["value1"];
    Input.BinaryParameters.add parameters "key2" ["value2"];
    let run = (Run.empty ()) in
    let _,run = Run.add_binary (Input.create_binary_spec ~parameters:parameters "binary1") run in
    let _,run = Run.add_binary (Input.create_binary_spec "binary2") run in
    let add_inline (run : Run.t) (inline: Run.inline_info) : Run.t = Run.add_inline inline run in
    let inlines =
      let open Run in
      [
      {parent={binary_idx=0; name="foo"; addr=Int64.of_int 0xdeadbeef};
       out_of_line_copy={binary_idx=1; name="foo"; addr=Int64.of_int 0xdeadbeef}
      };
      {parent={binary_idx= 0; name="bar"; addr=Int64.of_int 0xcafebabe};
       out_of_line_copy={binary_idx=0; name="baz"; addr=Int64.of_int 0xdeadbeef}
    }] in
    let run = List.fold_left (add_inline : Run.t -> Run.inline_info -> Run.t) (run:Run.t) (inlines: Run.inline_info list) in
    sexp_of_t {
      version = 1;
      runs = [run]
    }
end

include Batch
