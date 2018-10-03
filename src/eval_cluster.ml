open Core.Std
open Core_extended.Std

module type ClusterSubject =
sig
  type t
  val to_string : t -> string
  val to_key : t -> string
  val parse : (string -> string option ) -> string -> (t, Error.t) Result.t
  val of_func_info : (int -> FilePath.filename) -> Batch.Run.func_info -> (t, Error.t) Result.t
  val of_key : string -> (t, Error.t) Result.t
  val symbol : t -> string
  val compiler : t -> string
  val version : t -> string
  val path : t -> string
  val address : t -> Int64.t
  val equal : t -> t -> bool
  include Comparable.S with type t := t
end

module FuzzyInlinesSubject : ClusterSubject =
struct
  module T =
  struct
  type t = {
    path: string;
    symbol: string;
    addr: Int64.t;
  }
  let to_string t = Printf.sprintf "XXX: subj %s" t.symbol
  let to_key t =
    Printf.sprintf "%s:%s" t.path t.symbol
  let sexp_of_t _ = failwith "TBD"
  let t_of_sexp _ = failwith "TBD"
  let compare a b = String.compare (to_key a) (to_key b)
  let of_key str = failwith "FuzzyInlinesSubject.of_key: not implemented"
  let parse progmap str =
    (*
     * For fuzzy inlines, we can deduce the binary name simply by looking
     * at the cluster.
     *)
    let re = Str.regexp "\\(.+\\)-\\([^-]+\\)-\\([a-fA-F0-9]+\\)$" in
    if Str.string_match re str 0 then begin
      let prog = Str.matched_group 1 str in
      let symbol = Str.matched_group 2 str in
      let addr = "0x" ^ (Str.matched_group 3 str) in
      (* Lookup path to binary using the basename *)
      match progmap prog with
      | None ->
        let s = Printf.sprintf "No binary path for %s" prog in
        Result.Error (Core.Error.of_string s)
      | Some path ->
        begin
          Result.Ok {
            symbol;
            path;
            addr = Int64.of_string addr;
          }
        end
    end else begin
        let s = Printf.sprintf "Could not parse subject %s" str in
        Result.Error (Core.Error.of_string s)
    end
  let of_func_info pathmap info =
    let module R = Batch.Run in
    let binidx = info.R.binary_idx in
    try
      (* The pathmap allows us to map the binary index (an int) used in the
       * batch file to the binary path specified in the same batch file. I.e.
       * this function is specific to the batch file we're parsing.
       *)
      let path = pathmap binidx in
      let symbol = info.R.name in
      let addr = info.R.addr in
      Result.Ok {
        symbol;
        path;
        addr;
      }
    with Not_found ->
      let s = Printf.sprintf "of_func_info: binary %d not found" binidx in
      Result.Error (Core.Error.of_string s)
  let symbol t = t.symbol
  let compiler _ = failwith ".compiler on FuzzyInlinesSubject"
  let version _ = failwith ".version on FuzzyInlinesSubject"
  let path t = t.path
  let address t = t.addr
  let equal t1 t2 = t1 = t2
  end
  include T
  include Comparable.Make(T)
end

module PrimitivesSubject : ClusterSubject =
struct
  module T = struct
  type t = {
    compiler:string;
    version:string;
    case:string;
    olevel:string;
    symbol:string;
    address:string;
    path:string;
  }
  let to_string subject =
    Printf.sprintf "%s-%s-%s-%s-%s-%s" subject.case subject.compiler
      subject.version subject.olevel subject.symbol subject.address
  let to_key subject =
    (*
     * Do no include the symbol address, because that might vary
     * between linked binaries!
     *)
    Printf.sprintf "%s-%s-%s-%s-%s" subject.case subject.compiler
      subject.version subject.olevel subject.symbol
  let bin_regexp_str =
    String.concat ~sep:"-" [
        "\\(clang\\|gcc\\)";
        (* We have results that use a '.' or a '_' for the compiler
           version separator. So match any char between numbers.*)
        "\\([0-9]+.[0-9]+.[0-9]+\\)";
        "\\([a-zA-Z0-9_]+\\)";
        "\\([^-]+\\)";
    ]

  let sexp_of_t _ = failwith "TBD"
  let t_of_sexp _ = failwith "TBD"
(* This is the reason we don't want to use polymorphic compare; we
 * need to use to_key here to omit the symbol address *)
  let compare a b = String.compare (to_key a) (to_key b)

  let bin_regexp = Str.regexp bin_regexp_str

  let of_key str =
    let key_regexp =
      Str.regexp "\\([^-]+\\)-\\([^-]+\\)-\\([^-]+\\)-\\([^-]+\\)-\\([^-]+\\)"
    in
    if Str.string_match key_regexp str 0 then begin
      let case = Str.matched_group 1 str in
      let compiler = Str.matched_group 2 str in
      let version  = Str.matched_group 3 str in
      let olevel = Str.matched_group 4 str in

      let path = Printf.sprintf "%s-%s-%s-%s" compiler version case olevel in
      Result.Ok {
        compiler;
        version;
        case;
        olevel;
        symbol = Str.matched_group 5 str;
        address = "0x0"; (* n/a *)
        path;
      }
    end else begin
      Or_error.error_string
        (Printf.sprintf "of_key: Invalid cluster subject format for %s" str)
    end

  let parse _ str =
    let regexp = Str.regexp (String.concat ~sep:"-" [
        bin_regexp_str;
        "\\([^-]+\\)";
        "\\([0-9a-f]+\\)";
      ]) in
    (*
     * For the primitives, the path to the binary is not immediately
     * available from the cluster name; what we have is the compiler,
     * version and primitive name (a.k.a. case, yuck). Those are enough
     * to reconstruct the binary name, though it further reproduces
     * convention-over-any-trace-of-discoverability-and-debuggability :(
     *)
    if Str.string_match regexp str 0 then begin
      let compiler = Str.matched_group 1 str in
      let version = Str.matched_group 2 str in
      let olevel = Str.matched_group 3 str in
      let case = Str.matched_group 4 str in

      let path = Printf.sprintf "%s-%s-%s-%s" compiler version case olevel in
      Result.Ok {
        compiler;
        version;
        case;
        olevel;
        symbol = Str.matched_group 5 str;
        address = Str.matched_group 6 str;
        path;
      }
    end else Or_error.error_string
        (Printf.sprintf "parse: Invalid cluster subject format for %s" str)

  let of_func_info pathmap info =
    let module R = Batch.Run in
    let binidx = info.R.binary_idx in
    try
      let path = pathmap binidx in
      let symbol = info.R.name in
      let addr = info.R.addr in
      let binname = FilePath.basename path in
      if Str.string_match bin_regexp binname 0 then begin
        Result.Ok {
          compiler = Str.matched_group 1 binname;
          version = Str.matched_group 2 binname;
          case = Str.matched_group 4 binname;
          olevel = Str.matched_group 3 binname;
          symbol;
          address = Printf.sprintf "%Lx" addr;
          path;
        }
      end else begin
        let s = Printf.sprintf "of_func_info: could not parse '%s'" binname in
        Result.Error (Core.Error.of_string s)
      end
    with Not_found ->
      let s = Printf.sprintf "of_func_info: binary %d not found" binidx in
      Result.Error (Core.Error.of_string s)

  let symbol t = t.symbol
  let compiler t = t.compiler
  let version t = t.version
  let path {path} = path
  let address t = Int64.of_string t.address
  let equal t1 t2 = t1 = t2
  end
  include T
  include Comparable.Make(T)
end

module type ClusterSig =
sig
  module Subject : ClusterSubject
  type t
  val left : t -> Subject.t
  val right : t -> Subject.t
  val to_string : t -> string
  val to_key : t -> string
  val of_key : string -> (t, Error.t) Result.t
  val parse : (string -> string option) -> string -> (t, Error.t) Result.t
  val of_inline : (int -> FilePath.filename) -> Batch.Run.inline_info -> (t, Error.t) Result.t
  val compilers : t -> string list (* XXX *)
  val versions : t -> string * string
  val paths : t -> string * string
  val addresses : t -> (Int64.t * Int64.t)
  val is_self : t -> bool
  include Comparable.S with type t := t
end

module BaseCluster(Subject : ClusterSubject) =
struct
  module T = struct
  module Subject = Subject
  type t = {
    lhs: Subject.t;
    rhs: Subject.t;
  }

  let left t = t.lhs
  let right t = t.rhs

  let to_string cl =
    Printf.sprintf "%s vs %s"
      (Subject.to_string cl.lhs)
      (Subject.to_string cl.rhs)
  let to_key cl =
    let lhs = Subject.to_key cl.lhs in
    let rhs = Subject.to_key cl.rhs in
    lhs ^ "--" ^ rhs

  let sexp_of_t _ = failwith "TBD"
  let t_of_sexp _ = failwith "TBD"
  let compare a b = String.compare (to_key a) (to_key b)

  let of_key str =
    let subjects = Str.split (Str.regexp "--") str in
    let subjects = List.map subjects ~f:Subject.of_key in
    match Or_error.combine_errors subjects with
    | Ok [lhs; rhs] ->
      Ok{lhs; rhs}
    | Ok fields ->
      let err = Printf.sprintf "Too many subjects (%d) in cluster %s"
               (List.length fields) str in
      Error (Core.Error.of_string err)
    | Error err ->
      Error (Core.Error.of_list [
          err;
          Core.Error.of_string (Printf.sprintf "Failed to parse cluster %s" str)])

  let parse progmap str =
    let open Result in
    let subjects = Str.split (Str.regexp "--") str in
    let subjects = List.map ~f:(Subject.parse progmap) subjects in
    let subjects = Or_error.combine_errors subjects in
    match subjects with
    | Ok [lhs; rhs] ->
      Ok {lhs; rhs}
    | Ok fields ->
      let err = Printf.sprintf "Too many subjects (%d) in cluster %s"
               (List.length fields) str in
      Error (Core.Error.of_string err)
    | Error err -> Error (Core.Error.of_list [
        err;
        Core.Error.of_string (Printf.sprintf "Failed to parse cluster %s" str)])
  let of_inline pathmap inline =
    let open Batch.Run in
    let lhs = Subject.of_func_info pathmap inline.parent in
    let rhs = Subject.of_func_info pathmap inline.out_of_line_copy in
    let open Result in
    match lhs, rhs with
    | Ok lhs, Ok rhs ->
      Ok {lhs; rhs}
    | Error err, _
    | _, Error err ->
      Error err

  let symbol t =
    let s1 = Subject.symbol t.lhs in
    let s2 = Subject.symbol t.rhs in
    if String.compare s1 s2 <> 0 then begin
      let s = Printf.sprintf "LHS symbol %s != RHS symbol %s"
          s1 s2 in
      failwith s
    end else
      s1
  let compilers t = [Subject.compiler t.lhs; Subject.compiler t.rhs;]
  let versions t = (Subject.version t.lhs, Subject.version t.rhs)
  let paths t = (Subject.path t.lhs, Subject.path t.rhs)
  let addresses t = (Subject.address t.lhs, Subject.address t.rhs)
  let is_self cl = Subject.equal cl.lhs cl.rhs
  end
  include T
  include Comparable.Make(T)
end
