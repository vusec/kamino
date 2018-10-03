module D = Debug.Make(struct let name = "Callinfo" and default=`Debug end)
open D

module Addr =
struct
  type t = Type.addr
  let compare = Int64.compare
end

module AddrMap = BatMap.Make(Addr)

type t = {
  map : Callgraph.call_target AddrMap.t;
}

let empty = {map = AddrMap.empty}

let callsite = Callgraph.callsite

let add t ct =
  let to_s ct =
    Sexplib.Sexp.to_string_hum (Callgraph.sexp_of_call_target ct)
  in
  let site = callsite ct in
  match AddrMap.Exceptionless.find site t.map with
  | None ->
    {t with map = AddrMap.add site ct t.map}
  | Some pct ->
    let open Callgraph in
    match pct, ct with
    | DirectCall (site1, tgt1), DirectCall (site2, tgt2) when site1 = site2 && tgt1 = tgt2 ->
      dprintf "XXX: WTF, this can happen because of a bug elsewhere \
               in the program and no time to track this down now :(";
      t
    | IndirectCall site1, IndirectCall site2 when site1 = site2 ->
      dprintf "XXX: WTF, this can happen because of a bug elsewhere \
               in the program and no time to track this down now :(";
      t
    | _ ->
      let s = Printf.sprintf "tried to add the same callsite to callinfo: \
                              new %s, prev %s"
          (to_s ct) (to_s pct)
      in
      failwith s

let call_at_addr t addr =
  AddrMap.Exceptionless.find addr t.map

let fold f t acc =
  AddrMap.fold (fun _ ct acc -> f ct acc) t.map acc

let filter_by_site f t =
  AddrMap.fold (fun site ct acc ->
      if f site then
        ct :: acc
      else
        acc) t.map []

let sexp_of_t t =
  let open Sexplib in
  let calls = BatList.of_enum (AddrMap.values t.map) in
  let calls = Std.sexp_of_list Callgraph.sexp_of_call_target calls in
  Sexp.List [Sexp.Atom "callinfo"; calls;]

let to_string t =
  let open Sexplib in
  Sexp.to_string_hum (sexp_of_t t)
