module D = Debug.Make(struct let name = "Memrange" and default=`NoDebug end)
open D
open Big_int_Z

module Tree = Imtree.Tree(Int64)

module RType =
struct
  type t = int
  let of_typ = function
    | Type.Reg n -> n
    | _ -> failwith "Not a reg type"
  let compare a b = a - b
end
(* We generate intervals for globals by using the address as an offset from a base pointer
   that represents the "global" memory region.
   The right approach would be to first compute the interval tree by observing all global accesses in
   all functions, but we can short-circuit this by only looking at the global accesses performed in the
   function being analyzed given that side-effects of callees have been properly propagated.

   XXX: Note that side-effects only propagate kills (i.e., writes to globals)
   However, ....
*)
module Memrange =
struct
  module WidthSet = BatSet.Make(RType)
  module VarHash = Var.VarHash
  type t = ((Tree.t  * WidthSet.t) VarHash.t)

  let create inputs =
    let module VarSet = Var.VarSet in
    let memr = VarHash.create (VarSet.cardinal inputs) in
    VarSet.fold (fun inp htbl ->
        VarHash.add htbl inp (Tree.empty, WidthSet.empty);
        htbl) inputs memr
  let access memr base_var ~low ~high typ =
    let (tree, widths) =
      try
        VarHash.find memr base_var
      with Not_found ->
        (Tree.empty, WidthSet.empty)
    in
    let width = Typecheck.bytes_of_width typ in
    dprintf "Memrange.access [%Ld-%Ld] %d" low high width;
    let tree' = Tree.insert tree (low, high) in
    let widths' = WidthSet.add width widths in
    VarHash.replace memr base_var (tree', widths');
    memr
  let to_string memr =
    let pp_ws widths =
      let strlist = WidthSet.fold (fun w acc ->
          (w)::acc) widths [] in
      let pp_int = Printf.sprintf "%d" in
      Print.list_to_string pp_int strlist
    in
    let strlist = VarHash.fold (fun var (tree, widths) acc ->
        let v = Pp.var_to_string var in
        let t = Tree.to_string tree in
        let ws = pp_ws widths in
        let str = Printf.sprintf "%s: %s (widths %s)" v t ws in
        str::acc
      ) memr []
    in
    let id = (fun x -> x) in
    Print.list_to_string ~enclosing:("", "")
      ~sep:"\n" id strlist

  let fold_pointers f acc memr =
    VarHash.fold (fun base _ acc ->
      f base acc) memr acc
  let fold_intervals f acc memr var =
    try
      let itree, _ = VarHash.find memr var in
      Tree.fold_intervals f acc itree
    with Not_found ->
      let str = Printf.sprintf "Could not find var %s in memr: %s"
        (Pp.var_to_string var) (to_string memr) in
      failwith str
end

include Memrange
