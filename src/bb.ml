module D = Debug.Make(struct let name = "BB" and default=`NoDebug end)
open D

module StringMap = BatMap.Make(String)
type bb_summary = {
    (*
     * Some BBs are synthesized; e.g. in the presence of the x86 rep prefix.
     * Those will not have an address (und es ist gut so).
     *)
    bb_saddr : Type.addr option;
    bb_fbegin: Type.addr;
    id: Cfg.bbid;
    tfs: Transfer_function.t StringMap.t option;
    (*
     * Transfer functions that produce outputs that are not
     * visible/useful in the rest of the function (probably
     * because they are only calculating intermediate values).
     * We still want to allow them to take part in matching.
     * Motivating example:
     *
     * r1 = F(blah)	r3 = F(blah)
     * r2 = r1 + 2
     * Here, the LHS will have <r2> = F(blah) + 2 as the TF of
     * its sole output. This is what we want to match preferentially.
     * However, if that fails, we should still try to pair
     * r1 <-> r3 (but then it's a subset match).
     *)
    invisible_tfs : Transfer_function.t StringMap.t;
}

module BBidOrd =
struct
  type t = Cfg.bbid
  let compare id1 id2 =
    let open Cfg in
    match (id1, id2) with
    | BB_Entry, BB_Entry -> 0
    | BB_Entry, _ -> -1
    | BB_Exit, BB_Entry -> 1
    | BB_Exit, BB_Exit -> 0
    | BB_Exit, _ -> -1
    | BB_Indirect, BB_Entry
    | BB_Indirect, BB_Exit -> 1
    | BB_Indirect, BB_Indirect -> 0
    | BB_Indirect, _ -> -1
    | BB_Error, BB_Entry
    | BB_Error, BB_Exit
    | BB_Error, BB_Indirect -> 1
    | BB_Error, BB_Error -> 0
    | BB_Error, _ -> -1
    | BB n1, BB n2 -> n1 - n2
    | BB _, _ -> 1
end

module BBidMap = BatMap.Make(BBidOrd)

module Ssa_ext = struct
    open Ssa_ext
    (* For a basic block, get the variables defined and referenced*)
    let def_and_ref stmts =
        let defined = VariableHash.create 8 in
        let referenced = ref VariableSet.empty in
        let visitor = object(self)
            inherit Ssa_ext_visitor.nop
            method visit_stmt stmt = match stmt with
            | Statement.Move (var, exp, attr) ->
                    VariableHash.add defined var exp; Ssa_ext_visitor.DoChildren
            | _ -> Ssa_ext_visitor.DoChildren
            method visit_rvar var =
                referenced := VariableSet.add var !referenced; Ssa_ext_visitor.DoChildren
        end
        in
        ignore(Ssa_ext_visitor.stmts_accept visitor stmts);
        (defined, !referenced)

end

module SSA =
struct
  let is_nop cfg v =
    (* See if the BB has any actual statements. Compilers might generate nops
     * for alignment purposes and those nops might end up forming a BB of
     * their own. Notice that we rely on BAP to notice long nops like
     * lea 0x0(%esi, %eiz, 1), %esi and not emit any BAP IL statements.
    *)
    let module C = Cfg.SSA in
    let stmts_are_nops stmts =
      try
        BatList.find_map (fun s ->
          let open Ssa in
          (match s with
          | Move _
          | Jmp _
          | CJmp _
          | Halt _ -> Some false
          | _ -> None)
        ) stmts
      with Not_found -> true
    in
    let stmts = C.get_stmts cfg v in
    (stmts_are_nops stmts)
  let ends_in_hlt cfg v =
    dprintf "ends_in_hlt";
    let module C = Cfg.SSA in
    let stmts = C.get_stmts cfg v in
    let stmts = List.filter (fun s ->
      match s with
      | Ssa.Label _
      | Ssa.Assert _
      | Ssa.Comment _ ->
        dprintf "false";
        false
      | _ ->
        dprintf "true: %s" (Pp.ssa_stmt_to_string s);
        true) stmts in
    match List.hd (List.rev stmts) with
    | Ssa.Halt _ -> true
    | _ -> false
end

let stmt_get_addr s =
  let () = dprintf "stmt_get_addr: %s" (Pp.ast_stmt_to_string s) in
  (* XXX: are we supposed to only use labels? not sure *)
  let get_addr_from_attrs s =
    let attrs = Ast.get_attrs s in
    let () = dprintf "attrs (%d): " (List.length attrs) in
    try
      let addr = BatList.find_map (fun attr ->
	match attr with
	| Type.Address addr ->
	  let () = dprintf "got addr" in
	  Some addr
	| _ -> let () = dprintf "nope" in None) attrs
      in
      Some addr
    with Not_found -> None
  in
  match s with
  | Ast.Label (Type.Addr addr, _) -> Some addr
  | _ -> get_addr_from_attrs s

let get_bbaddr stmts =
  try
    (* get the first address in the BB *)
    let bbaddr = BatList.find_map stmt_get_addr stmts in
    Some bbaddr
  with Not_found ->
(*
  At least for repnz scas and similar x86 instructions, lifting
  will generate a cjmp to a generated BB refered to by named label.
  It should be safe to ignore those (XXX: we have one binary
  instructing belonging to two BAP il BBs, this may break some assumptions?).
  XXX: for now, ignore BBs we can't assign an address to and hope for the best.
*)
    let bb_str = Print.ast_stmts_to_string stmts in
    let () = dprintf "No address for BB with stmts:\n{\n%s\n}\n)" bb_str in
    None

let ssa_stmt_get_addr s =
  let () = dprintf "stmt_get_addr: %s" (Pp.ssa_stmt_to_string s) in
  (* XXX: are we supposed to only use labels? not sure *)
  let get_addr_from_attrs s =
    let attrs = Ssa.get_attrs s in
    let () = dprintf "attrs (%d): " (List.length attrs) in
    try
      let addr = BatList.find_map (fun attr ->
	match attr with
	| Type.Address addr ->
	  let () = dprintf "got addr" in
	  Some addr
	| _ -> let () = dprintf "nope" in None) attrs
      in
      Some addr
    with Not_found -> None
  in
  match s with
  | Ssa.Label (Type.Addr addr, _) -> Some addr
  | _ -> get_addr_from_attrs s

let get_bbaddr_from_ssa stmts =
  let ssa_stmts_to_string stmts =
    let stmt_strs = List.map Pp.ssa_stmt_to_string stmts in
    List.fold_left (fun acc str ->
      acc ^ str ^ "\n") "" stmt_strs
  in
  try
    (* get the first address in the BB *)
    let bbaddr = BatList.find_map ssa_stmt_get_addr stmts in
    Some bbaddr
  with Not_found ->
(*
  At least for repnz scas and similar x86 instructions, lifting
  will generate a cjmp to a generated BB refered to by named label.
  It should be safe to ignore those (XXX: we have one binary
  instructing belonging to two BAP il BBs, this may break some assumptions?).
  XXX: for now, ignore BBs we can't assign an address to and hope for the best.
*)
    let bb_str = ssa_stmts_to_string stmts in
    let () = dprintf "No address for BB with stmts:\n{\n%s\n}\n)" bb_str in
    None

let get_bbbounds_from_ssa stmts =
  try
    let addrs = BatList.filter_map ssa_stmt_get_addr stmts in
    BatResult.Ok (List.hd addrs, BatList.last addrs)
  with
  | Invalid_argument "Empty List" ->
    BatResult.Bad "Empty list to get_bbbounds_from_ssa"
  | Not_found ->
    failwith "get_bbbounds_from_ssa"

let get_bbbounds_from_ast stmts =
  try
    let addrs = BatList.filter_map stmt_get_addr stmts in
    match addrs with
    | [] -> None
    | [single] -> Some (single, single)
    | low :: rest -> Some (low, BatList.last rest)
  with Not_found ->
    failwith "get_bbbounds_from_ast"

let contains_code stmts =
  List.fold_left (fun acc stmt -> match stmt with
      | Ast.Label _ -> acc
      | Ast.Comment _ -> acc
      | _ -> true) false stmts

let nr_insns cfg bb =
  let v = Cfg.SSA.find_vertex cfg bb.id in
  let stmts = Cfg.SSA.get_stmts cfg v in
  List.fold_left (fun cnt s ->
      match s with
      | Ssa.Label (Type.Addr _, _) -> cnt + 1
      | _ -> cnt) 0 stmts

(* vim: set ts=8 sw=2 tw=80 et :*)
