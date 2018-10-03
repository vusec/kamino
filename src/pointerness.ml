module D = Debug.Make(struct let name = "Pointerness" and default=`NoDebug end)
open D

module ValType =
struct
  type t = Ssa.value

  let cmp_typ typ1 typ2 =
    let open Type in
    match typ1, typ2 with
    | Array _, _
    | _, Array _ -> failwith "cmp_typ called with arrays, not implemented"
    | TMem _, _
    | _, TMem _ -> failwith "cmp_typ called with TMem, not implemented"
    | Reg n1, Reg n2 -> n1 - n2

  let compare val1 val2 =
    let open Ssa in
    match val1, val2 with
    | Lab str1, Lab str2 ->
      String.compare str1 str2
    | Lab _, _ ->
      -1
    | _, Lab _ ->
      1
    | Int (bi1, t1), Int (bi2, t2) ->
      let d = cmp_typ t1 t2 in
      if d <> 0 then begin
        Big_int_Z.compare_big_int bi1 bi2
      end else begin
        d
      end
    | Int _, Var _ ->
      -1
    | Var _, Int _ ->
      1
    | Var v1, Var v2 ->
      Var.compare v1 v2
end

module VM = BatMap.Make(ValType)

module Lattice =
struct
  type t = bool VM.t

  let to_str map =
    let to_s (k, v) = Printf.sprintf "%s : %b" (Pp.value_to_string k) v in
    let kvs = VM.fold (fun k v acc ->
        (k, v) :: acc) map [] in
    Print.list_to_string to_s kvs

  let top = VM.empty
  let get k map =
    (* If  found, use the inferred boolean; else, it's not a definite pointer *)
    try
      VM.find k map
    with Not_found -> false

  let meet map1 map2 =
    let str1 = (to_str map1) in
    let str2 = (to_str map2) in
    dprintf "Lattice.meet <<<%s | %s>>>" str1 str2;
    VM.merge (fun k v1 v2 ->
        match (v1, v2) with
        | None, None -> None
        | Some v, None
        | None, Some v -> Some v
        | Some v1, Some v2 -> Some (v1 || v2)
      ) map1 map2
  let equal = VM.equal (fun a b -> a = b)
end


module FwdDataflow =
struct
  module G = Cfg.SSA.G
  module L = Lattice
  let s0 _ = Cfg.SSA.G.V.create Cfg.BB_Entry
  let init _ = VM.empty
  let dir = GraphDataflow.Forward

  let examine_stmt map s =
    dprintf "Looking at %s" (Pp.ssa_stmt_to_string s);
    let is_p value =
      try
        VM.find value map
      with Not_found -> false
    in
    match s with
    | Ssa.Move (avar, Ssa.BinOp (bop, val1, val2), _)
      when bop = Type.PLUS ->
      begin
        let avar_is_p = match is_p val1, is_p val2 with
        | false, false -> false
        | false, true
        | true, false -> true
        | true, true ->
          (*
           * Addition of pointers. It /can/ happen but at this stage let's
           * assume that if we run into this, it's our algorithm that messed
           * up.
           *)
          failwith "pointer PLUS pointer"
        in
        if avar_is_p then begin
          VM.add (Ssa.Var avar) true map
        end else begin
          map
        end
      end
    | Ssa.Move (avar, Ssa.BinOp (bop, val1, val2), _)
      when bop = Type.MINUS ->
      begin
        let avar_is_p = match is_p val1, is_p val2 with
        | false, false -> false
        | false, true
        | true, false -> true
        | true, true ->
          (* Subtraction of pointers is not a pointer *)
          false
        in
        if avar_is_p then begin
          VM.add (Ssa.Var avar) true map
        end else begin
          map
        end
      end
    | Ssa.Move (_, Ssa.Load (_, idx, _, _), _)
    | Ssa.Move (_, Ssa.Store (_, idx, _, _, _), _) ->
      (*
       * Notice that we'll happily mark an Ssa.Int as a pointer (it's a
       * global). And of course every value derived from that is also
       * a pointer.
       *)
      dprintf "Marking %s as a pointer" (Pp.value_to_string idx);
      VM.add idx true map
    | Ssa.Move (avar, Ssa.Phi vs, _) ->
      begin
        try
          (*
           * If all of the phi vars are pointers, the avar is a pointer too.
           * Note that one var isn't enough:
           *     if (x) { y = -err; } else { y = ptr; }
           *     ...
           *     if (IS_ERR(y)) { error(); } else { z = *y }
           *)
          ignore(List.find (fun v ->
              not (is_p (Ssa.Var v))) vs);
          (* Found a var that's not necessarily a pointer *)
          map
        with Not_found ->
          VM.add (Ssa.Var avar) true map
      end
    | _ ->
      map
  let transfer_function g v lattice =
    dprintf "fwd_transfer_function";
    let stmts = Cfg.SSA.get_stmts g v in
    List.fold_left examine_stmt lattice stmts
end

let is_pointer cfg v value =
  let module Fwd = GraphDataflow.Make(FwdDataflow) in
  let (lin, lout) = Fwd.worklist_iterate cfg in
  Cfg.SSA.G.iter_vertex (fun v ->
      let lin = lin v in
      dprintf "%s: l_in =\n%s\n" (Cfg.SSA.v2s v) (Lattice.to_str lin);
      let lout = lout v in
      dprintf "%s: l_out =\n%s\n" (Cfg.SSA.v2s v) (Lattice.to_str lout);
    ) cfg;
  if debug () then begin
    Graph_dump.output_ssa stderr cfg
  end;
  Lattice.get value (lout v)
