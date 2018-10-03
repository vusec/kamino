let pair_to_string pp = function (f, s) -> Printf.sprintf "(%s,%s)" (pp f) (pp s)

let enum_to_string ?(enclosing=("( ", " )")) ?(sep=",") pp enum =
    (fst enclosing) ^ (BatEnum.fold (fun acc e -> if acc <> "" then acc ^ sep ^ (pp e) else (pp e)) "" enum) ^ (snd enclosing)

let list_to_string ?(enclosing=("[ ", " ]")) ?(sep=",") pp l = enum_to_string ~enclosing ~sep pp (BatList.enum l)

let set_to_string ?(enclosing=("( ", " )")) ?(sep=",") pp s = enum_to_string ~enclosing ~sep pp (BatSet.enum s)

let ast_stmts_to_string stmts =
  let stmt_strs = List.map Pp.ast_stmt_to_string stmts in
  List.fold_left (fun acc str ->
    acc ^ str ^ "\n") "" stmt_strs

let context_to_string c =
    let attr_to_string = Pp.pp2string (fun p -> p#attr) in
    attr_to_string (Type.Context c)

let taint_mapping_to_string m =
    Hashtbl.fold (fun addr mapping i -> 
        Printf.sprintf "0x%Lx =  %s\n%s" addr
        (Hashtbl.fold ( fun var ctxs i' -> 
            Printf.sprintf "%s -> %s\n%s" (Pp.var_to_string var)
            (list_to_string context_to_string ctxs) i'
        ) mapping "") i
    ) m ""

let hashtbl_to_string pp_key pp_value tbl =
    Hashtbl.fold( fun k v acc -> acc ^ (Printf.sprintf "%s = %s\n" (pp_key k) (pp_value
    v))) tbl ""

let bitset_to_string bset =
  let out = BatIO.output_string () in
  let () = BatBitSet.print out bset in
  BatIO.close_out out

(*
 * We insert fold markers to make our debugging output easy to navigate.
 * Use markers that we can't possibly produce in our well-formed output.
 * To use this, open with
 *    view "+set foldmarker={>{{,}<}}" "+set foldmethod=marker" $file
 *)
let fo = "{>{{"
let fc = "}<}}"
