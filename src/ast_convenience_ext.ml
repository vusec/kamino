include Ast_convenience

let rec ctxs_from_attrs a = match a with
| [] -> []
| h :: t -> ( match h with
    | Type.Context ctx -> ctx :: (ctxs_from_attrs t)
    | _ -> ctxs_from_attrs t)

let get_addr = function
  | Ast.Label ( Type.Addr addr,  _) -> Some addr
  | _ -> None
