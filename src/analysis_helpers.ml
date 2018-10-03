
module SSA =
struct
  module C = Cfg.SSA
  module G = C.G
  module Dom = Dominator.Make(G)
  module Dfs = Graph.Traverse.Dfs(G)
  module VH = Var.VarHash

  open Ssa
  open BatListFull

  let get_stmt_at g loc =
    let (v, n) = loc in
    let stmts = Cfg.SSA.get_stmts g v in
    List.nth stmts n

  let val2var = function
    | Int _ | Lab _ -> None
    | Var v -> Some v

  let val2var_exn = function
    | Int _ | Lab _ -> raise Not_found
    | Var v -> v

  let mem_is_ary mem =
    try
      Var_convenience.Array.is_array (val2var_exn mem)
    with Not_found -> false

  (* Modified from sccvn.ml *)
  let def_info cfg =
    let defs = VH.create 128 in
    let sites = VH.create 128 in
    let add_defs_in_bb bb =
      let add_def i = function
        | Move (v,e,_) -> VH.add sites v (bb,i);
          VH.add defs v e
        | _ -> () in
      List.iteri add_def (C.get_stmts cfg bb) in
    G.iter_vertex add_defs_in_bb cfg;
    let before_entry = (G.V.create Cfg.BB_Entry, -1) in
    (fun var ->
       let def = try Some (VH.find defs var)
         with Not_found -> None in
       (* Globals are defined before BB_Entry *)
       let site = try VH.find sites var
         with Not_found -> before_entry in
       (def, site))

  let pos_dom cfg =
    let {Dom.dom=dom;} =
      Dom.compute_all cfg (G.V.create Cfg.BB_Entry) in
    (fun (bb, i) (bb', i') -> dom bb bb' || (bb = bb' && i < i'))

  (* Copied from sccvn.ml *)
  let fold_postfix_component f g v i =
    let acc = ref i in
    Dfs.postfix_component (fun x -> acc := f x !acc) g v;
    !acc

  let get_varargs_exp exp =
    let vals,_,_,_,_,_,vars,_ = getargs_exp exp in
    (List.filter_map val2var vals) @ (List.flatten vars)
end

module AstCfg = struct
  let remove_identities cfg =
    let aux v cfg =
      let rev_stmts = List.fold_left (fun rev_stmts -> function
          | Ast.Move (avar, Ast.Var rvar, _) when avar = rvar -> rev_stmts
          | _ as stmt -> stmt :: rev_stmts
        ) [] (Cfg.AST.get_stmts cfg v) in
      Cfg.AST.set_stmts cfg v (List.rev rev_stmts)
    in
    Cfg.AST.G.fold_vertex aux cfg cfg
end

module Var = struct
  module VH = Var.VarHash
  let vh_find vh var =
    try
      Some (Var.VarHash.find vh var)
    with Not_found -> None

  let varmap_find vm var =
    try
      Some (Var.VarMap.find var vm)
    with Not_found -> None
end
