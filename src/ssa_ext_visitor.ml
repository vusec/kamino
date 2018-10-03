(** Visitor for extended ssa *)
open Ssa_ext

(* XXX: Should we implement SkipParent? 
 * Note: No obvious semantics when children disagree
 * *)
type 'a visit_action = 
  | SkipChildren
  | ChangeTo of 'a
  | DoChildren
  | ChangeToAndDoChildren of 'a
  | DoParent

type direction = TopToBottom | BottomToTop

class type t = object
  method get_direction : direction
  (** Called when visiting an expression *)
  method visit_exp: Expression.t -> Expression.t visit_action

  (** Called when visiting a statement *)
  method visit_stmt : Statement.t -> Statement.t visit_action

  (** Called when visiting a value *)
  method visit_value : Value.t -> Value.t visit_action

  (** Called when visiting a referenced variable. See also {!visit_avar}. *)
  method visit_rvar : Variable.t -> Variable.t visit_action

  (** Called when visiting an assigned variable.
      Note that in a Move(), referenced variables will be visited first, so
      that this can be used to add the assigned variable to your context.
  *)
  method visit_avar : Variable.t -> Variable.t visit_action
end

class nop : t = object
  (* Default direction is top to bottom *)
  method get_direction = TopToBottom
  method visit_exp _   = DoChildren
  method visit_value _ = DoChildren
  method visit_stmt _  = DoChildren
  method visit_avar _  = DoChildren
  method visit_rvar _  = DoChildren
end

class rnop : t = object
  method get_direction = BottomToTop
  method visit_exp _   = DoParent
  method visit_value _ = DoParent
  method visit_stmt _  = DoParent
  method visit_avar _  = DoParent
  method visit_rvar _  = DoParent
end

let rec action direction vischil startvisit node =
  match direction with
  | TopToBottom ->
    (match startvisit node with
    | SkipChildren -> node
    | ChangeTo x -> x (* FIXME: warn if x = node *)
    | DoChildren -> vischil node
    | ChangeToAndDoChildren x -> vischil x
    | DoParent -> failwith "Unable to handle DoParent when visiting top-down")
  | BottomToTop ->
    let new_node = (vischil node) in
    (match startvisit new_node  with
    | SkipChildren -> failwith "Unable to handle SkipChildren when visiting bottom-up"
    | ChangeTo x -> x (* FIXME: warn if x = node *)
    | DoChildren -> failwith "Unable to handle Dochildren when visiting bottom-up"
    | ChangeToAndDoChildren _ -> failwith "Unable to handle ChangeToAndDoChildren when visiting bottom-up"
    | DoParent -> new_node)

let wrapstmt f v = let v' = f v in if quick_stmt_eq v v' then v else v'
let wrapexp f v = let v' = f v in if quick_exp_eq v v' then v else v'
let wrapval f v = let v' = f v in if quick_value_eq v v' then v else v'

let id x = x

let rec exp_accept visitor = 
  let vischil = function
    | Expression.Ite(cond, v1, v2) ->
    let vc' = value_accept visitor cond in 
    let v1' = value_accept visitor v1 in 
    let v2' = value_accept visitor v2 in 
    Expression.Ite(vc', v1', v2')
    | Expression.Extract(h, l, v) ->
    let v' = value_accept visitor v in
    Expression.Extract(h, l, v')
    | Expression.Concat(lv, rv) ->
    let lv' = value_accept visitor lv in
    let rv' = value_accept visitor rv in
    Expression.Concat(lv', rv')
    | Expression.BinOp(bop, v1, v2) -> 
    let v1' = value_accept visitor v1 in 
    let v2' = value_accept visitor v2 in 
    Expression.BinOp(bop, v1', v2')
    | Expression.UnOp(up, v) -> 
    let v' = value_accept visitor v in 
    Expression.UnOp(up, v')
    | Expression.Val(v) -> 
    let v' = value_accept visitor v in 
    Expression.Val(v')
    | Expression.Cast(ct, t, v) ->
    let v' = value_accept visitor v in 
    Expression.Cast(ct,t,v')
    | Expression.Unknown _ as exp -> exp
    | Expression.Load(v1, v2, v3, t, attrs) -> 
    let v1' = value_accept visitor v1 in 
    let v2' = value_accept visitor v2 in 
    let v3' = value_accept visitor v3 in 
    Expression.Load(v1',v2',v3',t,attrs)
    | Expression.Store(v1,v2,v3,v4,t,attrs) ->
    let v1' = value_accept visitor v1 in 
    let v2' = value_accept visitor v2 in 
    let v3' = value_accept visitor v3 in 
    let v4' = value_accept visitor v4 in 
    Expression.Store(v1',v2',v3',v4',t,attrs)
    | Expression.Phi(vl) ->
    let vl' = List.map (rvar_accept visitor) vl in  
    Expression.Phi(vl')
  in
  action (visitor#get_direction) (wrapexp vischil) (visitor#visit_exp)


and avar_accept visitor =
  action (visitor#get_direction) id (visitor#visit_avar)
and rvar_accept visitor = 
  action (visitor#get_direction) id (visitor#visit_rvar)

and value_accept visitor =
  let vischil = function
    | Value.Var var -> ( match var with 
        | Variable.Var (v,attrs) as v' -> Value.Var (rvar_accept visitor v')
        (* Variable expression are transient and not visited by the visitor. *)
        | Variable.VarExp (v,e,attrs) -> Value.Var (Variable.VarExp(v,exp_accept visitor e,attrs)))
    | v -> v
  in
  action (visitor#get_direction) (wrapval vischil) (visitor#visit_value)

and stmt_accept visitor = 
  let vischil = function 
      (* TODO: attributes? *)
    | Statement.Jmp(l, a) -> Statement.Jmp(value_accept visitor l, a) 
    | Statement.CJmp(c, l1, l2, a) -> 
    let c' = value_accept visitor c in
    let l1' = value_accept visitor l1 in
    let l2' = value_accept visitor l2 in
    Statement.CJmp(c', l1', l2', a)
    | Statement.Move(lv, e, a) ->
    let e = exp_accept visitor e in
    let lv = avar_accept visitor lv in
    Statement.Move(lv, e, a)
    | Statement.Label _ as s -> s
    | Statement.Comment _ as s-> s
    | Statement.Assert(e,a) -> Statement.Assert(value_accept visitor e, a)
    | Statement.Halt(e,a) -> Statement.Halt(value_accept visitor e, a)
  in
  action (visitor#get_direction) (wrapstmt vischil) (visitor#visit_stmt)

let stmts_accept vis stmts =
  List.map (stmt_accept vis) stmts

(* vim: set ts=2 sw=2 tw=80 et :*)
