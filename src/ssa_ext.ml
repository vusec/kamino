(**
Extended Single Static Assignment Form
@author: Remco Vermeulen
*)

module D = Debug.Make(struct let name = "Ssa_ext" and default=`NoDebug end)
open D

module VC = Var_convenience
module VH = VC.VH
module VS = VC.VS

let dot_escape s =
  let open BatPervasives in
   String.escaped (Str.global_replace (Str.regexp "-") "_" s)

module RuntimeInformation : sig
    type t = (Big_int_Z.big_int * Type.typ * Type.taint_type)
end =
struct
    type t = (Big_int_Z.big_int * Type.typ * Type.taint_type)
end

type decoration = Rti | NamedNodes | StopAtStore
let with_rti = List.mem Rti
let with_namednodes = List.mem NamedNodes
let with_stop_at_store = List.mem StopAtStore

let int_to_str i t =
    let is = Arithmetic.to_sbig_int (i,t)
    in
    match (is, t) with
    | (bi, Type.Reg 1) when Big_int_convenience.bi_is_zero bi -> "false"
    | (bi, Type.Reg 1) when Big_int_convenience.bi_is_minusone bi -> "true"
    | (bi, t) ->
            if Big_int_convenience.(<%) (Big_int_Z.abs_big_int bi) Big_int_convenience.bia
            then (Big_int_Z.string_of_big_int bi) ^ (Pp.typ_to_string t)
            else "0x" ^ (Util.big_int_to_hex (Arithmetic.to_big_int (i,t)))
            ^ ":" ^(Pp.typ_to_string t)

let rti_to_str = function
    | [] -> ""
    | l ->
        let pp = function (value, typ, taint) -> Printf.sprintf "%s<%s>"
        (int_to_str value typ) (Pp.taint_to_string taint)
        in
        Print.list_to_string ~enclosing:("{","}") pp l

module rec Attribute : sig
    type t = Attr of Type.attribute | Rti of RuntimeInformation.t
    val rti_from : t -> RuntimeInformation.t option
    val rti_from_attrs : t list -> RuntimeInformation.t list
end =
struct
    type t = Attr of Type.attribute | Rti of RuntimeInformation.t
    let rti_from = function
      | Attr _ -> None
      | Rti rti -> Some rti
    and rti_from_attrs attrs =
      List.rev (List.fold_left ( fun acc attr -> match attr with
      | Rti rti -> rti :: acc
      | _ -> acc) [] attrs)

end
and Variable : sig
    type t = Var of Var.t * Attribute.t list | VarExp of Var.t * Expression.t * Attribute.t list

    val sexp_of_t : t -> Sexplib.Sexp.t
    val to_string : ?decorators:decoration list -> ?breaks:bool -> t -> string
    val to_dot : out_channel -> string -> ?parent:string option -> ?serial:int -> t -> unit
    val pp : Format.formatter -> ?decorators:decoration list -> ?breaks:bool -> t -> unit
    val hash : t -> int

    val equal : t -> t -> bool

    val compare : t -> t -> int
    val name : t -> string
end
= struct
    type t = Var of Var.t * Attribute.t list | VarExp of Var.t * Expression.t * Attribute.t list

    let rti_from_var = function
      | Var (_,attrs)
      | VarExp (_,_,attrs) ->
        List.map BatOption.get (List.filter BatOption.is_some (List.map Attribute.rti_from attrs))

    let pp ft ?(decorators=[NamedNodes]) ?(breaks=true) var =
      let rti_str =
        if with_rti decorators
        then
          let rti = rti_from_var var in
          rti_to_str rti
        else " "
      in
      match var with
      | Variable.Var (var, attrs) ->
        let s = Pp.var_to_string var in
        Format.fprintf ft "%s%s" s rti_str
      | Variable.VarExp (var,exp,attrs) ->
	if breaks then
	  Format.pp_open_vbox ft 2
	else
	  Format.pp_open_hbox ft ();
	if with_namednodes decorators then begin
	  Format.fprintf ft "{<%s>%s= " (Pp.var_to_string var) rti_str;
	  Expression.pp ft ~decorators ~breaks exp;
	  Format.pp_print_string ft "}"
        end else begin
	  Expression.pp ft ~decorators ~breaks exp;
	end;
	Format.pp_close_box ft ()

    let sexp_of_t = function
      | Var (var, _) -> Sexplib.Sexp.of_string (String.escaped (Var.name var))
      | VarExp (var, exp, _) -> Expression.sexp_of_t exp

    let to_string ?(decorators=[NamedNodes]) ?(breaks=true) var =
      let buf = Buffer.create 40 in
      let ft = Format.formatter_of_buffer buf in
      ignore(pp ft ~decorators ~breaks var);
      Format.pp_print_flush ft ();
      Buffer.contents buf

    let name = function
      | Var (v, _)
      | VarExp (v, _, _) -> Pp.var_to_string v

    let to_dot oc pref ?(parent=None) ?(serial=0) var =
      let do_edge me =
        match parent with
        | Some p -> Printf.fprintf oc "%s -> %s [];\n" p me
        | None -> ()
      in
      let (node, exp) = match var with
      | Var (_, _) -> ("Var", None)
      | VarExp (_, exp, _) -> ("VarExp", Some exp)
      in
      let node = Printf.sprintf "%s_%s_%d" pref node serial in
      let vn = dot_escape (name var) in
      Printf.fprintf oc "%s [label=\"%s\"];\n" node vn;
      do_edge node;
      match exp with
      | None -> ()
      | Some e -> Expression.to_dot oc pref ~parent:(Some node) ~serial:(serial + 1) e

    let hash = function
        | Var (Var.V (i,_,_), _) -> i
        | VarExp (Var.V (i,_,_), _, _) -> i

    (*
        By default we say that two keys are equal if they have the same 'inner' var
        This means we ignore attributes and allows use to compare the variable
        'instances' where the variables are same, but one has attributes of both
        have different attributes.
    *)
    let equal x y = (Variable.compare x y) = 0

    let compare x y =
      String.compare (to_string ~decorators:[NamedNodes] x) (to_string ~decorators:[NamedNodes] y)
end
and
Value : sig
    type t =
        | Int of Big_int_Z.big_int * Type.typ
        | Var of Variable.t
        | Lab of string

    val pp : Format.formatter -> ?decorators:decoration list -> ?breaks:bool -> t -> unit
    val sexp_of_t: t -> Sexplib.Sexp.t
    val to_string : ?decorators:decoration list -> ?breaks:bool -> t -> string
    val to_dot : out_channel -> string -> ?parent:string option -> ?serial:int -> t -> unit
    val compare : t -> t -> int
end
= struct
    type t =
        | Int of Big_int_Z.big_int * Type.typ
        | Var of Variable.t
        | Lab of string

    let pp ft ?(decorators=[]) ?(breaks=true) v = match v with
      | Int(i,t) -> Format.pp_print_string ft (int_to_str i t)
      | Var v' -> Variable.pp ft ~decorators ~breaks v'
      | Lab lab -> Format.fprintf ft "\"%s\"" lab

    let sexp_of_t v =
      let open Sexplib in
      match v with
      | Int (bi, typ) ->
        let buf = Buffer.create 40 in
        let ft = Format.formatter_of_buffer buf in
        ignore(Format.pp_print_string ft (int_to_str bi typ));
        Format.pp_print_flush ft ();
        Sexp.of_string (Buffer.contents buf)

      | Var v -> Variable.sexp_of_t v
      | Lab lab -> Sexp.List [Sexp.Atom "Label"; Sexp.Atom (String.escaped lab);]

    let to_string ?(decorators=[]) ?(breaks=true) v =
      let buf = Buffer.create 40 in
      let ft = Format.formatter_of_buffer buf in
      ignore(pp ft ~decorators ~breaks v);
      Format.pp_print_flush ft ();
      Buffer.contents buf

    let to_dot oc pref ?(parent=None) ?(serial=0) value =
      let do_edge me =
        match parent with
        | Some p -> Printf.fprintf oc "%s -> %s [];\n" p me
        | None -> ()
      in
      let (node, var) = match value with
        | Int _ -> (to_string ~breaks:false value, None)
        | Var v -> ("Var", Some v)
        | Lab _ -> (to_string ~breaks:false value, None)
      in
      let disp = dot_escape node in
      let node = Printf.sprintf "%s_%s_%d" pref disp serial in
      Printf.fprintf oc "%s [label=\"%s\"];\n" node disp;
      do_edge node;
      match var with
      | None -> ()
      | Some v ->
        Variable.to_dot oc pref ~parent:(Some node) ~serial:(serial + 1) v

    let compare = Pervasives.compare
end
and
Expression : sig
    type t =
        | Load of Value.t * Value.t * Value.t * Type.typ * Attribute.t list
        | Store of Value.t * Value.t * Value.t * Value.t * Type.typ * Attribute.t list
        | Ite of Value.t * Value.t * Value.t
        | Extract of Big_int_Z.big_int * Big_int_Z.big_int * Value.t
        | Concat of Value.t * Value.t
        | BinOp of Type.binop_type * Value.t * Value.t
        | UnOp of Type.unop_type * Value.t
        | Val of Value.t
        | Cast of Type.cast_type * Type.typ * Value.t
        | Unknown of string * Type.typ
        | Phi of Variable.t list

    val pp : Format.formatter -> ?decorators:decoration list -> ?breaks:bool -> t -> unit
    val sexp_of_t : t -> Sexplib.Sexp.t
    val to_string : ?decorators:decoration list -> ?breaks:bool -> t -> string
    val to_dot : out_channel -> string -> ?parent:string option -> ?serial:int -> t -> unit
    val getargs : t -> Value.t list * Type.typ list * Type.binop_type list *
      Type.unop_type list * string list * Type.cast_type list *
      Variable.t list * Big_int_Z.big_int list * Attribute.t list list
    val hash : t -> int
    val equal: t -> t -> bool
    val is_loadstore: t -> bool
end
= struct
    type t =
        | Load of Value.t * Value.t * Value.t * Type.typ * Attribute.t list
        | Store of Value.t * Value.t * Value.t * Value.t * Type.typ * Attribute.t list
        | Ite of Value.t * Value.t * Value.t
        | Extract of Big_int_Z.big_int * Big_int_Z.big_int * Value.t
        | Concat of Value.t * Value.t
        | BinOp of Type.binop_type * Value.t * Value.t
        | UnOp of Type.unop_type * Value.t
        | Val of Value.t
        | Cast of Type.cast_type * Type.typ * Value.t
        | Unknown of string * Type.typ
        | Phi of Variable.t list

    let rec edn_to_str = function
      | Value.Int(bi, Type.Reg 1) when Big_int_convenience.bi_is_zero bi -> "e_little"
      | Value.Int(bi, Type.Reg 1) when Big_int_convenience.bi_is_one bi -> "e_big"
      | x -> Value.to_string x
    and pp ft ?(decorators=[]) ?(breaks=true) exp =
      let nl () =
	if breaks then
	  Format.pp_force_newline ft ()
      in
      match exp with
      | Expression.Load(arr,idx,edn,typ,attrs) ->
        let rti = Attribute.rti_from_attrs attrs in
	Format.fprintf ft "@[";
        Value.pp ft ~decorators ~breaks arr;
	Format.pp_print_string ft (rti_to_str rti);
	Format.pp_print_string ft "[";
	Value.pp ft ~decorators ~breaks idx;
	Format.pp_print_string ft ", ";
	Format.fprintf ft "%s]:%s" (edn_to_str edn) (Pp.typ_to_string typ)
     | Expression.Store(arr,idx,v,edn,typ,attrs) ->
       Format.pp_open_hovbox ft 2;
       Value.pp ft ~decorators ~breaks arr;
       Format.pp_print_string ft " with [";
       Value.pp ft ~decorators ~breaks idx;
       Format.fprintf ft ", %s]:%s" (edn_to_str edn) (Pp.typ_to_string typ);
       if not (with_stop_at_store decorators) then begin
         Format.pp_print_space ft ();
         Format.pp_print_string ft "=";
         Format.pp_print_space ft ();
         Value.pp ft ~decorators ~breaks v;
         Format.pp_close_box ft ()
       end
     | Expression.Ite(c, x, y) ->
       Format.pp_print_string ft "if ";
       Value.pp ft ~decorators ~breaks c;
       Format.pp_print_string ft " then ";
       Value.pp ft ~decorators ~breaks x;
       Format.pp_print_string ft " else ";
       Value.pp ft ~decorators ~breaks y;
     | Expression.Extract(h, l, e) ->
       Format.fprintf ft "extract:%s:%s:["
	 (Big_int_Z.string_of_big_int h)
	 (Big_int_Z.string_of_big_int l);
       Value.pp ft ~decorators ~breaks e;
       Format.pp_print_string ft "]"
     | Expression.Concat(lv, rv) ->
       Format.pp_print_string ft "concat:[";
       Value.pp ft ~decorators ~breaks lv;
       Format.pp_print_string ft "][";
       Value.pp ft ~decorators ~breaks rv;
       Format.pp_print_string ft "]";
     | Expression.BinOp(b, x, y) ->
       Format.pp_open_vbox ft 2;
       Format.pp_print_string ft "(";
       nl ();
       Format.pp_print_string ft "  ";
       Value.pp ft ~decorators ~breaks x;
       nl ();
       Format.fprintf ft "%s" (Pp.binop_to_string b);
       nl ();
       Format.pp_print_string ft "  ";
       Value.pp ft ~decorators ~breaks y;
       Format.pp_print_string ft ")";
       Format.pp_close_box ft ()
     | Expression.UnOp(u, x) ->
       Format.fprintf ft "(%s" (Pp.unop_to_string u);
       Value.pp ft ~decorators ~breaks x;
       Format.pp_print_string ft ")"
     | Expression.Val v ->
       Value.pp ft ~decorators ~breaks v
     | Expression.Cast(ct,t,v) ->
       Format.fprintf ft "%s:%s(" (Pp.ct_to_string ct) (Pp.typ_to_string t);
       Value.pp ft ~decorators ~breaks v;
       Format.pp_print_string ft ")"
     | Expression.Unknown(s,t) ->
       Format.fprintf ft "unknown \"%s\":%s" s (Pp.typ_to_string t)
     | Expression.Phi [] ->
       Format.pp_print_string ft "(ERROR: Empty phi)"
     | Expression.Phi l ->
       Format.pp_open_vbox ft 2;
       Format.pp_print_string ft "phi(";
       nl ();
       List.iter (fun v ->
	 Variable.pp ft ~decorators ~breaks v;
	 nl ();
       ) l;
       Format.pp_print_string ft ")";
       Format.pp_close_box ft ()
    and to_string ?(decorators=[NamedNodes]) ?(breaks=true) exp =
      let buf = Buffer.create 40 in
      let ft = Format.formatter_of_buffer buf in
      ignore(pp ft ~decorators ~breaks exp);
      Format.pp_print_flush ft ();
      Buffer.contents buf

    let sexp_of_t exp =
      let open Sexplib in
      match exp with
      | Load (ary, idx, _, typ, _) ->
        Sexp.List [
          Sexp.Atom "Ld";
          Value.sexp_of_t ary;
          Value.sexp_of_t idx;
          Sexp.Atom (Pp.typ_to_string typ);]
      | Store (ary, idx, _, _, typ, _) ->
        Sexp.List [
          Sexp.Atom "St";
          Value.sexp_of_t ary;
          Value.sexp_of_t idx;
          Sexp.Atom (Pp.typ_to_string typ);]
      | Ite (c, x, y) ->
        Sexp.List [
          Sexp.Atom "Ite";
          Value.sexp_of_t c;
          Value.sexp_of_t x;
          Value.sexp_of_t y;]
      | Extract (h, l, v) ->
        Sexp.List [
          Sexp.Atom "extract";
          Sexp.Atom (Big_int_Z.string_of_big_int h);
          Sexp.Atom (Big_int_Z.string_of_big_int l);
          Value.sexp_of_t v;]
      | Concat (lv, rv) ->
        Sexp.List [
          Sexp.Atom "concat";
          Value.sexp_of_t lv;
          Value.sexp_of_t rv;]
      | BinOp (op, x, y) ->
        Sexp.List [
          Sexp.Atom (Pp.binop_to_string op);
          Value.sexp_of_t x;
          Value.sexp_of_t y;]
      | UnOp (op, x) ->
        Sexp.List [
          Sexp.Atom (Pp.unop_to_string op);
          Value.sexp_of_t x;]
      | Val v ->
        Value.sexp_of_t v
      | Cast (ct, typ, v) ->
        Sexp.List [
          Sexp.Atom (Pp.ct_to_string ct);
          Sexp.Atom (Pp.typ_to_string typ);
          Value.sexp_of_t v;]
      | Unknown (s, typ) ->
        Sexp.List [
          Sexp.Atom "UNKNOWN";
          Sexp.Atom (Pp.typ_to_string typ);]
      | Phi (vs) ->
        assert (List.length vs > 0);
        let unbox var = Sexp.Atom (String.escaped (Variable.name var)) in
        Std.sexp_of_list unbox vs

    (* Returns vallist, tlist, btlist, utlist, slist, clist, varlist, ilist, * attributes *)
    let getargs = function
      | Expression.Load(e1,e2,e3,t1,attrs) -> [e1;e2;e3], [t1], [], [], [], [], [], [], [attrs]
      | Expression.Store(e1,e2,e3,e4,t1,attrs) ->
        [e1;e2;e3;e4], [t1], [], [], [], [], [], [], [attrs]
      | Expression.Ite(e1,e2,e3) -> [e1;e2;e3], [], [], [], [], [], [], [], []
      | Expression.Extract(i1,i2,e1) -> [e1], [], [], [], [], [], [], [i1;i2], []
      | Expression.Concat(e1,e2) -> [e1;e2], [], [], [], [], [], [], [], []
      | Expression.BinOp(bt,e1,e2) -> [e1;e2], [], [bt], [], [], [], [], [], []
      | Expression.UnOp(ut,e1) -> [e1], [], [], [ut], [], [], [], [], []
      | Expression.Val(v1) -> [v1], [], [], [], [], [], [], [], []
      | Expression.Cast(c1,t1,e1) -> [e1], [t1], [], [], [], [c1], [], [], []
      | Expression.Unknown(s1,t1) -> [], [t1], [], [], [s1], [], [], [], []
      | Expression.Phi(vl1) -> [], [], [], [], [], [], vl1, [], []

    let to_dot oc pref ?(parent=None) ?(serial=0) exp =
      let do_edge me =
        match parent with
        | Some p -> Printf.fprintf oc "%s -> %s [];\n" p me
        | None -> ()
      in
      let (node, lab) = match exp with
        | Expression.Load _ ->
          ("Load", "Load")
        | Expression.Store _ ->
          ("Store", "Store")
        | Expression.Ite _ ->
          ("Ite", "Ite")
        | Expression.Extract _ ->
          ("Extract", "Extract")
        | Expression.Concat _ ->
          ("Concat", "Concat")
        | Expression.BinOp (bt, _, _) ->
          ("BinOp", Pp.binop_to_string bt)
        | Expression.UnOp (ut, _) ->
          ("UnOp", Pp.unop_to_string ut)
        | Expression.Val _ ->
          ("Val", "Val")
        | Expression.Cast (c, t, _) ->
          ("Cast", Printf.sprintf "%s_%s" (Pp.ct_to_string c)
            (Pp.typ_to_string t))
        | Expression.Unknown _ -> failwith "Can't get here"
        | Expression.Phi _ ->
          ("Phi", "Phi")
      in
      let node = Printf.sprintf "%s_%s_%d" pref node serial in
      let lab = dot_escape lab in
      Printf.fprintf oc "%s [label=\"%s\"];\n" node lab;
      do_edge node;
      let vals, _, _, _, _, _, _, _, _ = getargs exp in
      List.iter (fun value ->
        Value.to_dot oc pref ~parent:(Some node) ~serial:(serial + 1) value) vals

    let hash = Hashtbl.hash

    let equal = (==)
    let is_loadstore expr =
      match expr with
      | Expression.Load _ -> true
      | Expression.Store _ -> true
      | _ -> false

end
and
Statement : sig
    type t =
        | Move of Variable.t * Expression.t * Attribute.t  list
        | Jmp of Value.t * Attribute.t list
        | CJmp of Value.t * Value.t * Value.t * Attribute.t list
        | Label of Type.label * Attribute.t list
        | Halt of Value.t * Attribute.t list
        | Assert of Value.t * Attribute.t list
        | Comment of string * Attribute.t list
    val to_string : ?decorators:decoration list -> t -> string
end
= struct
    type t =
        | Move of Variable.t * Expression.t * Attribute.t  list
        | Jmp of Value.t * Attribute.t list
        | CJmp of Value.t * Value.t * Value.t * Attribute.t list
        | Label of Type.label * Attribute.t list
        | Halt of Value.t * Attribute.t list
        | Assert of Value.t * Attribute.t list
        | Comment of string * Attribute.t list
    let to_string ?(decorators=[]) = function
      | Statement.Move (v, e, _) ->
        Printf.sprintf "%s = %s" (Variable.to_string ~decorators v)
	  (Expression.to_string ~decorators e)
      | Statement.Jmp (v,_) ->
        Printf.sprintf "jmp %s" (Value.to_string ~decorators v)
      | Statement.CJmp (i, t, e, _) ->
        Printf.sprintf "cjmp %s, %s, %s" (Value.to_string ~decorators i)
          (Value.to_string ~decorators t) (Value.to_string ~decorators e)
      | Statement.Label (lab, _) -> (match lab with
        | Type.Name s -> Printf.sprintf "label %s" s
        | Type.Addr a -> Printf.sprintf "addr 0x%Lx" a)
      | Statement.Halt (value, _) -> Printf.sprintf "halt %s" (Value.to_string ~decorators value)
      | Statement.Assert (value, _) -> Printf.sprintf "assert %s" (Value.to_string ~decorators value)
      | Statement.Comment (s, _) -> Printf.sprintf "/* %s */" s

end

module VariableHash = BatHashtbl.Make(Variable)
module VariableSet = BatSet.Make(Variable)

module ValueSet = BatSet.Make(Value)

module ExpressionHash = Hashtbl.Make(Expression)

let of_attr attr = Attribute.Attr attr
let of_attrs = List.map (fun attr -> of_attr attr)

let of_val v = match v with
    | Ssa.Int (i, t) -> Value.Int (i, t)
    | Ssa.Var v -> Value.Var (Variable.Var (v, []))
    | Ssa.Lab s -> Value.Lab s

let of_var v = Variable.Var (v, [])

let of_exp exp = match exp with
    | Ssa.Load (arr, idx, endian, t) ->
            Expression.Load ((of_val arr),(of_val idx),(of_val endian), t, [])
    | Ssa.Store (arr, idx, v, endian, t) ->
            Expression.Store ((of_val arr),(of_val idx), (of_val v),(of_val endian), t, [])
    | Ssa.Ite (v1, v2, v3) -> Expression.Ite ((of_val v1), (of_val v2), (of_val v3))
    | Ssa.Extract (i1, i2, v) -> Expression.Extract (i1, i2, (of_val v))
    | Ssa.Concat (v1, v2) -> Expression.Concat ((of_val v1), (of_val v2))
    | Ssa.BinOp (t, v1, v2) -> Expression.BinOp (t, (of_val v1), (of_val v2))
    | Ssa.UnOp (t, v) -> Expression.UnOp (t, (of_val v))
    | Ssa.Val v -> Expression.Val (of_val v)
    | Ssa.Cast (t, t', v) -> Expression.Cast (t, t', (of_val v))
    | Ssa.Unknown (s, t) -> Expression.Unknown (s, t)
    | Ssa.Phi l -> Expression.Phi (List.map of_var l)

let of_stmt = function
  | Ssa.Move (var, exp, attrs) -> Statement.Move (of_var var, of_exp exp, of_attrs attrs)
  | Ssa.Jmp (value, attrs) -> Statement.Jmp (of_val value, of_attrs attrs)
  | Ssa.CJmp (i, t, e, attrs) -> Statement.CJmp (of_val i, of_val t, of_val e, of_attrs attrs)
  | Ssa.Label (lab, attrs) -> Statement.Label (lab, of_attrs attrs)
  | Ssa.Halt (value, attrs) -> Statement.Halt (of_val value, of_attrs attrs)
  | Ssa.Assert (value, attrs) -> Statement.Assert(of_val value, of_attrs attrs)
  | Ssa.Comment (str, attrs) -> Statement.Comment(str, of_attrs attrs)

let of_prog p = List.rev (List.fold_left (fun l s -> (of_stmt s) :: l) [] p)

let full_value_eq v1 v2 = match v1,v2 with
  | Value.Int(i1, t1), Value.Int(i2, t2) -> ( Big_int_convenience.(==%) i1 i2) && (t1 = t2)
  | Value.Int _, _ -> false
  | _, Value.Int _ -> false
  | a, b -> a = b
let quick_value_eq = full_value_eq

let binop_is_commutative = function
  | Type.PLUS
  | Type.TIMES
  | Type.AND
  | Type.OR
  | Type.XOR
  | Type.EQ
  | Type.NEQ ->
    true
  | Type.MINUS
  | Type.DIVIDE
  | Type.SDIVIDE
  | Type.MOD
  | Type.SMOD
  | Type.LSHIFT
  | Type.RSHIFT
  | Type.ARSHIFT
  | Type.LT
  | Type.LE
  | Type.SLT
  | Type.SLE ->
    false

let num_exp = function
  | Expression.Load _ -> 0
  | Expression.Store _ -> 1
  | Expression.Ite _ -> 2
  | Expression.Extract _ -> 3
  | Expression.Concat _ -> 4
  | Expression.BinOp _ -> 5
  | Expression.UnOp _ -> 6
  | Expression.Val _ -> 7
  | Expression.Cast _ -> 8
  | Expression.Unknown _ -> 9
  | Expression.Phi _ -> 10


(** quick_exp_eq e1 e2 returns true if and only if the subexpressions
    in e1 and e2 are *physically* equal. *)
let quick_exp_eq e1 e2 =
  if (num_exp e1) <> (num_exp e2) then false else
    let l1,l2,l3,l4,l5,l6,l7,l8,l9 = Expression.getargs e1 in
    let r1,r2,r3,r4,r5,r6,r7,r8,r9 = Expression.getargs e2 in
    let b1 = List.for_all2 (==) l1 r1 in
    let b2 = List.for_all2 (==) l2 r2 in
    let b3 = List.for_all2 (==) l3 r3 in
    let b4 = List.for_all2 (==) l4 r4 in
    let b5 = List.for_all2 (==) l5 r5 in
    let b6 = List.for_all2 (==) l6 r6 in
    let b7 = List.for_all2 (==) l7 r7 in
    let b8 = List.for_all2 (==) l8 r8 in
    let b9 = List.for_all2 (==) l9 r9 in
    if b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 then
      true else false

(** full_exp_eq e1 e2 returns true if and only if e1 and e2 are
    structurally equivalent. *)
let rec full_exp_eq e1 e2 = e1 = e2

let num_stmt = function
  | Statement.Move _ -> 0
  | Statement.Jmp _ -> 1
  | Statement.CJmp _ -> 2
  | Statement.Label _ -> 3
  | Statement.Halt _ -> 4
  | Statement.Assert _ -> 5
  | Statement.Comment _ -> 6

let getargs_stmt = function
    (* value, var, label, attr, string, exp *)
  | Statement.Move(v,e,a) -> [], [v], [], [a], [], [e]
  | Statement.CJmp(e1,e2,e3,a) -> [e1;e2;e3], [], [], [a], [], []
  | Statement.Label(l,a) -> [], [], [l], [a], [], []
  | Statement.Jmp(e,a)
  | Statement.Halt(e,a)
  | Statement.Assert(e,a) -> [e], [], [], [a], [], []
  | Statement.Comment(s,a) -> [], [], [], [a], [s], []

(** quick_stmt_eq returns true if and only if the subexpressions in e1
    and e2 are *physically* equal. *)
let quick_stmt_eq s1 s2 =
  if (num_stmt s1) <> (num_stmt s2) then false else
    let l1,l2,l3,l4,l5,l6 = getargs_stmt s1 in
    let r1,r2,r3,r4,r5,r6 = getargs_stmt s2 in
    let b1 = List.for_all2 (==) l1 r1 in
    let b2 = List.for_all2 (==) l2 r2 in
    let b3 = List.for_all2 (==) l3 r3 in
    let b4 = List.for_all2 (==) l4 r4 in
    let b5 = List.for_all2 (==) l5 r5 in
    let b6 = List.for_all2 (==) l6 r6 in
    if b1 & b2 & b3 & b4 & b5 & b6 then
      true
    else if b1 & b2 & b3 & b4 & b5 then
      (* s1 and s2 are not physically equal.  But maybe their
     subexpressions are physically equal. *)
      List.for_all2 quick_exp_eq l6 r6
    else
      false

(** full_stmt_eq returns true if and only if e1 and e2 are structurally equivalent. *)
let full_stmt_eq s1 s2 = s1 = s2

let rec value_count_vars value =
  let rec expr_count_vars expr =
    match expr with
    | Expression.Load _
    | Expression.Store _ -> failwith "Can't happen"
    | Expression.Ite (v1, _, _) -> value_count_vars v1
    | Expression.Extract (_, _, v1) -> value_count_vars v1
    | Expression.Concat (v1, v2)
    | Expression.BinOp (_, v1, v2) -> (value_count_vars v1) + (value_count_vars v2)
    | Expression.UnOp (_, v1) -> value_count_vars v1
    | Expression.Val v1 -> value_count_vars v1
    | Expression.Cast (_, _, v1) -> value_count_vars v1
    | Expression.Unknown _ -> failwith "Can't happen"
    | Expression.Phi vs -> List.length vs
  in
  match value with
  | Value.Int _ -> 0
  | Value.Lab _ -> 0
  | Value.Var (Variable.Var _) -> 1
  | Value.Var (Variable.VarExp (_, expr, _)) ->
    expr_count_vars expr
