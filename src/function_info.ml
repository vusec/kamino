module D = Debug.Make(struct let name = "Function_info" and default=`Debug end)
open D

open Interval
open Func_attr

module Function_info =
struct

  module Function =
  struct
    type t = {
      symbols: string BatSet.t;
      interval: Function_interval.t;
      unmodified_ast: Ast.stmt list;
      ast: Ast.stmt list;
      astcfg: Cfg.AST.G.t option ref;
      ssacfg: Cfg.SSA.G.t option ref;
      attrs: FuncAttrSet.t;
    }

    let create sym interval stmts =
      let attrs = match Symbols.sym_has_attrs sym with
        | Some attrs -> attrs
        | None -> FuncAttrSet.empty
      in
      {
        symbols = BatSet.singleton sym;
        interval;
        unmodified_ast = stmts;
        ast = [];
        astcfg = ref None;
        ssacfg = ref None;
        attrs = attrs;
      }
    let add_alias f sym = {f with symbols = BatSet.add sym f.symbols}
    let symbols {symbols} = BatList.of_enum (BatSet.enum symbols)
    let symbols_to_str f =
      let syms = symbols f in
      Print.list_to_string ~enclosing:("", "") ~sep:"|" (fun x -> x) syms

    let begin_address {interval} = Function_interval.begin_ interval
    let end_address {interval} = Function_interval.end_ interval

    let to_string f =
      let symstr = Print.enum_to_string ~enclosing:("", "") ~sep:"|"
          (fun x -> x) (BatSet.enum f.symbols)
      in
      let addrstr = BatOption.map_default (Printf.sprintf "%#Lx") "n/a" in
      let baddr = addrstr (begin_address f) in
      let eaddr = addrstr (end_address f) in
      Printf.sprintf "[D] %s [%s-%s] %s" symstr baddr eaddr
        (Func_attr.fattrs_to_string f.attrs)

    let stmts {unmodified_ast; ast} =
      if BatList.is_empty ast then unmodified_ast
      else ast
    let unmodified_stmts {unmodified_ast} = unmodified_ast
    let set_stmts f ast = {f with ast = ast}
    let attrs f = f.attrs
    let set_attrs f attrs = {f with attrs = attrs}
    let has_attr f attr = FuncAttrSet.mem attr f.attrs

    let astcfg f = match !(f.astcfg) with
      | Some cfg -> cfg
      | None ->
        let cfg = Cfg_ast.of_prog (stmts f) in
        f.astcfg := Some cfg;
        cfg
    let set_astcfg f astcfg = match !(f.astcfg) with
      | Some _ ->
        assert(!(f.ssacfg) = None);
        f.astcfg := Some astcfg;
        f
      (*
       * We don't want the callers to be doing the ast -> astcfg conversion
       * manually. Or, at the very least, we want to know if this starts
       * happening.
       *)
      | None ->
        failwith "Manual astcfg conversion detected. I can't let you do that, Dave."
    let ssacfg f = match !(f.ssacfg) with
      | Some cfg -> cfg
      | None ->
        let cnt_to_str (minor, promoted, major) =
          Printf.sprintf "(min %f, prom %f, maj %f)" (4.0 *. minor) (4.0 *. promoted) (4.0 *. major)
        in
        let cntdiff (aminor, apromoted, amajor) (bminor, bpromoted, bmajor) =
          (aminor -. bminor, apromoted -. bpromoted, amajor -. bmajor)
        in
        Gc.full_major ();
        let cnt_before = Gc.counters () in
        let cfg = Cfg_ssa.of_astcfg (astcfg f) in
        f.ssacfg := Some cfg;
        Gc.full_major ();
        let cnt_after = Gc.counters () in
        dprintf "%s: Heap expansion (%s -> %s): %s [bytes]\n" (to_string f)
          (cnt_to_str cnt_before) (cnt_to_str cnt_after) (cnt_to_str (cntdiff cnt_after cnt_before));
        cfg
    let set_ssacfg f ssacfg = match !(f.ssacfg) with
      | Some _ ->
        f.ssacfg := Some ssacfg;
        f
      (*
       * We don't want the callers to be doing the ast -> ssa conversion
       * manually. Or, at the very least, we want to know if this starts
       * happening.
       *)
      | None ->
        failwith "Manual SSA conversion detected. I can't let you do that, Dave."
    let inval_ssacfg f =
      f.ssacfg := None;
      f
  end

  module ExternalFunction =
  struct
    type t = {
      symbol: string;
      offset: Type.addr;
      attrs: FuncAttrSet.t
    }

    let create sym offset =
      let attrs = match Symbols.sym_has_attrs sym with
        | Some attrs -> attrs
        | None -> FuncAttrSet.empty
      in
      {
        symbol = sym;
        offset;
        attrs;
      }

    let symbol {symbol} = symbol
    let offset {offset} = offset
    let attrs f = f.attrs
    let set_attrs f attrs = {f with attrs = attrs}
    let to_string f = Printf.sprintf "[E] %s [%#Lx] %s" f.symbol f.offset
        (Func_attr.fattrs_to_string f.attrs)
  end

  type t =
      Function of Function.t
    | ExternalFunction of ExternalFunction.t
    | Indirect
    | Unknown of Type.addr

  let create sym interval stmts = Function (Function.create sym interval stmts)
  let create_external sym offset = ExternalFunction (ExternalFunction.create sym offset)
  let create_indirect = Indirect
  let create_unknown addr = Unknown addr

  let symbols = function
    | Function f -> Function.symbols f
    | ExternalFunction f -> [ExternalFunction.symbol f]
    | Indirect -> []
    | Unknown _ -> [] (* XXX: option? *)

  let symbols_to_str f =
    let syms = symbols f in
    Print.list_to_string ~enclosing:("", "") ~sep:"|" (fun x -> x) syms

  let begin_address = function
    | Function f -> Function.begin_address f
    | ExternalFunction f -> Some (ExternalFunction.offset f)
    | Indirect -> None
    | Unknown addr -> Some addr

  let stmts = function
    | Function f -> Some (Function.stmts f)
    | ExternalFunction _ -> None
    | Indirect -> None
    | Unknown _ -> None

  let unmodified_stmts = function
    | Function f -> Function.unmodified_stmts f
    | ExternalFunction _ -> raise Not_found
    | Indirect -> raise Not_found
    | Unknown _ -> raise Not_found

  let set_stmts f stmts = match f with
    | Function f -> Function (Function.set_stmts f stmts)
    | ExternalFunction _ | Indirect | Unknown _ ->
      failwith "Unable to set statements!"

  let has_attr f attr = match f with
    | Function f -> FuncAttrSet.mem attr (Function.attrs f)
    | ExternalFunction f -> FuncAttrSet.mem attr (ExternalFunction.attrs f)
    | Indirect -> failwith "has_attr called on Indirect"
    | Unknown addr -> failwith (Printf.sprintf "has_attr on Unknown %#Lx" addr)

  let attrs f = match f with
    | Function f -> Function.attrs f
    | ExternalFunction f -> ExternalFunction.attrs f
    | _ -> failwith "No attrs available"

  let set_attr f attr = match f with
    | Function f ->
      let nattrs = FuncAttrSet.add attr (Function.attrs f) in
      Function (Function.set_attrs f nattrs)
    | ExternalFunction f ->
      let nattrs = FuncAttrSet.add attr (ExternalFunction.attrs f) in
      ExternalFunction (ExternalFunction.set_attrs f nattrs)
    | _ -> failwith "Can't set attr"

  let astcfg = function
    | Function f -> Some (Function.astcfg f)
    | _ -> None

  let set_astcfg f astcfg = match f with
    | Function f -> Function (Function.set_astcfg f astcfg)
    | _ -> failwith "Tried to set_astcfg to !Function"

  let ssacfg = function
    | Function f -> Some (Function.ssacfg f)
    | _ -> None

  let set_ssacfg f ssacfg = match f with
    | Function f -> Function (Function.set_ssacfg f ssacfg)
    | _ -> failwith "Tried to set_ssacfg to !Function"

  let inval_ssacfg f = match f with
    | Function f -> Function (Function.inval_ssacfg f)
    | _ -> failwith "Tried inval_ssacfg to !Function"

  let to_string f = match f with
    | Function f -> Function.to_string f
    | ExternalFunction f -> ExternalFunction.to_string f
    | Indirect -> "[I] Indirect"
    | Unknown addr -> Printf.sprintf "[U] unknown_func_%#Lx" addr

  module HashedType =
    struct
      (*
       * Observable functions are compared by address, as the names of
       * the functions need not be unique in a binary. In fact, when
       * we force an out-of-line copy of an inlined function to be emitted,
       * such a copy is emitted once for every compilation unit where
       * a given function is inlined.
       * For other kinds of functions, names are enough. Note: even though
       * two external functions might have the same name (whether in the
       * same or different .so files), the name we generate for them
       * includes the address of their PLT entry (indeed, in C, when
       * function addresses are compared, it's the address of the PLT entry
       * that's compared). So using the name is safe.
       *)
      let equal f1 f2 =
        match (f1, f2) with
        | Function f1, Function f2 ->
          begin
            match (Function.begin_address f1, Function.begin_address f2) with
            | Some addr1, Some addr2 -> 0 = Int64.compare addr1 addr2
            | _ -> failwith "Function without an address!"
          end
        | Function _, _
        | _, Function _ ->
          false
        | ExternalFunction f1, ExternalFunction f2 ->
          0 = Int64.compare (ExternalFunction.offset f1) (ExternalFunction.offset f2)
        | ExternalFunction _, _
        | _, ExternalFunction _ ->
          false
        | Indirect, Indirect ->
          true
        | Indirect, _
        | _, Indirect ->
          false
        | Unknown addr1, Unknown addr2 ->
          0 = Int64.compare addr1 addr2
      let hash t =
        let key = match t with
          | Function f ->
            begin
              match Function.begin_address f with
              | Some addr -> addr
              | None ->
                let str = Printf.sprintf "function without an address: %s"
                    (to_string t) in
                failwith str
            end
          | ExternalFunction f -> ExternalFunction.offset f
          | Indirect -> Int64.zero
          | Unknown addr -> addr
        in
        Hashtbl.hash key
    end

  include HashedType
end

include Function_info

module Hashtbl = struct
  include BatHashtbl.Make(Function_info)
  (*
   * In batteries 1.4.3, the find_option of BatHashtbl.Make
   * uses the polymorphic find_option which, obviously,
   * uses the polymorphic '='. However, find will use our
   * compare as it should. So here we need to override
   * find_option so that Function_info.HashedType.compare
   * will be used instead.
   *)
  let find_option t key =
    try
      Some (find t key)
    with Not_found -> None
end
