module D = Debug.Make(struct let name = "Callgraph" and default=`Debug end)
open D
open Interval

type call_target = DirectCall of Type.addr * Type.addr | IndirectCall of Type.addr

let callsite = function
  | DirectCall (addr, _)
  | IndirectCall addr -> addr

let cmp_by_call_site a b =
  Int64.compare (callsite a) (callsite b)

let sexp_of_call_target ct =
  let open Sexplib in
  let sexp_of_addr addr = Sexp.Atom (Printf.sprintf "%#Lx" addr) in
  match ct with
  | DirectCall (site, target) ->
    Sexp.List [Sexp.Atom "DC"; sexp_of_addr site; sexp_of_addr target;]
  | IndirectCall site ->
    Sexp.List [Sexp.Atom "IC"; sexp_of_addr site;]

let call_targets stmts =
  let open Big_int_convenience in
  let rec call_target_from_addr_exp call_site = function
    | Ast.Int (addr, _) -> DirectCall (call_site, Big_int_Z.int64_of_big_int addr)
    (* Every other expresson is considered an indirect address*)
    | _ -> IndirectCall call_site
  in
  let call_target_from_jmp call_site = function
    | Ast.Jmp (exp, _) -> call_target_from_addr_exp call_site exp
    | _ -> failwith "Unexpected AST statement, expected a Jmp!"
  in
  let visitor = object
    inherit Ast_visitor.nop

    val mutable call_site = Int64.zero
    val mutable call_targets = []

    method get_call_targets = call_targets

    method visit_stmt = function
      | Ast.Label (Type.Addr addr, _) ->
        call_site <- addr;
        Type.SkipChildren
      | Ast.Jmp _ as jmp when (Misc.is_call Asmir.arch_i386 jmp) ->
        if not (Misc.call_is_getpc Asmir.arch_i386 call_site jmp)
        then call_targets <- (call_target_from_jmp call_site jmp) :: call_targets
        else ();
        Type.SkipChildren
      | _ -> Type.SkipChildren
  end
  in
  let () = ignore(Ast_visitor.prog_accept visitor stmts)
  in
  visitor#get_call_targets

let call_sites call_targets = List.map (function
  | DirectCall (cs, _) -> cs
  | IndirectCall cs ->cs) call_targets

module FunctionInfoVertex = struct
  type t = Function_info.t
  let compare v1 v2 =
    compare (Function_info.to_string v1) (Function_info.to_string v2)
  include Function_info.HashedType
end

type call = {
  call_site : Type.addr;
  stack_height : Type.addr option; (* Cannot always compute the stack height *)
}
module Edge = struct
  type t = call
  let compare e1 e2 = Int64.compare e1.call_site e2.call_site
  let default = {call_site = Int64.zero; stack_height = None}
  let to_string {call_site; stack_height} =
    let sh = match stack_height with
      | None -> "n/a"
      | Some h -> Printf.sprintf "%Ld" h
    in
    Printf.sprintf "%#Lx (SH: %s)" call_site sh
end

module Callgraph = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(FunctionInfoVertex)(Edge)

let generate_singular_callgraph func =
  let g = Callgraph.empty in
  Callgraph.add_vertex g func

let generate_call_graph unknown_function_resolver functions =
  let callgraph = Callgraph.empty in
  let addr_to_func addr =
    let address_to_function_mapping =
      List.fold_left (fun tbl func ->
          match Function_info.begin_address func with
          | Some addr ->
            dprintf "address_to_function_mapping: %#Lx -> %s" addr (Function_info.to_string func);
            Hashtbl.add tbl addr func;
            tbl
          | None -> tbl
    ) (Hashtbl.create (List.length functions)) functions
    in
    try
      Hashtbl.find address_to_function_mapping addr
    with Not_found ->
      dprintf "Unknown function at %#Lx, trying to resolve." addr;
      if Int64.compare addr Int64.zero = 0 then begin
        (*
         * This mostly happens in frame_dummy, but it could legitimately
         * occur in real code too (either intending to segfault or having
         * mmapped code at address 0 or ... being buggy). In any case,
         * it seems safe to have an unknown function here. If we allow
         * this address to go into the plt resolver, we'll end up with
         * an Asmir.Memory_error for reeasons that I haven't investigated
         * yet. -- agg
         *)
        Function_info.create_unknown addr
      end else begin
        match unknown_function_resolver addr with
        | Some func ->
          dprintf "Resolved unknown function to %s" (Function_info.to_string func);
          Hashtbl.add address_to_function_mapping addr func;
          func
        | None ->
          Function_info.create_unknown addr
      end
  in
  (* Initialize the graph with all the functions and an indirect node*)
  let indirect_node = Function_info.create_indirect
  in
  let callgraph = List.fold_left (fun g f ->
      dprintf "Adding %s" (Function_info.to_string f);
      Callgraph.add_vertex g f) callgraph (indirect_node :: functions)
  in
  List.fold_left (fun graph f ->
    let calls = call_targets (BatOption.get (Function_info.stmts f)) in
    (*
     * Note: setting the callsites needs to happen after the astcfg conversion
     * *through the pipeline*, otherwise we still have BB_Indirect etc
     *)
    List.fold_left (fun g call -> match call with
    | DirectCall (call_site, call_target) ->
      let resolved_target = addr_to_func call_target in
      dprintf "Adding edge %s --%Lx-> %s" (Function_info.to_string f)
        call_site (Function_info.to_string resolved_target);
      Callgraph.add_edge_e g
        (f, {call_site; stack_height = None}, resolved_target)
    | IndirectCall call_site ->
      dprintf "Adding edge %s --%Lx-> indirect" (Function_info.to_string f)
        call_site;
      Callgraph.add_edge_e g
        (f, {call_site; stack_height = None}, indirect_node)
        ) graph calls
    ) callgraph functions


module Callgraph_printer =
struct
  include Callgraph
  let default_edge_attributes _ = [`Style `Solid]
  let edge_attributes e = [`Label (Edge.to_string (E.label e))]
  (* The dot language has issues with node names containing a '.', so we replace all
  occurrences with  '_'*)
  let vertex_name v = Str.global_replace (Str.regexp "\\.") "_" (Function_info.symbols_to_str v)
  let default_vertex_attributes _ = [`Shape `Box]
  let vertex_attributes _ = [`Shape `Box]
  let graph_attributes _ = [`Orientation `Landscape]
  let get_subgraph _ = None
end
module Callgraph_dot = Graph.Graphviz.Dot(Callgraph_printer)

let dump_call_graph g oc =
  Callgraph_dot.output_graph oc g

let traverse_from_callee_to_callers g f =
  let module T = Graph.Traverse.Dfs(Callgraph) in
  if T.has_cycle g then failwith "Recursive calls not supported!"
  else T.postfix f g

let add_out_node cg =
  let out_node = Function_info.create "out_node"
    (Interval.Function_interval.create Int64.zero Int64.zero) []
  in
  let astcfg = match Function_info.astcfg out_node with
    | None -> failwith "No astcfg??"
    | Some c -> c
  in
  let astcfg = Hacks.ast_remove_indirect astcfg in
  let out_node = Function_info.set_astcfg out_node astcfg in
  let out_node = Function_info.set_attr out_node Func_attr.WellBehaved in
  let leaves = Callgraph.fold_vertex (fun fi acc ->
    match Callgraph.out_degree cg fi with
    | 0 -> fi :: acc
    | _ -> acc) cg []
  in
  let cg = List.fold_left (fun ncg leaf ->
    Callgraph.add_edge_e ncg
      (leaf,
       {
         call_site = Int64.zero;
         stack_height = None;
       },
       out_node)) cg leaves
  in
  (cg, out_node)
