open Ast
open Big_int_Z
open Big_int_convenience
open Type

open Symbeval_copy

module D = Debug.Make(struct let name = "SymbEvalExt" and default=`Debug end)
open D 

type iostats = {
    undefined_vars : Var.t list;
    updated_vars : (Var.t * varval) list;
    memory_loads : (varval * Ast.exp) list;
    memory_writes : (varval * Ast.exp * Ast.exp) list;
}

let add_undefined_var iostats var = iostats := {!iostats with undefined_vars = var :: !iostats.undefined_vars}
let add_updated_var iostats var value = iostats := {!iostats with updated_vars = (var, value) :: !iostats.updated_vars}
let add_memory_load iostats mem idx = iostats := {!iostats with memory_loads = (mem,idx) :: !iostats.memory_loads}
let add_memory_write iostats mem idx value = iostats := {!iostats with memory_writes = (mem,idx,value) :: !iostats.memory_writes}

let empty_stats = {undefined_vars = []; updated_vars = []; memory_loads = []; memory_writes = []}
let clear_stats iostats = iostats := empty_stats 

module SymbolicWithIODetectionMemoryLookup =
struct
  type t = (varval VH.t * iostats ref)

  let print_values (delta,_) =
    pdebug "contents of variables" ;
    VH.iter
      (fun k v ->
  	 match k,v with
  	   | var,Symbolic e ->
               pdebug ((Pp.var_to_string var) ^ " = " ^ (Pp.ast_exp_to_string e))
  	   | _ -> ()
      ) delta

  let print_mem (delta,_) =
    pdebug "contents of memories" ;
    VH.iter
      (fun k v ->
  	 match k,v with
  	   | var, ConcreteMem(mem,_) ->
               pdebug ("memory " ^ (Var.name var)) ;
               AddrMap.iter
  		 (fun i v ->
  		    pdebug((Printf.sprintf "%Lx" i)
  			   ^ " -> " ^ (Pp.ast_exp_to_string v))
  		 )
  		 mem
  	   | _ -> ()
      ) delta

  let print_var (delta,_) name =
    VH.iter
      (fun var exp ->
  	 match exp with
  	   | Symbolic e ->
  	       let varname = Var.name var in
  		 if varname = name then
  		   pdebug (varname ^ " = "
  			   ^ (Pp.ast_exp_to_string e))
  	   | _ -> ()
      ) delta

  (** Number of variable locations stored in state *)
  let num_values (delta,_) =
    VH.length delta

  (** Number of concrete memory locations stored in state *)
  let num_mem_locs (delta,_) =
    (** Number of bindings in map

	XXX: This is inefficient; switch to BatMaps which support cardinality
    *)
    let map_length m =
      AddrMap.fold (fun _ _ c -> c+1) m 0
    in
    VH.fold
      (fun k v count  ->
	 match k,v with
	   | var, ConcreteMem(mem,_) ->
             count + (map_length mem)
	   | _ -> count
      ) delta 0

  let copy (delta,stats) =  (VH.copy delta, {contents = !stats})
  let clear (delta,stats) =  VH.clear delta; clear_stats stats
  let create () = (VH.create 5000, {contents = empty_stats})

  let lookup_var (delta,stats) var =
    dprintf "Looking up var %s" (Pp.var_to_string var);
    try VH.find delta var
    with Not_found ->
    dprintf "Undefined var %s" (Pp.var_to_string var);
    add_undefined_var stats var;
    match Var.typ var with
	| TMem _
	| Array _ ->
	    empty_mem var
	| Reg _ ->
	    Symbolic(Var var)
  
  let update_var (delta,stats) var value =
    dprintf "Updating var %s" (Pp.var_to_string var);
    add_updated_var stats var value;
    VH.replace delta var value; 
    (delta,stats)
  
  let remove_var (delta,stats) var =
    VH.remove delta var;
    (delta,stats)

  (* Converting concrete memory to symbolic *)
  let conc2symb memory v =
    pdebug "Concrete to symbolic" ;
    (* FIXME: a better symbolism for uninitialized memories *)
    let init = Var v in
      pdebug "The point of no return" ;
      Symbolic (AddrMap.fold
		  (fun k v m -> Store (m,Int(big_int_of_int64 k,reg_32),v,exp_false,reg_8))
		  memory init)

  (* Normalize a memory address, setting high bits to 0. *)
  let normalize i t = int64_of_big_int (Arithmetic.to_big_int (i,t))

  let rec update_mem (delta,stats) mu pos value endian =
    add_memory_write stats mu pos value;
    (*pdebug "Update mem" ;*)
    match mu with
      | Symbolic m -> Symbolic (Store(m,pos,value,endian,reg_8))
      | ConcreteMem (m,v) ->
	  match pos with
	    | Int(p,t) ->
		ConcreteMem(AddrMap.add (normalize p t) value m, v)
	    | _ -> update_mem (delta,stats) (conc2symb m v) pos value endian

  let rec lookup_mem (delta,stats) mu index endian =
    add_memory_load stats mu index;
    (*pdebug "Lookup mem" ;*)
    match mu, index with
      | ConcreteMem(m,v), Int(i,t) ->
	  (try AddrMap.find (normalize i t) m
	   with Not_found ->
	     Load(Var v, index, endian, reg_8)
	       (* FIXME: handle endian and type? *)
	  )
	    (* perhaps we should introduce a symbolic variable *)
      | Symbolic mem, _ -> Load (mem,index,endian,reg_8)
      | ConcreteMem(m,v),_ -> lookup_mem (delta,stats) (conc2symb m v) index endian

end

module SymbolicWithIODetection = Make(SymbolicWithIODetectionMemoryLookup)(FastEval)(StdAssign)(StdForm)

(** Execute a program concretely *)
let symbolically_execute ?start_addr ?(init_stmts=[]) p =
  let rec step ctx =
    let s = try SymbolicWithIODetection.inst_fetch ctx.sigma ctx.pc
      with Not_found ->
        failwith (Printf.sprintf "Fetching instruction %#Lx failed; you probably need to add a halt to the end of your program" ctx.pc)
    in
    dprintf "Executing: %s" (Pp.ast_stmt_to_string s);
    let nextctxs = try SymbolicWithIODetection.eval ctx, None with
        SymbolicWithIODetection.Halted (v, ctx) -> [ctx], v
    in
    match nextctxs with
    | [next], None -> step next
    |  _, None -> failwith "step"
    (* Done recursing *)
    | [ctx], v -> ctx, v
    | _, Some _ -> failwith "step"
  in
  let ctx = SymbolicWithIODetection.build_default_context p in
  (* Evaluate initialization statements *)
  let ctx = List.fold_left (fun ctx s ->
			      dprintf "Init %s" (Pp.ast_stmt_to_string s);
			      match SymbolicWithIODetection.eval_stmt ctx s with
			      | nctx::[] -> nctx
			      | _ -> failwith "Expected one context"
			   ) ctx init_stmts 
  in
  let ctx = match start_addr with
    | Some(s) -> {ctx with pc = SymbolicWithIODetection.label_decode ctx.lambda (Addr s)}
    | None ->
      (* Explicitly set pc to 0, since executing any init statements
         will (unintentionally) increment pc. *)
      {ctx with pc = 0L}
  in
  let ctx, v = step ctx in
  SymbolicWithIODetection.print_values ctx.delta;
  SymbolicWithIODetection.print_mem ctx.delta;
  let stats = !(snd ctx.delta) in
  dprintf "Execution stats";
  dprintf "Inputs";
  List.iter (fun var -> 
      dprintf "%s" (Pp.var_to_string var)
  ) stats.undefined_vars;
  List.iter (fun (mem,idx) -> 
      match mem with
      | (Symbolic v) -> dprintf "%s[%s]" (Pp.ast_exp_to_string v) (Pp.ast_exp_to_string idx)
      | (ConcreteMem (m,v)) -> dprintf "%s[%s]" (Pp.var_to_string v) (Pp.ast_exp_to_string idx)
  ) stats.memory_loads;
  dprintf "Outputs";
  List.iter (fun (var, value) -> 
      match value with
      | (Symbolic v) -> dprintf "%s = %s" (Pp.var_to_string var) (Pp.ast_exp_to_string v)
      | (ConcreteMem (m,v)) -> dprintf "%s : " (Pp.var_to_string v);
               AddrMap.iter (fun i v -> dprintf "%#Lx -> %s " i (Pp.ast_exp_to_string v)) m
  ) stats.updated_vars;
  List.iter (fun (mem,idx,value) -> 
      match mem with
      | (Symbolic v) -> dprintf "%s[%s] = %s" (Pp.ast_exp_to_string v) (Pp.ast_exp_to_string idx)(Pp.ast_exp_to_string value)
      | (ConcreteMem (m,v)) -> dprintf "%s[%s] = %s" (Pp.var_to_string v)(Pp.ast_exp_to_string idx)(Pp.ast_exp_to_string value)
  ) stats.memory_writes;
  (match v with
  | Some(Symbolic v) -> dprintf "result: %s" (Pp.ast_exp_to_string v)
  | _ -> dprintf "no result");
  ctx
