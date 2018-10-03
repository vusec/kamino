module D = Debug.Make(struct let name = "Address_ranges" and default=`NoDebug end)
open D

(* XXX: kill me *)
let print_attrs attrs =
  let () = dprintf "attrs (%d){\n" (List.length attrs) in
  let pp = new Pp.pp Format.std_formatter in
  let () = List.iter (fun attr ->
    pp#attr attr) attrs
  in
  let () = Format.pp_print_flush Format.std_formatter () in
  pp#close;
  dprintf "} attrs\n"

let get_ast_cfg asm_prog s e =
  let arch = Asmir.get_asmprogram_arch asm_prog in
  let stmts = Asmir.asmprogram_to_bap_range asm_prog s e in
  let () = dprintf "get_ast_cfg %#Lx %#Lx\n" s e in
  let dumb_cfg = Cfg_ast.of_prog ~special_error:false (Misc.ast_replace_calls arch stmts) in
  (* XXX: this assumes there are no actual indirect jumps other than rets *)
  let no_ind = Hacks.ast_remove_indirect dumb_cfg in
  let optimistic_cfg = Coalesce.coalesce_ast (Prune_unreachable.prune_unreachable_ast no_ind) in
  optimistic_cfg

module FuncCfgMemoImpl =
struct
  type k = Int64.t * Int64.t
  type v = Cfg.AST.G.t
  type priv = Asmir.asmprogram
  let lookup asmp (low, high)= get_ast_cfg asmp low high
  let finalize _ = dprintf "switching function\n%!"
  let k_to_string (s, e) = Printf.sprintf "(%#Lx, %#Lx)" s e
end

module FuncCfgMemo = Memo.MakeSingleMemoizer(FuncCfgMemoImpl);;

class type address_ranges_type =
object
  method get_program_bounds : (Int64.t * Int64.t)
  method get_function : Int64.t -> (string * Int64.t * Libbfd.address_t) option
  method get_function_bb : Int64.t -> ((string * Int64.t * Libbfd.address_t) option * (Int64.t * string)) option
end;;

class address_ranges binary =
  let asm_prog = Asmir.open_program binary in
  let franges = Array.of_list (Asmir.get_function_ranges asm_prog) in
  let sort_cmp (_, a, _) (_, b, _) = Int64.compare a b in
  let () = Array.sort sort_cmp franges in
  let cfgmemo = FuncCfgMemo.create asm_prog in
object (self)
  method get_program_bounds =
    let (_, s, _) = Array.get franges 0
    and (_, _, e) = Array.get franges ((Array.length franges) - 1) in
    (s, e)
  method get_function addr =
    let addr_cmp s e addr =
      if addr < s then
	-1
      else if addr >= e then
	1
      else
	0
    in
    let range_cmp (_, s1, e1) (_, s2, e2) =
      if (s1 = e1) then
	addr_cmp s2 e2 s1
      else if (s2 = e2) then
	addr_cmp s1 e1 s2
      else
	raise (Failure("no address?"))
    in
    let idx = Misc.ary_bsearch franges (fun x -> x) range_cmp ("_", addr, addr) in
    match idx with
    | Some i -> Some (Array.get franges i)
    | None -> None
  method get_function_bb addr =
    let module AddrMap = BatMap.Make(Int64) in
    let get_bb s e =
      let () = dprintf "get_bb: function boundaries (%#Lx-%#Lx)" s e in
      (* XXX: should be caching the BB enum, not the cfg *)
      let cfg = FuncCfgMemo.lookup cfgmemo (s, e) in
      (* put the start address of each BB in an ordered map *)
      let sort_bbs =
	let addr_to_bb = AddrMap.empty in
	let bb_add_to_map v map =
	  let () = dprintf "bb_add_to_map: %s" (Cfg.AST.v2s v) in
	  try
	    match Bb.get_bbaddr (Cfg.AST.get_stmts cfg v) with
	    | None -> map (* failwith "Couldn't get bbaddr" *)
	    | Some bbaddr ->
	      (* stick the BB address in the ordered map *)
	      AddrMap.add bbaddr (Cfg.AST.v2s v) map
	  with Not_found -> map
	in
	Cfg.AST.G.fold_vertex bb_add_to_map cfg addr_to_bb
      in
      let addr_to_bb = sort_bbs in
      let enum = AddrMap.backwards addr_to_bb in
      (* Which BB does the address belong to? *)
      let (bbaddr, bb) = BatEnum.find (fun (k, _) ->
	addr >= k) enum in
      (bbaddr, bb)
    in
    let frange = self#get_function addr in
    match frange with
    | None -> None
    | Some (fname, s, e) ->
      let bb = get_bb s e in
      (* the frange is for free, so throw it in as a limited-time offer *)
      Some (frange, bb)
end
;;

(*
XXX: ocamldocify

Usage example

let () =
  let ar = new address_ranges Sys.argv.(1) in
  let addr = Int64.of_string Sys.argv.(2) in
  let frange_bb = ar#get_function_bb addr in
  match bb with
  | None -> Printf.printf "Can't get bb for %#Lx\n" addr
  | Some (_, (bbaddr, bbname)) ->
    Printf.printf "bb for %#Lx is %s@%#Lx\n" addr bbname bbaddr
*)
