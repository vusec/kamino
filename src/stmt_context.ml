
type context_list = Type.context list	(* list of contexts for a specific dynamic insn *)
type context_history = context_list list		(* observed ctxlists for a given dynamic insn *)

type stmt_context = {
  sctx_addr : Type.addr;
  sctx_ctxs: context_list;
}

(* XXX: atrocious field names; get creative to avoid the code police *)
type stmt_context_history = {
  sctxhist_addr : Type.addr;
  sctxhist_ctxlist : context_history;
}

let sctx_format ft stmt_ctx =
  Format.fprintf ft "# stmt %#Lx\n" stmt_ctx.sctx_addr;
  List.iter (fun ctx ->
    Format.pp_print_string ft (Print.context_to_string ctx);
    Format.pp_print_newline ft ()) stmt_ctx.sctx_ctxs

let sctxlist_format ft stmt_ctxs =
  List.iter (sctx_format ft) stmt_ctxs
