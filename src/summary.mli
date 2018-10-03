module Algo :
sig
  val handle_ast_callgraph:
    ?func_filter:(Function_info.t -> bool) ->
    Misc.arch ->
    ?keypref:string option ->
    Callgraph.Callgraph.t ->
    (Analysis_pass.pipeline_ctx option Function_info.Hashtbl.t *
       Callgraph.Callgraph.t)
  val handle_astcfg_callgraph:
    ?func_filter:(Function_info.t -> bool) ->
    Analysis_pass.pipeline_ctx option Function_info.Hashtbl.t->
    ?keypref:string option ->
    Callgraph.Callgraph.t ->
    (Analysis_pass.pipeline_ctx option Function_info.Hashtbl.t *
       Callgraph.Callgraph.t)
  val handle_callgraph:
    ?func_filter:(Function_info.t -> bool) ->
    Misc.arch -> string -> (string, string list) Hashtbl.t option  ->
    Callgraph.Callgraph.t -> Stats.analyzable_type ->
    Ktype.analyzed_func list
  val handle_binary : ?runid:int -> int -> Input.binary_spec ->
    (Ktype.analyzed_func list * Stats.analyzable_type)
end;;

val summarize_binary_spec: ?runid:int -> ?report_coverage:bool ->
                           Input.binary_spec -> Ktype.analyzed_prog
val fold : f:('a -> Ktype.analyzed_prog -> 'a) -> init:'a -> ?runid:int -> Input.binary_spec list -> 'a
