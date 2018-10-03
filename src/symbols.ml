
module StringSet = BatSet.Make(String)

let symbol_blacklist =
  StringSet.of_enum (BatList.enum [
    (* _fini's BB ends up trimmed for some reason; need to investigate *)
    "_fini";
    (* _start ended up with no statements at the SSA stage, even though
       it's pretty beefy *)
    "_start";
    (* ocamlgraph assertion failure in coalesce_ast:
     * Invalid_argument("[ocamlgraph] iter_succ") *)
    "_getopt_internal_r";
    "atexit";
  ])

let sym_is_blacklist name =
  StringSet.mem name symbol_blacklist

let symbol_attributes =
  let open Func_attr in
  [
    ("__stack_chk_fail", [Abort]);
    ("abort", [Abort]);
    ("exit", [Noreturn]);
    (* XXX: can't keep doing this, need to deduce/propagate the Noreturn attr *)
    ("xalloc_die", [Noreturn]);
    ("__assert_fail", [Abort]);
  ]

let symattrs =
  let htbl = BatHashtbl.create (List.length symbol_attributes) in
  List.iter (fun (sym, attrlist) ->
    let attrs = Func_attr.FuncAttrSet.of_enum (BatList.enum attrlist) in
    BatHashtbl.add htbl sym attrs) symbol_attributes;
  htbl

let sym_has_attrs name = Misc.bathashtbl_find_option symattrs name
