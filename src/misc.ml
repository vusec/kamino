module D = Debug.Make(struct let name = "Misc" and default=`Debug end)
open D

(*
 * For some reason, BatHashtbl.find_option may return
 * None while BatHashtbl.find (correctly) returns true.
 * This is the case at least until batteries-2.5.3 and
 * as far back as I remember. Fix this preemptively
 * /everywhere/ cause I'm done chasing it down. -- agg
 *)
let bathashtbl_find_option t k =
  try
    Some (BatHashtbl.find t k)
  with Not_found ->
    None

let finally finalizer f arg =
  let r =
    try
      f arg
    with e ->
      dprintf "Temporarily caught exception '%s' in order to run a finalizer" (Printexc.to_string e);
      (* Don't lose the backtrace! *)
      Printexc.print_backtrace stderr;
      finalizer ();
      raise e
  in
  finalizer ();
  r


let finally_with_exn handler f x =
  let r =
    try
      f x
    with e ->
      dprintf "Temporarily caught exception '%s' in order to run a finalizer" (Printexc.to_string e);
      (* Don't lose the backtrace! *)
      Printexc.print_backtrace stderr;
      handler (Some e);
      raise e
  in
  handler None;
  r

module type HashableStringSig =
sig
  type t = string
  val equal : t -> t -> bool
  val hash : t -> int
end;;

module HashableString : HashableStringSig =
struct
  type t = string
  let equal af1 af2 = af1 = af2
  let hash = Hashtbl.hash
end;;

let repeat times x =
  let rec inner acc n =
    if n = 0 then begin
      acc
    end else begin
      inner (x :: acc) (n - 1)
    end
  in
  inner [] times

let list_pad n el list =
  let diff = n - (List.length list) in
  if diff > 0 then begin
    list @ (repeat diff el)
  end else begin
    list
  end

let ary_bsearch ary unbox compare key =
  let rec search low high key =
    let pivot = low + (high - low) / 2 in
    let pivot_key = unbox (Array.get ary pivot) in
    let cmp = compare key pivot_key in
    if cmp = 0 then
      Some pivot
    else if low >= high then
      None
    else if cmp < 0 then
      search low pivot key
    else
      search (pivot + 1) high key
  in
  search 0 ((Array.length ary) - 1) key

let npartition classify els =
  let buckets = BatHashtbl.create 10 in
  List.fold_left (fun htbl el ->
    let key = classify el in
    let bucket = BatHashtbl.find_default htbl key [] in
    let bucket = el :: bucket in
    BatHashtbl.replace htbl key bucket;
    htbl) buckets els

(* XXX: duplicated from eval_batch.ml *)
(* Generate pairs without (x, x) and (x, y) = (y, x) *)
let list_unique_pairs l =
  let rec aux acc l = match l with
    | []  -> acc
    | h :: t -> begin match t with
        | [] -> acc (* If we want to include (x, x), replace with (h,h) :: acc *)
        | l' ->
          let acc' = List.rev
              (List.fold_left (fun acc e -> (h, e) :: acc) [] l') in
          aux (acc @ acc') t
      end
  in
  aux [] l

let rec permutations l =
  let rec insert x = function
    | [] -> [[x]]
    | h :: t -> (x :: h :: t) :: (List.map (fun l -> h :: l) (insert x t))
  in
  match l with
  | [] -> []
  | h :: [] -> [[h]]
  | h :: t -> List.flatten (List.map(fun l -> insert h l) (permutations t))

let longest_common_prefix_n eq lists =
  let rec inner acc rest =
    try
      begin
        let heads = List.map List.hd rest in
        match heads with
        | [] ->
          acc
        | x :: xs ->
          begin
            if List.exists (fun y -> not (eq x y)) xs then begin
              acc
            end else begin
              inner (x :: acc) (List.map List.tl rest)
            end
          end
      end
    with Failure s when s = "hd" -> acc
  in
  List.rev (inner [] lists)

let ffs n =
  let module I = Int64 in
  let two = I.of_int 2 in
  let rec inner off =
    if off = 64 then
      None
    else begin
      let n = I.shift_right_logical n off in
      if I.rem n two = I.one then
        Some off
      else
        inner (off + 1)
    end
  in
  inner 0

let count_trailing_ones (bi_ : Big_int_Z.big_int) =
  let open Big_int_convenience in
  let rec inner nset bi =
    if bi_is_zero bi then begin
      nset
    end else if bi_is_zero (bi &% bi1) then begin
      nset
    end else begin
      inner (nset + 1) (bi >>% 1)
    end
  in
  inner 0 bi_

let bi_is_mask (bi_, t) =
  let open Big_int_convenience in
  let (bi : Big_int_Z.big_int) = Arithmetic.to_big_int (bi_, t) in
  let ones = count_trailing_ones bi in
  if ones = 0 then begin
    None
  end else begin
    let trailing_ones_mask = (bi1 <<% ones) -% bi1 in
    if bi_is_zero (bi -% trailing_ones_mask) then begin
      Some ones
    end else begin
      None
    end
  end

let bi_bit_ranges (bi_, t) =
  let open Big_int_convenience in
  let nbits = Typecheck.bits_of_width t in
  let rec inner imap curr_bit_off bi =
    let imap = match bi_is_zero (bi &% bi1) with
      | true -> imap
      | false -> BatISet.add curr_bit_off imap
    in
    let curr_bit_off = curr_bit_off + 1 in
    if curr_bit_off < nbits then begin
      inner imap curr_bit_off (bi >>% 1)
    end else begin
      imap
    end
  in
  inner BatISet.empty 0 (Arithmetic.to_big_int (bi_, t))

(*
 * Given two lists of possibly different sizes and a function that
 * determines whether any two given elements match, find matching
 * pairs by combinatorial search.
 * Returns the matches and the elements remaining on either side.
 * The matching function takes the user-provided accumulator (state)
 * and returns an option. If None, the elements can't be matched and
 * the state is passed on as-is. If the elements do match, the user-
 * supplied function should return Some (nstate, something), where
 * nstate is the (potentially modified) state which will be seen by
 * further invocations of the user function and 'something' is
 * some expression of this specific match. The 'something's will be
 * returned in a list, but they are not available in later invocations
 * of the user function.
 *)
let lists_do_match user_state l1 l2 do_match =
  let one_to_n caller_state one n =
    let rec one_to_n_inner state remaining didnt_match =
      match remaining with
      | [] ->
	None
      | x::xs ->
	match do_match state one x with
	| Some (nstate, save) ->
	  Some (nstate, xs @ didnt_match, save)
	| None ->
	  one_to_n_inner state xs (x::didnt_match)
    in
    one_to_n_inner caller_state n []
  in
  let rec lists_cardinal_inner state l1 l2 matches didnt_match1 =
    match l1 with
    | [] ->
      (state, matches, didnt_match1, l2)
    | el1 :: rest ->
      let ret = one_to_n state el1 l2 in
      (match ret with
      | Some (nstate, l2', save) ->
	         (* XXX: callback *)
	lists_cardinal_inner nstate rest l2' (save::matches) didnt_match1
      | None ->
	lists_cardinal_inner state rest l2 matches (el1::didnt_match1)
      )
  in
  lists_cardinal_inner user_state l1 l2 [] []

type arch = Asmir.arch
let is_call arch stmt =
  let call_regexp = Str.regexp "call\\(.*\\)" in
  let re_match_call s = Str.string_match call_regexp s 0 in
  if arch = Asmir.arch_i386 then
    (match stmt with
    | Ast.Jmp (_, attrs) ->
      (let attrs = Ast.get_attrs stmt in
       try
         let attr_str = List.find (fun attr -> match attr with
           | Type.StrAttr _ -> true
           | _ -> false) attrs in
         let str =
           (match attr_str with
           | Type.StrAttr asm -> asm
           | _ -> "")
         in
         re_match_call str
       with Not_found -> false)
    | _ -> false)
  else
    failwith "not implemented"

let is_ret arch stmt =
  if arch = Asmir.arch_i386 then
    (match stmt with
    | Ast.Jmp (_, attrs) ->
      (let ret_regexp = Str.regexp "\\(repz[ ]+\\)?retn?.*" in
       let match_ret s = Str.string_match ret_regexp s 0 in
       let is_ret_str attr =
	 match attr with
	 | Type.StrAttr str -> match_ret str
	 | _ -> false
       in
       List.exists is_ret_str attrs)
    | _ -> false)
  else
    failwith "not implemented"

let call_is_getpc arch pc stmt =
  if arch = Asmir.arch_i386 then
    (match stmt with
    | Ast.Jmp (Ast.Int (taddr, t), attrs) ->
      let open Big_int_Z in
      let diff = sub_big_int taddr (big_int_of_int64 pc) in
      eq_big_int diff (big_int_of_int 5)
    | _ -> false)
  else
    failwith "not implemented"

let ast_replace_calls arch stmts =
  let replace_call s =
    match is_call arch s with
    | true -> Ast.Special ("dummy_call", Ast.get_attrs s)
    | false -> s
  in
  List.map replace_call stmts

(*
 * Replace all occurences of the specified regexp in the supplied
 * string with unique identifiers, but be consistent so that
 * the same regexp match is always replaced with the same identifier.
 *)
let normalize_string id_regexp string =
  let replace hsh id =
    match BatHashtbl.find_option hsh id with
    | Some repl ->
      repl
    | None ->
      let serial = (BatHashtbl.length hsh) + 1 in
      let repl = string_of_int serial in
      BatHashtbl.add hsh id repl;
      repl
  in
  let rec norm_string str acc pos mapping =
    try
      let mpos = Str.search_forward id_regexp str pos in
      let ms = Str.matched_string str in
      let repl = replace mapping ms in
      let leading = String.sub str pos (mpos - pos) in
      let nacc = String.concat "" [acc; leading; "_"; repl] in
      norm_string str nacc (mpos + (String.length ms)) mapping
    with Not_found ->
      let remaining = String.sub str pos ((String.length str) - pos) in
      String.concat "" [acc; remaining]
  in
  dprintf "normalize_string: before: %s" string;
  let ret = norm_string string "" 0 (BatHashtbl.create 10) in
  dprintf "normalize_string: after: %s" ret;
  ret

let strcmp tmpl ~expected ~got =
  let (exp_path, exp_tf) = Filename.open_temp_file tmpl "expected" in
  let (got_path, got_tf) = Filename.open_temp_file tmpl "result" in
  output_string exp_tf expected;
  flush exp_tf;
  close_out exp_tf;
  output_string got_tf got;
  flush got_tf;
  close_out got_tf;
  let cmd = Printf.sprintf "diff -bu '%s' '%s'" exp_path got_path in
  let p = BatUnix.open_process_in cmd in
  let data = BatInnerIO.read_all p in
  let ret = if 0 = String.length data then
    BatResult.Ok ()
  else
    BatResult.Bad data
  in
  Unix.unlink exp_path;
  Unix.unlink got_path;
  ret

let stmts_with_addrs stmts =
  let visitor = object
    inherit Ast_visitor.nop
    val mutable curr_addr = None
    val mutable stmts = []
    method stmts_with_addr () =
      List.rev stmts
    method visit_stmt = function
    | Ast.Label (Type.Addr addr, _) as stmt->
      curr_addr <- Some addr;
      stmts <- (curr_addr, stmt) :: stmts;
      Type.SkipChildren
    | stmt ->
      stmts <- (curr_addr, stmt) :: stmts;
      Type.SkipChildren
  end
  in
  ignore(Ast_visitor.prog_accept visitor stmts);
  visitor#stmts_with_addr ()

let rec ast_exprs_eq e1 e2 =
  let open Ast in
  let open Big_int_Z in
  match e1, e2 with
  | Load (ary1, idx1, end1, typ1), Load (ary2, idx2, end2, typ2) ->
    if typ1 <> typ2 then begin
      let str = Printf.sprintf "types %s %s differ" (Pp.typ_to_string typ1)
        (Pp.typ_to_string typ2) in
      BatResult.Bad str
    end else
      do_cmp_exprs [ary1; idx1; end1;] [ary2; idx2; end2;]
  | Store (ary1, idx1, val1, end1, typ1), Store (ary2, idx2, val2, end2, typ2) ->
    if typ1 <> typ2 then begin
      let str = Printf.sprintf "types %s %s differ" (Pp.typ_to_string typ1)
        (Pp.typ_to_string typ2) in
      BatResult.Bad str
    end else
      do_cmp_exprs [ary1; idx1; val1; end1;] [ary2; idx2; val2; end2;]
  | BinOp (op1, a1, b1), BinOp (op2, a2, b2) ->
    if op1 = op2 then begin
      do_cmp_exprs [a1; b1;] [a2; b2;]
    end else begin
      let str = Printf.sprintf "binops %s %s differ" (Pp.binop_to_string op1)
        (Pp.binop_to_string op2) in
      BatResult.Bad str
    end
  | UnOp (op1, e1), UnOp (op2, e2) ->
    if op1 = op2 then
      do_cmp_exprs [e1] [e2]
    else begin
      let str = Printf.sprintf "unops %s %s differ" (Pp.unop_to_string op1)
        (Pp.unop_to_string op2) in
      BatResult.Bad str
    end
  | Var v1, Var v2 ->
    if String.compare (Var.name v1) (Var.name v2) = 0 then
      BatResult.Ok ()
    else
      BatResult.Bad (Printf.sprintf "var names %s %s differ" (Var.name v1)
                    (Var.name v2))
  | Lab _, Lab _ ->
    (* We rely on cfg edges to detect label mismatches *)
    BatResult.Ok ()
  | Int (bi1, typ1), Int (bi2, typ2) ->
    if typ1 = typ2 then begin
      if compare_big_int bi1 bi2 = 0 then
        BatResult.Ok ()
      else
        BatResult.Bad (Printf.sprintf "big_ints differ: %s %s"
                      (string_of_big_int bi1)
                      (string_of_big_int bi2))
    end else begin
      let str = Printf.sprintf "types %s %s differ" (Pp.typ_to_string typ1)
        (Pp.typ_to_string typ2) in
      BatResult.Bad str
    end
  | Cast (ct1, typ1, e1), Cast (ct2, typ2, e2) ->
    if typ1 = typ2 then begin
      if ct1 = ct2 then
        do_cmp_exprs [e1] [e2]
      else begin
        let str = Printf.sprintf "cast types %s %s differ" (Pp.ct_to_string ct1)
            (Pp.ct_to_string ct2) in
        BatResult.Bad str
      end
    end else begin
      let str = Printf.sprintf "types %s %s differ" (Pp.typ_to_string typ1)
        (Pp.typ_to_string typ2) in
      BatResult.Bad str
    end
  | Let (v1, a1, b1), Let (v2, a2, b2) ->
    if String.compare (Var.name v1) (Var.name v2) = 0 then
      do_cmp_exprs [a1; b1;] [a2; b2;]
    else
      BatResult.Bad (Printf.sprintf "var names %s %s differ" (Var.name v1)
                    (Var.name v2))
  | Unknown (s1, typ1), Unknown (s2, typ2) ->
    if typ1 = typ2 then begin
      if String.compare s1 s2 = 0 then
        BatResult.Ok ()
      else
        BatResult.Bad (Printf.sprintf "unknowns %s %s differ" s1 s2)
    end else begin
      let str = Printf.sprintf "types %s %s differ" (Pp.typ_to_string typ1)
        (Pp.typ_to_string typ2) in
      BatResult.Bad str
    end
  | Ite (a1, b1, c1), Ite (a2, b2, c2) ->
    do_cmp_exprs [a1; b1; c1;] [a2; b2; c2]
  | Extract (h1, l1, e1), Extract (h2, l2, e2) ->
    if compare_big_int h1 h2 = 0 then begin
      if compare_big_int l1 l2 = 0 then
          do_cmp_exprs [e1] [e2]
      else
        BatResult.Bad (Printf.sprintf "big_ints differ: %s %s"
                      (string_of_big_int l1)
                      (string_of_big_int l2))
    end else begin
        BatResult.Bad (Printf.sprintf "big_ints differ: %s %s"
                      (string_of_big_int h1)
                      (string_of_big_int h2))
    end
  | Concat (a1, b1), Concat (a2, b2) ->
    do_cmp_exprs [a1; b1;] [a2; b2;]
  | _ ->
    BatResult.Bad "expression types differ"
and do_cmp_exprs es1 es2 =
  if (List.length es1) <> (List.length es2) then
    BatResult.Bad (Printf.sprintf "#exprs differs: %d %d"
                  (List.length es1) (List.length es2))
  else
    BatList.fold_left2 (fun acc e1 e2 ->
        match acc with
        | BatResult.Bad _ as bad -> bad
        | BatResult.Ok () -> ast_exprs_eq e1 e2
      ) (BatResult.Ok ()) es1 es2

let ast_stmts_eq s1 s2 =
  let open Ast in
  let res = match s1, s2 with
    | Move (v1, e1, _), Move (v2, e2, _) ->
      if String.compare (Var.name v1) (Var.name v2) <> 0 then begin
        let str = Printf.sprintf "%s compares unequal to %s"
            (Var.name v1) (Var.name v2) in
        BatResult.Bad str
      end else begin
        do_cmp_exprs [e1] [e2]
      end
    | CJmp (c1, then1, else1, _), CJmp (c2, then2, else2, _) ->
      do_cmp_exprs [c1;] [c2;]
    | Halt (e1, _), Halt (e2, _)
    | Assert (e1, _), Assert (e2, _) ->
      do_cmp_exprs [e1] [e2]
    | Special (s1, _), Special (s2, _) ->
      if String.compare s1 s2 = 0 then
        BatResult.Ok ()
      else
        BatResult.Bad (Printf.sprintf "specials %s %s differ" s1 s2)
    | Comment _, Comment _
    | Jmp _, Jmp _
    (* XXX: we need special handling of calls!! *)
    | Label _, Label _ ->
      BatResult.Ok ()
    | _ ->
      BatResult.Bad "Statement types differ"
  in
  match res with
  | BatResult.Ok () as ok -> ok
  | BatResult.Bad reason ->
    let str = Printf.sprintf "stmts %s %s differ (%s)"
        (Pp.ast_stmt_to_string s1) (Pp.ast_stmt_to_string s2)
        reason in
    BatResult.Bad str

let stmt_comparator_noop _ _ = BatResult.Ok ()

let stmt_comparator_standard stmts1 stmts2 =
  if (List.length stmts1) <> (List.length stmts2) then
    BatResult.Bad "Different number of statements"
  else
    BatList.fold_left2 (fun acc s1 s2 ->
        match acc with
        | BatResult.Bad _ as bad -> bad
        | BatResult.Ok () -> ast_stmts_eq s1 s2
      ) (BatResult.Ok ()) stmts1 stmts2


module type Lang
=
sig
  type stmtlist
end

module LangAST = struct
  type stmtlist = Ast.stmt list
end

module LangSSA = struct
  type stmtlist = Ssa.stmt list
end

(* XXX: migrate to own file *)
module CfgUtil(L:Lang)(C : Cfg.CFG with type lang = L.stmtlist)
=
struct
  module G = C.G
  let e2s e =
    let lab = (G.E.label e) in
    let src, dst = (G.E.src e, G.E.dst e) in
    let str = match lab with
      | Some true -> "T"
      | Some false -> "F"
      | None -> "-"
    in
    Printf.sprintf "%s -%s-> %s" (C.v2s src) str (C.v2s dst)

  let compare ~stmt_comparator cfg1 cfg2 =
  (* let module C = (val cfgmod : Cfg.CFG with type lang = stmt list) in *)
  (* let module G = C.G in *)
  let rec cmp_bbs ~visited1 ~visited2 ~bb1 ~bb2 =
    let stmts1 = C.get_stmts cfg1 bb1 in
    let stmts2 = C.get_stmts cfg2 bb2 in
    match stmt_comparator stmts1 stmts2 with
    | BatResult.Bad _ as bad ->
      bad
    | BatResult.Ok () ->
      begin
        let succ_e1 = G.succ_e cfg1 bb1 in
        let succ_e2 = G.succ_e cfg2 bb2 in
        if List.length succ_e1 <> List.length succ_e2 then begin
          let str = Printf.sprintf "#succ for (%s, %s) differ" (C.v2s bb1) (C.v2s bb2) in
          BatResult.Bad str
        end else begin
          let esort e1 e2 =
            let lab1 = G.E.label e1 in
            let lab2 = G.E.label e2 in
            match lab1, lab2 with
            | None, None -> 0
            | None, _ -> -1
            | Some false, None -> 1
            | Some false, Some false -> 0
            | Some false, Some true -> -1
            | Some true, Some true -> 0
            | Some true, _ -> 1
          in
          let edges1 = List.sort esort succ_e1 in
          let edges2 = List.sort esort succ_e2 in
          BatList.fold_left2 (fun acc edge1 edge2 ->
              match acc with
              | BatResult.Bad _ as bad -> bad
              | BatResult.Ok (visited1, visited2) ->
                if G.E.label edge1 <> G.E.label edge2 then begin
                  (*
                   * For each edge labeled with this type, there needs to
                   * be a matching one on the other side.
                   *)
                  let str = Printf.sprintf "No matching edge for %s" (e2s edge1) in
                  BatResult.Bad str
                end else begin
                  visit_bbs ~visited1 ~visited2
                    ~bb1:(G.E.dst edge1)
                    ~bb2:(G.E.dst edge2)
                end) (BatResult.Ok (visited1, visited2)) edges1 edges2
        end
      end
  and visit_bbs ~visited1 ~visited2 ~bb1 ~bb2 =
    match BatSet.mem bb1 visited1, BatSet.mem bb2 visited2 with
    | false, false ->
      let visited1 = BatSet.add bb1 visited1 in
      let visited2 = BatSet.add bb2 visited2 in
      cmp_bbs ~visited1 ~visited2 ~bb1 ~bb2
    | true, true ->
      BatResult.Ok (visited1, visited2)
    | _ ->
      (*
       * We make exactly the same next BB choice on both sides, so if
       * one BB has been visited before another, the graphs cannot be
       * isomorphic.
       *)
      BatResult.Bad "Graphs are not isomorphic"
  in
  let entry1 = C.find_vertex cfg1 Cfg.BB_Entry in
  let entry2 = C.find_vertex cfg2 Cfg.BB_Entry in
  match visit_bbs BatSet.empty BatSet.empty entry1 entry2 with
  | BatResult.Ok _ -> BatResult.Ok ()
  | BatResult.Bad _ as bad -> bad
end

let astcfgs_identical cfg1 cfg2 =
  let module CfgUtil = CfgUtil(LangAST)(Cfg.AST) in
  CfgUtil.compare ~stmt_comparator:stmt_comparator_standard cfg1 cfg2

let astcfgs_isomorphic cfg1 cfg2 =
  let module CfgUtil = CfgUtil(LangAST)(Cfg.AST) in
  CfgUtil.compare ~stmt_comparator:stmt_comparator_noop cfg1 cfg2

let ssacfgs_isomorphic cfg1 cfg2 =
  let module CfgUtil = CfgUtil(LangSSA)(Cfg.SSA) in
  CfgUtil.compare ~stmt_comparator:stmt_comparator_noop cfg1 cfg2

type frange = (string * Int64.t * Int64.t)

let demangle_franges franges =
  let (input, output) = Unix.open_process "c++filt" in
  let demangled = List.map (fun (name, s, e) ->
      Printf.fprintf output "%s\n" name;
      flush output;
      let line = input_line input in
      let demangled = BatString.trim line in
      (demangled, s, e)) franges
  in
  close_out output;
  demangled

let dedup_franges franges =
  let htbl = BatHashtbl.create 10 in
  let htbl = List.fold_left (fun acc fr ->
      let (_, s, _) = fr in
      let prev = BatHashtbl.find_default acc s [] in
      BatHashtbl.add acc s (fr :: prev);
      acc
    ) htbl franges
  in
  let deduped = BatHashtbl.fold (fun k v acc ->
      match v with
      | [] ->
        failwith "Empty list when deduping franges"
      | (name, s, e) :: _ ->
        begin
          List.iter (fun (_, s', e') ->
              (* The functions must match exactly *)
              assert(s' = s);
              assert(e' = e)) v;
          let names = List.map (fun (name, _, _) -> name) v in
          (names, s, e) :: acc
        end
    ) htbl []
  in
  List.sort (fun (_, s1, _) (_, s2, _) -> Int64.compare s1 s2) deduped

let type_width_equal t1 t2 =
  match (t1, t2) with
  | Type.Reg bits1, Type.Reg bits2 when bits1 = bits2 -> true
  | _ -> false

module Pervasives = struct
  let ( |- ) f g x = g (f x)
end
