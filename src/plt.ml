module D = Debug.Make(struct let name = "Plt" and default=`NoDebug end)
open D

let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
       try Some (input_line channel) with End_of_file -> None);;

let parse_plt_entry plt_entry =
  let () = dprintf "Parsing entry %s" plt_entry in
  let plt_entry_pattern = Str.regexp "\\(0x[0-9a-fA-F]+\\) \\(.+\\)" in
  match Str.string_match plt_entry_pattern plt_entry 0 with
  | true -> (Int64.of_string (Str.matched_group 1 plt_entry), Str.matched_group 2 plt_entry)
  | false -> failwith "Invalid PLT entry!"

let parse_plt_entries stream =
  let entries = ref [] in
  let () =
    Stream.iter (fun entry -> entries := (parse_plt_entry entry) :: !entries) stream
  in
  !entries

let pltpath_of_binpath binpath = (binpath ^ ".plt")

let gen_plt_file ~unlink:rm binary =
  let pltpath = pltpath_of_binpath binary in
  dprintf "Regenerating .plt file for %s" binary;
  if rm then
    Unix.unlink pltpath;
  let cmd = Printf.sprintf "readelf -W -r '%s' | grep -E '^[0-9a-fA-F]+' | grep R_386_JUMP_SLOT | awk '{print \"0x\"$1\" \"$5}' | c++filt > '%s'" binary pltpath in
  dprintf "Running: %s" cmd;
  match Unix.system(cmd) with
  | Unix.WEXITED 0 -> open_in pltpath
  | _ -> failwith "Could not generate PLT file"

let get_plt_file binary =
  let open Unix in
  let path = pltpath_of_binpath binary in
  let bin_stat = stat binary in
  try
    let fd = openfile path [O_RDONLY] 0 in
    let plt_stat = fstat fd in
    if bin_stat.st_mtime > plt_stat.st_mtime then
      gen_plt_file ~unlink:true binary
    else
      in_channel_of_descr fd
  with Unix_error (Unix.ENOENT, _, _) ->
    gen_plt_file ~unlink:false binary

let plt_entries_from binary =
  let plt_entries_file = get_plt_file binary in
  let stream = line_stream_of_channel plt_entries_file in
  let plt_entries = parse_plt_entries stream in
  let () = close_in plt_entries_file in
  plt_entries

let plt_resolve_addr asm_prog plt_entries plt_addr =
  let stmts,_ = Asmir.asm_addr_to_bap asm_prog plt_addr in
  (* We expect a comment with the asm, a label and a jump instruction*)
  if (List.length stmts) == 3 then
    match List.hd(List.rev stmts) with
    | Ast.Jmp (Ast.Load (_, Ast.Int (addr, _), _, _),_) -> (
        try
          let addr = Big_int_Z.int64_of_big_int addr in
          let () = dprintf "Searching plt entries" in
          let (offset, symbol) = List.find (
              fun (offset,_) ->
                dprintf "Comparing %Lx with %Lx" addr offset;
                (Int64.compare addr offset) == 0) plt_entries in
          Some (Function_info.create_external symbol plt_addr)
        with Not_found ->
          dprintf "Addr is not in PLT";
          None)
    | _ as s -> dprintf "%s is not a jump!" (Pp.ast_stmt_to_string s); None
  else None
