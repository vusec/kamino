open Core.Std
open Core_extended

let symcache = Hashtbl.Poly.create ()

let symbol_address binary symbol =
  let symmap_of_path binpath =
    let re = Str.regexp "\\([a-fA-F0-9]+\\)[\t ]+T[\t ]+\\([^\t ]+\\)$" in
    let kv_of_line str =
      if Str.string_match re str 0 = false then begin
        failwith (Printf.sprintf "Could not parse '%s' from nm" str)
      end;
      let addr = Str.matched_group 1 str in
      let addr = Int64.of_string (Printf.sprintf "0x%s" addr) in
      let sym = Str.matched_group 2 str in
      (sym, addr)
    in
    (*
     * We select text symbols only on the shell, so that we can sanity-check
     * our regexp above. This way, if it fails we know we've encountered some
     * output we weren't expecting and need to take a look to figure out how
     * to handle it.
     *)
    let lines = Shell.sh_lines "nm %s | grep -w T" binpath in
    List.fold_left ~init:(Map.empty String.comparator) ~f:(fun map line ->
        let (sym, addr) = kv_of_line line in
        Map.change map sym (fun oaddr ->
            match oaddr with
            | Some oaddr ->
              Printf.eprintf "Already have an address (%#Lx) for symbol %s (new is %#Lx)\n"
                  oaddr sym addr;
              failwith "Duplicate symbol address"
            | None -> Some addr)) lines
  in
  let find_sym symmap =
    match Map.find symmap symbol with
    | Some addr ->
      addr
    | None ->
      failwith (Printf.sprintf "No address for symbol %s in %s" symbol binary)
  in
  let symmap = match Hashtbl.find symcache binary with
    | Some symmap ->
      symmap
    | None ->
      let symmap = symmap_of_path binary in
      Hashtbl.set symcache ~key:binary ~data:symmap;
      symmap
  in
  find_sym symmap
