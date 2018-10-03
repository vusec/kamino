
module FileMemo =
struct
  type k = string
  type v = in_channel
  type priv = unit
  let lookup _ = open_in
  let finalize ic =
    Printf.eprintf "finalize!\n%!";
    close_in ic
  let k_to_string k = k
end;;
	 

let () =
  let () = Printf.printf "Starting\n%!" in
  let module M = Memo.MakeSingleMemoizer(FileMemo) in
  let memo = M.create () in
  let paths = ["/etc/passwd"; "/etc/services"; "/etc/services"; "/etc/hosts"] in
  let lines = List.map (fun p ->
    let ic = M.lookup memo p in
    input_line ic) paths in
  List.iter (fun l -> Printf.printf "line: %s\n" l) lines
