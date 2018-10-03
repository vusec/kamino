open BatPervasives

let input = ref None
let output = ref stdout
let args = ref 0

let speclist =
  [
    ("-output",
     Arg.String (fun out ->
         output := open_out out
       ),
     "Output generated specification to specified file."
    )
  ]

let usage = "Usage: " ^ Sys.argv.(0) ^ " [options] FILE.\n"

let print_usage_and_exit e =
  Arg.usage speclist (e ^ "\n" ^ usage);
  exit 1

let anon_arg arg =
  match !args with
  | 0 -> input := Some arg;
    incr args
  | _ -> raise (Arg.Bad (Printf.sprintf "Unexpected parameter %s" arg))

let () = Arg.parse (Arg.align speclist) anon_arg usage;
  match !input with
  | Some input ->
    begin
      match Batchspec.spec_of_inline_info input with
      | Some spec ->
        Printf.printf "%s\n" spec
      | None ->
        exit 2
    end
  | None -> print_usage_and_exit "No input specified!"
