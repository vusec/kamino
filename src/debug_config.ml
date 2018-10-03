open Core.Std
open Core_extended.Std

let debug_module_name sourcefile =
  let extract_debug_name line =
    let regexp = Str.regexp ".*Debug\\.Make(struct let name[^=]*=[^\"]*\"\\([^\"]+\\)\".*" in
    if Str.string_match regexp line 0 then
      Some (Str.matched_group 1 line)
    else None
  in
  let fold acc line =
    match acc with
    | Some _ -> acc
    | None ->
       begin
         match extract_debug_name line with
         | Some name -> Some name
         | None -> acc
       end
  in
  let find_debug_module_name in_chan = In_channel.fold_lines in_chan ~init:None ~f:fold in
  In_channel.with_file sourcefile ~f:find_debug_module_name

let source_files_in ?(recursive=true) path=
  let level = match recursive with | true -> None | false -> Some  1 in
  let find_options = {
    Find.Options.default with
    Find.Options.max_depth = level;
    Find.Options.follow_links = true;
    Find.Options.filter = Some (fun (filename, _) ->
                                match Filename.split_extension filename with
                                | _, Some "ml" -> true
                                | _ -> false
                               );
    Find.Options.on_stat_errors = Find.Options.Ignore
  } in
  List.map ~f:fst (Find.find_all ~options:find_options path)

let modules_in path =
  List.filter_map ~f:debug_module_name (source_files_in path)

let join ?(sep="") list =
  match List.reduce ~f:(fun x y -> x ^ sep ^ y) list with
  | Some s -> s
  | None -> ""

exception Unknown_group of string
let group_to_modules_in path group =
  let group_to_path group = match group with
    | "kamino" -> path ^ "/src"
    | "bap" -> path ^ "/deps/bap/ocaml"
    | unkn -> raise (Unknown_group unkn)
  in
  modules_in (group_to_path group)

let gen_config kamino_root list_modules groups () =
  let kamino_root = match kamino_root with
    | Some path -> path
    | None -> begin let env = Environment.of_exec_env (Unix.environment ()) in
                    match Environment.find ~key:"KAMINO_ROOT" env with
                    | Some value -> value
                    | None -> ""
              end in
  if kamino_root <> "" then
    begin
      if list_modules then
        List.iter ~f:(fun m -> printf "%s\n" m) (modules_in kamino_root)
      else begin
          printf "BAP_DEBUG_MODULES=%s\n" (match groups with
            | Some spec ->
               begin
                 let groups = String.split ~on:',' spec in
                 let modules = List.concat (List.map ~f:(group_to_modules_in kamino_root) groups) in
                 join ~sep:":" modules
               end
            | None -> join ~sep:":" (modules_in kamino_root))
        end
    end
  else begin
      fprintf stderr "No kamino root specified!\n";
      exit 1;
    end

let command =
  Command.basic
    ~summary:"Generate environment to control debug output of BAP and Kamino."
    Command.Spec.(
    empty
    +> flag "-k" (optional string) ~doc:"path location of kamino to use."
    +> flag "-l" no_arg ~doc:" list available modules."
    +> flag "-g" (optional string) ~doc:"groups enable modules in group."
  ) gen_config

let () =
  Command.run ~version:"0.1" command
