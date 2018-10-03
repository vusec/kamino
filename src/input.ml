open Sexplib.Std

module BinaryPath = struct
  include BatPathGen.OfString

  let t_of_sexp sexp = of_string (Sexplib.Conv.string_of_sexp sexp)
  let sexp_of_t t = Sexplib.Conv.sexp_of_string (to_string t)
end

module HashedParameter = struct
  type t = string with sexp
  let equal = (=)
  let hash = Hashtbl.hash
end

type parameter_value = string list with sexp

module BinaryParameters = struct
  include BatHashtbl.Make(HashedParameter)

  let t_of_sexp val_of_sexp sexp = match sexp with
    | Sexplib.Sexp.List lst ->
       let htbl = create 0 in
       let act = function
         | Sexplib.Sexp.List [k_sexp; v_sexp] ->
            add htbl (HashedParameter.t_of_sexp k_sexp) (val_of_sexp v_sexp)
         | Sexplib.Sexp.List _ | Sexplib.Sexp.Atom _ ->
            Sexplib.Conv.of_sexp_error "hashtbl_of_sexp: tuple list needed" sexp
       in
      List.iter act lst;
      htbl
    | Sexplib.Sexp.Atom _ -> Sexplib.Conv.of_sexp_error "hashtbl_of_sexp: list needed" sexp

  let sexp_of_t sexp_of_val t =
    let coll k v acc = Sexplib.Sexp.List [HashedParameter.sexp_of_t k; sexp_of_val v] :: acc in
    Sexplib.Sexp.List (fold coll t [])

end

type binary_spec = {
  path: BinaryPath.t;
  parameters: parameter_value BinaryParameters.t option;
} with sexp

let create_binary_spec ?parameters path =
  {path=BinaryPath.of_string path; parameters}

module Parsers = struct
  exception Parse_error of string

  let split_commas str = Str.split (Str.regexp "," ) str
  let split_colons str = Str.split (Str.regexp ":" ) str

  let parse_param_spec ?valid_params str =
    let r = Str.regexp "\\([^=]+\\)=\\(.+\\)" in
    if Str.string_match r str 0
    then
      begin
        let key = Str.matched_group 1 str in
        let split_kvp str =
          let values = split_colons (Str.matched_group 2 str) in
          (key, values)
        in
        match valid_params with
        | Some l ->
           if List.mem key l
           then split_kvp str
           else raise (Parse_error (Printf.sprintf "Unknown parameter %s!" key))
        | None -> split_kvp str
      end
    else raise (Parse_error "Invalid parameter specification!")

  let parse_binary_spec str =
    match split_commas str with
    | [] -> raise (Parse_error "Invalid binary specification!")
    | [binary] -> create_binary_spec binary
    | binary :: params ->
       begin let param_lookup = BinaryParameters.create (List.length params) in
             let add_param params param =
               let k, v = parse_param_spec ~valid_params:["funcs"] param in
               BinaryParameters.add params k v;
               params
             in
             let params = List.fold_left add_param param_lookup params in
             create_binary_spec ~parameters:params binary
       end

  let parse_timeout str =
    let r = Str.regexp "\\([1-9][0-9]*\\)\\(s\\|m\\|h\\)?" in
    if Str.string_match r str 0 then
      begin
        let amount = int_of_string (Str.matched_group 1 str) in
        try
          match Str.matched_group 2 str with
          | "s" -> amount
          | "m" -> amount * 60
          | "h" -> amount * 3600
          | unkn -> raise (Parse_error (Printf.sprintf "Unknown timeout factor '%s'" unkn))
        with Not_found -> amount
      end
    else raise (Parse_error "Invalid timeout specification")

  let parse_compare_strategy str =
    match str with
    | "combcmp" -> `CombinatorialComparison
    | _ -> raise (Parse_error (Printf.sprintf "No such compare strategy: %s" str))
end
