type function_attr =
| Confusing of string
| Abort
| Noreturn
| WellBehaved

module FuncAttr =
struct
  type t = function_attr
  let num = function
    | Abort -> 0
    | Confusing _ -> 1
    | Noreturn -> 2
    | WellBehaved -> 3
  let compare a b =
    (num a) - (num b)
  let to_string = function
    | Abort -> "Abort"
    | Confusing s -> Printf.sprintf "(Confusing: %s)" s
    | Noreturn -> "Noreturn"
    | WellBehaved -> "WellBehaved"
end

module FuncAttrSet = BatSet.Make(FuncAttr)

let fattrs_to_string set =
  Print.enum_to_string ~enclosing:("{", "}") ~sep:", " FuncAttr.to_string
    (FuncAttrSet.enum set)
