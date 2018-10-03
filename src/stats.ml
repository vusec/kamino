module StringHtbl = BatHashtbl.Make(Misc.HashableString)

class type analyzable_type =
object
  method analyzed : unit
  method failed : string -> unit
  method to_string : string
  method sexp_of_t : Sexplib.Sexp.t
end

class analyzable name =
object(self)
  val mutable n_total = 0
  val mutable n_analyzed = 0
  val failures = StringHtbl.create 10
  method analyzed =
    n_total <- n_total + 1;
    n_analyzed <- n_analyzed + 1
  method failed reason =
    n_total <- n_total + 1;
    match StringHtbl.Exceptionless.find failures reason with
    | Some n ->
      StringHtbl.replace failures reason (n + 1)
    | None ->
      StringHtbl.add failures reason 1
  method to_string =
    let to_s (reason, count) = Printf.sprintf "%s: %d" reason count in
    let str = Print.enum_to_string ~enclosing:("", "") ~sep:"\n\t" to_s
      (StringHtbl.enum failures) in
    Printf.sprintf "%s: analyzed %d/%d (%0.2f%%)\n\t%s\n"
      name n_analyzed n_total
      ((100. *. (float_of_int n_analyzed)) /. (float_of_int n_total))
      str
  method sexp_of_t =
    let open Sexplib in
    let r2sexp (str, num) = Sexp.List [Sexp.Atom str; Std.sexp_of_int num] in
    let reasons = Std.sexp_of_list r2sexp (BatList.of_enum (StringHtbl.enum failures)) in
    Sexp.List [Sexp.of_string name; Std.sexp_of_int n_analyzed; Std.sexp_of_int n_total; reasons]
end
