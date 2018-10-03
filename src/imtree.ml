module type KeySig
=
sig
  include Map.OrderedType
  val to_string: t -> string
end

(* Let's call this interval merge tree *)
module Tree (Key: KeySig)
=
struct
  module Interval =
  struct
    type t = (Key.t * Key.t)
    let low = fst
    let high = snd
    let of_pair (l, h) =
      if l > h then
	failwith "(l > h)";
      (l, h)
    let to_pair x = x
    let intersect iv1 iv2 =
      ((Key.compare (low iv1) (high iv2)) <= 0) &&
      ((Key.compare (high iv1) (low iv2)) >= 0)
    let merge iv1 iv2 =
      assert(intersect iv1 iv2);
      let nlow =
	if (low iv1) < (low iv2) then
	  (low iv1)
	else
	  (low iv2)
      in
      let nhigh =
	if (high iv1) > (high iv2) then
	  (high iv1)
	else
	  (high iv2)
      in
      (nlow, nhigh)
    let to_string (l, h) =
      Printf.sprintf "(%s, %s)" (Key.to_string l) (Key.to_string h)
  end
  (*
   * No, I'm not really going to implement a real functional
   * tree at this point. Just need something that works.
   *)
  type t = Interval.t list

  let empty = []
  let insert itree interval =
    let interval = Interval.of_pair interval in
    let (rest, n) = List.fold_left (fun (nonintersecting, curr_interval) ival ->
      if Interval.intersect curr_interval ival then
	(nonintersecting, Interval.merge curr_interval ival)
      else
	(ival :: nonintersecting, curr_interval)) ([], interval) itree
    in
    n :: rest
  let to_string itree =
    let nl = List.sort (fun (l1, _) (l2, _) ->
      Key.compare l1 l2) itree
    in
    Print.list_to_string ~enclosing:("[", "]") ~sep:"; " Interval.to_string nl
  let fold_intervals f acc itree =
    List.fold_left (fun ivl -> f (Interval.to_pair ivl)) acc itree
end
