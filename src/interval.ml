(* Interval module from RealWorld Ocaml*)

module type EndpointSig =
sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
  val add : t -> t -> t
end

module type S =
sig
  type t
  type endpoint

  val create : endpoint -> endpoint -> t
  val empty : t
  val is_empty : t -> bool
  val begin_ : t -> endpoint option
  val end_ : t -> endpoint option
  val equal : t -> t -> bool
  val contains : t -> endpoint -> bool
  val intersect : t -> t -> t
  val strictly_below : below:t -> above:t -> bool
  val strictly_above :  above:t -> below:t -> bool
  val translate : t -> endpoint -> t
  val to_string : t -> string
  val sexp_of_t : t -> Sexplib.Sexp.t
end

module Make_interval (Endpoint : EndpointSig) : S with type endpoint := Endpoint.t =
struct
  type t = Interval of Endpoint.t * Endpoint.t | Empty

  (* TODO: use low/high labels here so we can't mix'em up *)
  let create low high =
    if Endpoint.compare low high > 0 then Empty
    else Interval (low, high)

  let empty = Empty

  let is_empty = function
    | Empty -> true
    | Interval _ -> false

  let begin_ = function
    | Empty -> None
    | Interval (l,_) -> Some l
  let end_ = function
    | Empty -> None
    | Interval (_,h) -> Some h

  let equal t1 t2 =
    match (t1, t2) with
    | Empty, Empty -> true
    | Empty, _
    | _, Empty -> false
    | Interval (l1, h1), Interval (l2, h2) when (l1 = l2) && (h1 = h2) -> true
    | _ -> false

  let contains t x =
    match t with
    | Empty -> false
    | Interval (l, h) -> Endpoint.compare l x <= 0 && Endpoint.compare x h <= 0

  let intersect t1 t2 =
    let min x y = if Endpoint.compare x y <= 0 then x else y in
    let max x y = if Endpoint.compare x y > 0 then x else y in
    match t1,t2 with
    | Empty,_ | _,Empty -> Empty
    | Interval (l1, h1), Interval (l2, h2) -> create (max l1 l2) (min h1 h2)

  let strictly_below ~below ~above =
    end_ below < begin_ above

  let strictly_above ~above ~below =
    begin_ above > end_ below

  let translate t move =
    match t with
    | Empty ->
      failwith "Tried to translate empty Interval"
    | Interval (l, h) ->
      (* Move can of course be negative *)
      Interval (Endpoint.add l move, Endpoint.add h move)

  let to_string = function
    | Interval (b, e) -> Printf.sprintf "[%s, %s]" (Endpoint.to_string b)
      (Endpoint.to_string e)
    | Empty -> "<empty>"
  let sexp_of_t t =
    let open Sexplib in
    let s ep = Sexp.of_string (Endpoint.to_string ep) in
    match t with
    | Empty -> Sexp.List []
    | Interval (l, h) -> Sexp.List [s l; s h;]
end

module Address_interval = Make_interval (
     struct
       type t = Type.addr
       let compare = Int64.compare
       let to_string = Int64.to_string
       let add = Int64.add
     end)

module Function_interval = Address_interval
module Section_interval = Address_interval

module Big_int = Make_interval (
  struct
    type t = Big_int_Z.big_int
    let compare = Big_int_Z.compare_big_int
    let to_string = Big_int_Z.string_of_big_int
    let add = Big_int_Z.add_big_int
  end
)
