module VH = Var.VarHash
module VS = Var.VarSet

let list_of_hash vh =
  VH.fold (fun k v r -> k :: r) vh []

let set_of_list =
  List.fold_left (fun s e -> VS.add e s) VS.empty

module NormalizableVar : sig
    type t

    val bind : t -> (Var.t -> t) -> t
    val return : Var.t -> t

    val to_v : t -> Var.t
end = struct
    type t = Normalized of Var.t | Preserved of Var.t

    let bind t f = match t with
      | Preserved v -> f v
      | Normalized _ -> t

    let return v = Preserved v
    let to_v = function | Preserved v | Normalized v -> v
end

module Array : sig
  val global_array_base : Var.t

  val is_mem : Var.t -> bool
  val is_array : Var.t -> bool
  val base_reg : Var.t -> Var.t
  val bounds : Var.t -> Interval.Big_int.t
  val size : Var.t -> Big_int_Z.big_int
  val is_global_ary : Var.t -> bool
  val of_var: Var.t -> int64 -> int64 -> Var.t
end
=
struct
  exception Invalid_array of string

  let global_array_base = Var.newvar "global" (Type.Reg 32)

  let parse ary =
    let ary_descr = Var.name ary in
    let regexp = Str.regexp "^ary_\\([A-Za-z_]+\\)_\\([0-9]+\\):u32_f\\(-?[0-9]+\\)t\\(-?[0-9]+\\)$" in
    if Str.string_match regexp ary_descr 0
    then
      begin
        let regname = Str.matched_group 1 ary_descr in
        let regidx = int_of_string (Str.matched_group 2 ary_descr) in
        let basereg = Var.construct regidx regname (Type.Reg 32) in
        let lower_bound = Big_int_Z.big_int_of_string (Str.matched_group 3 ary_descr) in
        let upper_bound = Big_int_Z.big_int_of_string (Str.matched_group 4 ary_descr) in
        (basereg, Interval.Big_int.create lower_bound upper_bound)
        end
    else raise (Invalid_array ary_descr)

  let is_mem v =
    match Var.typ v with
    | Type.TMem _ -> true
    | _ -> false

  let is_array v =
    try
      match Var.typ v with
      | Type.Reg _
      | Type.TMem _ ->
        false
      | Type.Array _ ->
        ignore(parse v);
        true
    with Invalid_array _ -> false

  let base_reg ary =
    fst (parse ary)

  let bounds ary =
    snd (parse ary)

  let size ary =
    let open Big_int_convenience in
    let interval = bounds ary in
    match Interval.Big_int.begin_ interval, Interval.Big_int.end_ interval with
    | None, None -> bi0
    | Some _, None
    | None, Some _ -> failwith "Interval only has one endpoint, lolwut"
    | Some low, Some high -> high -% low

  let is_global_ary ary =
    let base = base_reg ary in
    Var.equal base global_array_base

  let of_var var low high =
    let Var.V (vidx, vname, vtyp) = var in
    let typ = Pp.typ_to_string vtyp in
    let name = Printf.sprintf "ary_%s_%d:%s_f%Ldt%Ld" vname vidx typ low high in
    Var.construct 0 name (Type.Array (Type.Reg 32, Type.Reg 8))
end

let enable_varnums =
  let prev = !Pp.output_varnums in
  Pp.output_varnums := true;
  prev

let restore_varnums state =
  Pp.output_varnums := state
