module Make (T : Hashtbl.S) = struct
    let keys tbl =
        T.fold (fun k _ acc -> k :: acc) tbl []

    let values tbl =
        T.fold (fun _ v acc -> v :: acc) tbl []

    let filter_by sel pred tbl =
        T.fold (fun k v acc ->
            if pred (sel k v) then T.add acc k v;
            acc ) tbl (T.create (T.length tbl))

    let filter_by_key pred tbl =
        let key k v = k in
        filter_by key pred tbl

    let filter_by_value pred tbl =
        let value k v = v in
        filter_by value pred tbl

    let map f tbl =
        T.fold ( fun k v acc ->
            T.add acc k (f v); acc
            ) tbl (T.create (T.length tbl))

    let merge f t1 t2 =
        T.fold (fun k v acc ->
            if T.mem acc k then T.add acc k (f v (T.find acc k))
            else T.add acc k v;
            acc
            ) t1 t2

    let try_some f = function
        | Some t -> f t
        | None -> T.create 1

    let append tbl k v =
      try
        let l = T.find tbl k in
        let l' = List.rev l in
        T.replace tbl k (List.rev (v :: l'))
      with Not_found ->
        T.add tbl k [v]

    let find_option tbl k =
      try Some (T.find tbl k)
      with Not_found -> None

end

module VH = Make(Var.VarHash)
module VariableHash = Make(Ssa_ext.VariableHash)

let append tbl k v =
  try
    let l = Hashtbl.find tbl k in
    let l' = List.rev l in
    Hashtbl.replace tbl k (List.rev (v :: l'))
  with Not_found ->
    Hashtbl.add tbl k [v]
