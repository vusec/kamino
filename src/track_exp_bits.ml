open BatPervasives

module VarMap = Var.VarMap

let exp_bits e = Typecheck.infer_ast ~check:false e |> Typecheck.bits_of_width

let add_use_of_range var low high acc =
    (var, low, high - low + 1) :: acc

let join uses1 uses2 =
  let f var l r =
    try
      begin
        match (l, r) with
        | None, None -> None
        | Some ranges, None
        | None, Some ranges -> Some ranges
        | Some ranges1, Some ranges2 -> Some (BatISet.union ranges1 ranges2)
      end
    with Not_found ->
      failwith "Key not found in Track_exp_bits.join"
  in
  VarMap.merge f uses1 uses2

let rec exp_uses e =
  let uses = match e with
    | Ast.Load (_, e, _, _) ->
      exp_uses e
    | Ast.BinOp (Type.AND, e, Ast.Int bi)
    | Ast.BinOp (Type.AND, Ast.Int bi, e) ->
      begin
        let uses = exp_uses e in
        let and_ranges = Misc.bi_bit_ranges bi in
        VarMap.map (fun ranges ->
            BatISet.inter ranges and_ranges) uses
      end
    | Ast.Store (_, e1, e2, _, _)
    | Ast.BinOp (_, e1, e2)
    | Ast.Ite (_, e1, e2) ->
      join (exp_uses e1) (exp_uses e2)
    | Ast.UnOp (_, e) ->
      exp_uses e
    | Ast.Lab _
    | Ast.Int _
    | Ast.Unknown _ ->
      VarMap.empty
    | Ast.Let _ ->
      let s = Printf.sprintf "exp_uses can't handle %s" (Pp.ast_exp_to_string e) in
      failwith s
    | Ast.Concat (e1, e2) ->
      (* This is shifting the e1 bits high, but WRT to the inner variable,
       * it doesn't change which bits we're using.
       *)
      join (exp_uses e1) (exp_uses e2)
    | Ast.Extract (high, low, e) ->
      let high = Big_int_Z.int_of_big_int high in
      let low = Big_int_Z.int_of_big_int low in

      let uses = exp_uses e in
      VarMap.map (fun ranges ->
          BatISet.fold_range (fun ulow uhigh acc ->
              let uwidth = uhigh - ulow + 1 in
              if not (high - low <= uwidth) then begin
                failwith (Printf.sprintf "Extract: %d - %d > %d" high low uwidth)
              end;
              let nlow = low + ulow in
              BatISet.add_range nlow (nlow + high - low) acc) ranges BatISet.empty) uses
    | Ast.Cast (cast_type, t, e) ->
      begin
        let uses = exp_uses e in
        let cast_bits = Typecheck.bits_of_width t in
        match cast_type with
        | Type.CAST_UNSIGNED
        | Type.CAST_SIGNED ->
          (* We're still using the same bits from the inner var *)
          uses
        | Type.CAST_HIGH ->
          VarMap.map (fun ranges ->
              BatISet.fold_range (fun low high acc ->
                  let uwidth = high - low + 1 in
                  let nlow = low + uwidth - cast_bits in
                  let nhigh = nlow + cast_bits - 1 in
                  BatISet.add_range nlow nhigh acc) ranges BatISet.empty) uses
        | Type.CAST_LOW ->
          VarMap.map (fun ranges ->
              BatISet.fold_range (fun low high acc ->
                  BatISet.add_range low (low + cast_bits - 1) acc) ranges BatISet.empty) uses
      end
    | Ast.Var v ->
      (* Kick-off. Our callers will narrow down the view into the variable as needed *)
      let width = Var.typ v |> Typecheck.bits_of_width in
      VarMap.singleton v (BatISet.add_range 0 (width - 1) BatISet.empty)
  in
  uses

let exp_uses_tuple e =
  let uses = exp_uses e in
  VarMap.fold (fun var ranges acc ->
      let var_uses = BatISet.fold_range (add_use_of_range var) ranges [] in
      var_uses @ acc) uses []
