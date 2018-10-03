open Big_int_Z

let bi_is_mask = Misc.bi_is_mask

let do_mask_test ((i, t), mask_bits) =
  let bi = big_int_of_int i in
  match (bi_is_mask (bi, t), mask_bits) with
  | None, None ->
    BatResult.Ok ()
  | None, Some bits ->
    let s = Printf.sprintf "%#x:%s should be a mask:%d but wasn't" i
        (Pp.typ_to_string t) bits in
    BatResult.Bad s
  | Some bits, None ->
    let s = Printf.sprintf "%#x:%s shouldn't be a mask but was (%d)" i
        (Pp.typ_to_string t) bits in
    BatResult.Bad s
  | Some bits_found, Some bits_expected when bits_found <> bits_expected ->
    let s = Printf.sprintf "%#x:%s should be a mask with %d bits but found (%d)" i
        (Pp.typ_to_string t) bits_expected bits_found in
    BatResult.Bad s
  | _ ->
    BatResult.Ok ()

let test f (succeeded, total) tc =
  match f tc with
  | BatResult.Ok () ->
    (succeeded + 1, total + 1)
  | BatResult.Bad str ->
    Printf.eprintf "%s\n" str;
    (succeeded, total + 1)

let mask_tests = [
  ((0xff, Type.Reg 8), Some 8);
  ((0xff, Type.Reg 16), Some 8);
  ((0xf, Type.Reg 32), Some 4);
  ((0xffffffff, Type.Reg 32), Some 32);
  ((0x7fffffff, Type.Reg 31), Some 31);
  ((0x0, Type.Reg 8), None);
  ((0xf0f, Type.Reg 16), None);
]

let () =
  let (succeeded, total) = List.fold_left (test do_mask_test) (0, 0) mask_tests in
  Printf.printf "%d/%d succeeded\n" succeeded total;
  let ecode = if succeeded = total then 0 else 3 in
  exit ecode
