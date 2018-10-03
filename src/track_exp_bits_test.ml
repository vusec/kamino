open Track_exp_bits
open BatPervasives

let arch_decls = Asmir.decls_for_arch Asmir.arch_i386
let eax = List.find (fun v -> Var.name v = "R_EAX") arch_decls
let ebx = List.find (fun v -> Var.name v = "R_EBX") arch_decls
let ecx = List.find (fun v -> Var.name v = "R_ECX") arch_decls
let edx = List.find (fun v -> Var.name v = "R_EDX") arch_decls

let use_to_s (v, bit_low, bits) =
  Printf.sprintf "%s:[%d, %d]" (Var.name v) bit_low bits

let uses_to_s uses =
  List.map use_to_s uses |> BatString.concat ", "

let cmp_use (v1, bit_low1, bits1) (v2, bit_low2, bits2) =
  let ret = Var.compare v1 v2 in
  if ret = 0 then begin
    let ret = bit_low1 - bit_low2 in
    if ret = 0 then begin
      bits1 - bits2
    end else begin
      ret
    end
  end else begin
    ret
  end

type testcase = {
  exp : Ast.exp;
  uses : (Var.t * int * int) list;
}

let show_mismatch ~got ~expected =
  Printf.eprintf "Variable use mismatch\n";
  Printf.eprintf "got:      %s\n" (uses_to_s got);
  Printf.eprintf "expected: %s\n" (uses_to_s expected)

let compare_uses ~got ~expected =
  try
    List.iter2 (fun u1 u2 ->
        if cmp_use u1 u2 <> 0 then begin
          Printf.eprintf "Uses differ: %s vs %s\n" (use_to_s u1) (use_to_s u2);
          raise (Invalid_argument "difference")
        end) got expected;
    BatResult.Ok ()
  with Invalid_argument _ ->
    show_mismatch ~got ~expected;
    BatResult.Bad ()

let do_test test =
  let got = exp_uses_tuple test.exp in
  let got = List.sort cmp_use got in
  let expected = List.sort cmp_use test.uses in
  compare_uses ~got ~expected

let bi8 = Big_int_Z.big_int_of_int 8
let bi15 = Big_int_Z.big_int_of_int 15
let bi31 = Big_int_Z.big_int_of_int 31
let biff = Big_int_Z.big_int_of_int 0xff
let bif00f = Big_int_Z.big_int_of_int 0xf00f

let tests =
  [
    {
      exp = Ast.Cast (Type.CAST_LOW, Type.Reg 8, Ast.Var eax);
      uses = [(eax, 0, 8)];
    };
    {
      exp = Ast.Concat (Ast.Extract (bi31, bi8, Ast.Var eax),
                        Ast.BinOp (Type.XOR,
                                   Ast.Cast (Type.CAST_LOW, Type.Reg 8, Ast.Var eax),
                                   Ast.Cast (Type.CAST_HIGH, Type.Reg 8, Ast.Var ebx)));
      uses = [(eax, 0, 32); (ebx, 24, 8);];
    };
    {
      exp = Ast.Concat (Ast.Extract (bi31, bi8, Ast.Var eax),
                        Ast.Cast (Type.CAST_LOW, Type.Reg 8, Ast.Var eax));
      uses = [(eax, 0, 32)];
    };
    {
      exp = Ast.Concat (Ast.Cast (Type.CAST_UNSIGNED, Type.Reg 16,
                                  Ast.Cast (Type.CAST_LOW, Type.Reg 8, Ast.Var eax)),
                        Ast.Cast (Type.CAST_SIGNED, Type.Reg 16,
                                  Ast.Extract (bi15, bi8, Ast.Var ebx)));
      uses = [(eax, 0, 8); (ebx, 8, 8);];
    };
    {
      exp = Ast.BinOp (Type.AND, Ast.Var eax, Ast.Int (biff, Type.Reg 32));
      uses = [(eax, 0, 8);];
    };
    {
      exp = Ast.BinOp (Type.AND, Ast.Var eax, Ast.Int (bif00f, Type.Reg 32));
      uses = [(eax, 0, 4); (eax, 12, 4);];
    };
  ]

let () =
  let (successful, total) =
    List.fold_left (fun (successful, total) test ->
        match do_test test with
        | BatResult.Ok () -> (successful + 1, total + 1)
        | BatResult.Bad () -> (successful, total + 1)) (0, 0) tests
  in
  Printf.printf "%d/%d passed\n" successful total;
  let ecode = if successful < total then 3 else 0 in
  exit ecode
