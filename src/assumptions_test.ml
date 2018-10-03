module D = Debug.Make(struct let name = "Assumptions_test" and default=`NoDebug end)
open D

open Ssa_ext

type desc = (Variable.t list * Variable.t list) list

type expected_result_merge =
| MergeGolden of desc
| MergeVerifier of (Assumptions.t -> (unit, string) BatResult.t)
| MergeConflict

type expected_result_simplification =
| SimplifiedGolden of desc * desc
| SimplifiedVerifier of (Assumptions.t * Assumptions.t -> (unit, string) BatResult.t)
| SimplifiedConflict


type 'res testcase = {
  asxs1 : desc;
  asxs2 : desc;
  expected: 'res
}

type testcase_merge = expected_result_merge testcase
type testcase_simplification = expected_result_simplification testcase

let seed = ref 0

let a = Variable.Var (Var.newvar "a" (Type.Reg 8), [])
let b = Variable.Var (Var.newvar "b" (Type.Reg 8), [])
let c = Variable.Var (Var.newvar "c" (Type.Reg 8), [])
let d = Variable.Var (Var.newvar "d" (Type.Reg 8), [])
let e = Variable.Var (Var.newvar "e" (Type.Reg 8), [])
let f = Variable.Var (Var.newvar "f" (Type.Reg 8), [])
let g = Variable.Var (Var.newvar "g" (Type.Reg 8), [])
let h = Variable.Var (Var.newvar "h" (Type.Reg 8), [])
let i = Variable.Var (Var.newvar "i" (Type.Reg 8), [])
let j = Variable.Var (Var.newvar "j" (Type.Reg 8), [])
let k = Variable.Var (Var.newvar "k" (Type.Reg 8), [])
let l = Variable.Var (Var.newvar "l" (Type.Reg 8), [])
let m = Variable.Var (Var.newvar "m" (Type.Reg 8), [])
let n = Variable.Var (Var.newvar "n" (Type.Reg 8), [])
let o = Variable.Var (Var.newvar "o" (Type.Reg 8), [])
let p = Variable.Var (Var.newvar "p" (Type.Reg 8), [])
let q = Variable.Var (Var.newvar "q" (Type.Reg 8), [])
let r = Variable.Var (Var.newvar "r" (Type.Reg 8), [])
let s = Variable.Var (Var.newvar "s" (Type.Reg 8), [])
let t = Variable.Var (Var.newvar "t" (Type.Reg 8), [])
let u = Variable.Var (Var.newvar "u" (Type.Reg 8), [])
let v = Variable.Var (Var.newvar "v" (Type.Reg 8), [])
let w = Variable.Var (Var.newvar "w" (Type.Reg 8), [])
let x = Variable.Var (Var.newvar "x" (Type.Reg 8), [])
let y = Variable.Var (Var.newvar "y" (Type.Reg 8), [])
let z = Variable.Var (Var.newvar "z" (Type.Reg 8), [])

let merge_testcases = [
  {
    asxs1 = [
    ];
    asxs2 = [
    ];
    expected = MergeGolden [
    ];
  };
  {
    asxs1 = [];
    asxs2 = [([a], [b])];
    expected = MergeGolden [
      ([a], [b]);
    ];
  };
  {
    asxs1 = [
      ([a; b; c; r], [d; e; f; s]);
      ([g], [h]);
    ];
    asxs2 = [
      ([a; k], [e; l]);
      ([g; x], [h; y]);
      ([r], [s]);
    ];
    expected = MergeGolden [
      ([a], [e]);
      ([b; c], [d; f]);
      ([g], [h]);
      ([k], [l]);
      ([r], [s]);
      ([x], [y]);
    ];
  };
  {
    asxs1 = [
      ([a], [b]);
      ([c; d], [e; f]);
      ([g; h], [i; j]);
      ([k], [l]);
      ([m], [n]);
      ([o], [p]);
      ([q], [r]);
    ];
    asxs2 = [
      ([g; h], [i; j]);
    ];
    expected = MergeGolden [
      ([a], [b]);
      ([c; d], [e; f]);
      ([g; h], [i; j]);
      ([k], [l]);
      ([m], [n]);
      ([o], [p]);
      ([q], [r]);
    ];
  };
  {
    asxs1 = [
      ([a], [b]);
    ];
    asxs2 = [
      ([a], [c]);
    ];
    expected = MergeConflict;
  };
]

let simplification_testcases = [
  {
    asxs1 = [
    ];
    asxs2 = [
    ];
    expected = SimplifiedGolden ([], []);
  };
  {
    asxs1 = [];
    asxs2 = [([a], [b])];
    expected = SimplifiedGolden
      (
	[],
	[
	  ([a], [b])
	]
      );
  };
  {
    asxs1 = [
      ([a; b; c; r], [d; e; f; s]);
      ([g], [h]);
    ];
    asxs2 = [
      ([a; k], [e; l]);
      ([g; x], [h; y]);
    ];
    expected = SimplifiedGolden
      (
	[
	  ([a], [e]);
	  ([g], [h]);
	  ([b; c; r], [d; f; s]);
	],
	[
	  ([a], [e]);
	  ([k], [l]);
	  ([g], [h]);
	  ([x], [y]);
	]
      );
  };
]

let all_vars = [|a; b; c; d; e; f; g; h; i; j; k; l; m;
		 n; o; p; q; r; s; t; u; v; w; x; y; z;|]

(*
 * Given an array of available variables, return a list
 * of random pairings.
 *)
let base_assumptions vars =
  let shuffled = BatRandom.shuffle (BatArray.enum vars) in
  let n = Array.length shuffled in
  assert((n mod 2) = 0);
  let low = Array.sub shuffled 0 (n / 2) in
  let high = Array.sub shuffled (n / 2) (n / 2) in
  assert((Array.length low) = (Array.length high));
  BatArray.map2 (fun a b -> (a, b)) low high


let pairs_ary_to_list_pair pa =
  BatList.split (Array.to_list pa)

(*
 * Given some available 1-to-1 pairings of variables,
 * generate randomly-sized sets of assumptions.
 *)
let build_asxs avail =
  let n = Array.length avail in
  let finished = ref false in
  let idx = ref 0 in
  let ret = ref [] in
  while not !finished do
    (* notice that 0 is not acceptable *)
    let r = ref ((BatRandom.int (n - 1)) + 1) in
    if (!r + !idx) > n then
      r := n - !idx;
    let pick = Array.sub avail !idx !r in
    ret := (pairs_ary_to_list_pair pick)::(!ret);
    idx := !idx + !r;
    assert(!idx <= n);
    if !idx == n then
      finished := true;
  done;
  !ret

(*
 * Test the result of a merge against the 1-to-1 assumptions we used to
 * formulate the left and right hand side sets of assumptions. This will
 * only catch blatant inconsistencies, of course. TBD: make this smarter!
 *)
let trivially_check_assumptions assumptions res =
  let check_assumption (a, b) =
    Assumptions.verify_against_single res (a, b)
  in
  let ret = List.map check_assumption assumptions in
  (* any badness means total badness *)
  BatList.reduce (fun so_far el ->
      match so_far with
      | BatResult.Bad _ as r -> r
      | BatResult.Ok () -> el) ret

let break_merge asxdesc2 =
  let open BatPervasives in

  (* Note: ATM we expect asxdesc1 and asxdesc2 are the same *)
  let n = List.length asxdesc2 in
  let ary2 = Array.of_list asxdesc2 in

  let asms_swap_elements (x, set1) (y, set2) =
    let set1 = Array.of_list set1 in
    let set2 = Array.of_list set2 in
    let victim1 = BatRandom.int (Array.length set1) in
    let victim2 = BatRandom.int (Array.length set2) in
    let a = Array.get set1 victim1 in
    let b = Array.get set2 victim2 in
    Array.set set1 victim1 b;
    Array.set set2 victim2 a;
    ((x, Array.to_list set1), (y, Array.to_list set2))
  in
  let asms_dup_element (x, set1) (y, set2) =
    let set1 = Array.of_list set1 in
    let set2 = Array.of_list set2 in
    let victim1 = BatRandom.int (Array.length set1) in
    let victim2 = BatRandom.int (Array.length set2) in
    let a = Array.get set1 victim1 in
    Array.set set2 victim2 a;
    ((x, Array.to_list set1), (y, Array.to_list set2))
  in
  let change_two_asms op =
    let victim1 = BatRandom.int n in
    let victim2 = (victim1 + 1) mod n in
    let asm1 = Array.get ary2 victim1 in
    let asm2 = Array.get ary2 victim2 in
    let (asm1, asm2) = op asm1 asm2 in
    Array.set ary2 victim1 asm1;
    Array.set ary2 victim2 asm2
  in
  dprintf "break_merge: asxdesc2:\n%s\n" (asxdesc2 |> Assumptions.of_desc |> Assumptions.to_string);
  ignore(match BatRandom.int 2 with
  | 0 ->
    (* {a, e} <-> {b, f}; {c, g} <-> {d, h} ->

       {a, e} <-> {d, f}; {c, g} <-> {b, h}
       or
       {a, e} <-> {b, d}; {c, g} <-> {f, h}
    *)
    dprintf "break_merge: swap elements";
    change_two_asms asms_swap_elements
  | 1 ->
    (* {a, b} <-> {c, d}; {e, f} <-> {g, h} ->

       {a, b} <-> {c, d}; {e, f} <-> {d, h}
       or
       {a, b} <-> {c, d}; {e, f} <-> {g, d}
    *)
    dprintf "break_merge: dup element";
    change_two_asms asms_dup_element
  | _ -> failwith "screwup in break_assumptions");
  let ret = Array.to_list ary2 in
  dprintf "break_merge: ret:\n%s\n" (ret |> Assumptions.of_desc |> Assumptions.to_string);
  ret

let gen_random_testcase vars =
  let open BatPervasives in
  dprintf "TESTCASE\n";
  let maybe_break x inval =
    match inval with
    | true -> break_merge x
    | false -> x
  in
  let inval = BatRandom.bool () in
  let avail1 = base_assumptions vars in
  let a = build_asxs avail1 in
  let b' = a in
  dprintf "a:\n%s\n" (a |> Assumptions.of_desc |> Assumptions.to_string);
  dprintf "b':\n%s\n" (b' |> Assumptions.of_desc |> Assumptions.to_string);
  let b = maybe_break b' inval in
  dprintf "b:\n%s\n" (b |> Assumptions.of_desc |> Assumptions.to_string);
  let exp = List.map (fun (a, b) ->
    (a, b)) (Array.to_list avail1) in
  if inval then
    {asxs1 = a; asxs2 = b; expected = MergeConflict}
  else
    {asxs1 = a; asxs2 = b; expected = MergeVerifier (trivially_check_assumptions exp)}

let do_test_merge tc =
  let asxs1 = Assumptions.of_desc tc.asxs1 in
  let asxs2 = Assumptions.of_desc tc.asxs2 in
  let str1 = Assumptions.to_string asxs1 in
  let str2 = Assumptions.to_string asxs2 in
  let describe () =
    Printf.printf "-- 1\n%s\n-- 2\n%s\n" str1 str2
  in
  try
    if debug () then
      describe();
    let ret = Assumptions.merge_equivs asxs1 asxs2 in
    match (ret, tc.expected) with
    | (BatResult.Ok res, MergeGolden exp) ->
      let asxs_expected = Assumptions.of_desc exp in
      if 0 = (Assumptions.compare res asxs_expected) then
	Printf.printf "SUCCESS: matches expected result\n"
      else begin
	describe ();
	Printf.printf "==\n%s\n" (Assumptions.to_string res);
	Printf.printf "FAIL: expected\n--%s" (Assumptions.to_string asxs_expected);
	failwith "Failed to match against expected result"
      end
    | (BatResult.Ok res, MergeVerifier verifier) ->
      (match verifier res with
      | BatResult.Ok () ->
	Printf.printf "SUCCESS: verified result\n"
      | BatResult.Bad err ->
	describe ();
	Printf.printf "FAIL: verification failed: %s" err;
	failwith "Failed to verify testcase")
    | (BatResult.Ok res, MergeConflict) ->
      describe();
      Printf.printf "FAIL: expected conflict but got ==\n%s\n" (Assumptions.to_string res);
      failwith "Failed to detect conflict"
    | (BatResult.Bad str, MergeGolden _)
    | (BatResult.Bad str, MergeVerifier _) ->
      describe ();
      Printf.printf "FAIL: unexpected conflict: %s\n" str;
      failwith "Failed to merge properly"
    | (BatResult.Bad _, MergeConflict) ->
      Printf.printf "SUCCESS: got conflict as expected\n"
  with e ->
    Printf.printf "Exception while merging the following:\n";
    describe ();
    raise e

let random_test_valid n =
  let testcases = BatEnum.from (fun () -> gen_random_testcase all_vars) in
  (* Ugh. This seems to generate the testcases eagerly. Why? *)
  BatEnum.iter do_test_merge (BatEnum.take n testcases)

let do_test_simplification tc =
  let asxs1 = Assumptions.of_desc tc.asxs1 in
  let asxs2 = Assumptions.of_desc tc.asxs2 in
  let str1 = Assumptions.to_string asxs1 in
  let str2 = Assumptions.to_string asxs2 in
  let describe () =
    Printf.printf "-- 1\n%s\n-- 2\n%s\n" str1 str2
  in
  try
    if debug () then
      describe();
    let ret = Assumptions.simplify_asxs asxs1 asxs2 in
    match (ret, tc.expected) with
    | (BatResult.Ok (res1, res2), SimplifiedGolden (exp1, exp2)) ->
      let asxs_expected1 = Assumptions.of_desc exp1 in
      let asxs_expected2 = Assumptions.of_desc exp2 in
      if (0 = (Assumptions.compare res1 asxs_expected1)) &&
	(0 = (Assumptions.compare res2 asxs_expected2)) then
	Printf.printf "SUCCESS: matches expected result\n"
      else begin
	describe ();
	Printf.printf "==1\n%s\n==2\n%s\n"
	  (Assumptions.to_string res1) (Assumptions.to_string res2);
	Printf.printf "FAIL: expected\n--1%s\n--2\n%s\n"
	  (Assumptions.to_string asxs_expected1)
	  (Assumptions.to_string asxs_expected2);
	failwith "Failed to match against expected result"
      end
    | (BatResult.Ok res, SimplifiedVerifier verifier) ->
      (match verifier res with
      | BatResult.Ok () ->
	Printf.printf "SUCCESS: verified result\n"
      | BatResult.Bad err ->
	describe ();
	Printf.printf "FAIL: verification failed: %s" err;
	failwith "Failed to verify testcase")
    | (BatResult.Ok (res1, res2), SimplifiedConflict) ->
      describe();
      Printf.printf "FAIL: expected conflict but got ==1\n%s\n--2\n%s\n"
	(Assumptions.to_string res1) (Assumptions.to_string res1);
      failwith "Failed to detect conflict"
    | (BatResult.Bad str, SimplifiedGolden _)
    | (BatResult.Bad str, SimplifiedVerifier _) ->
      describe ();
      Printf.printf "FAIL: unexpected conflict: %s\n" str;
      failwith "Failed to simplify properly"
    | (BatResult.Bad _, SimplifiedConflict) ->
      Printf.printf "SUCCESS: got conflict as expected\n"
  with e ->
    Printf.printf "Exception while simplifying the following:\n";
    describe ();
    Printf.eprintf "%s\n" (Printexc.to_string e);
    raise e


let get_random_seed () =
  let f = open_in "/dev/urandom" in
  input_binary_int f

let () =
  Printexc.record_backtrace true;
  seed := get_random_seed ();
  let argv = Array.length (Sys.argv) in
  if argv > 2 then begin
    Printf.eprintf "Too many arguments\n";
    exit(2)
  end else begin
    if argv = 2 then
      seed := int_of_string Sys.argv.(1)
  end;
  BatRandom.init !seed;
  Printf.printf "Random seed: %d\n" !seed;
  try
    let nrandom = 1000 in
    List.iter do_test_merge merge_testcases;
    List.iter do_test_simplification simplification_testcases;
    random_test_valid nrandom;
    Printf.printf "Successfully verified %d predetermined \
                   and %d randomly-generated testcases\n"
      (List.length merge_testcases)
      nrandom;
  with e ->
    Printf.eprintf "Random seed: %d\n" !seed;
    Printf.eprintf "%s\n" (Printexc.to_string e)
