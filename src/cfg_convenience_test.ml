open OUnit
open Cfg
open BatPervasives

module Helpers
= struct
  (* Basic block to vertex *)
  let bb2v = SSA.G.V.create
  (* Basic block pair to vertex pair *)
  let bbp2vp (bb, bb') = (bb2v bb, bb2v bb')
  (* List of vertex pairs to SSA cfg *)
  let vpl2g =
    List.fold_left (fun g (bb, bb') ->
        SSA.add_edge (SSA.add_vertex g bb |> (flip SSA.add_vertex) bb') bb bb') (SSA.empty ())
  let add2trace bb trace = trace ^ (SSA.v2s bb)

  let bbl2trace bbl =
    List.fold_left (flip add2trace) "" (List.map bb2v bbl)
end

module Tests
= struct
  let straight () =
    let edges = List.map Helpers.bbp2vp [(BB_Entry, BB 1); (BB 1, BB 2); (BB 2, BB 3); (BB 3, BB_Exit)] in
    let g = Helpers.vpl2g edges in
    let test g direction expected =
      let result = direction Helpers.add2trace g "" in
      assert_equal ~printer:identity expected result in
    let expected = [BB_Entry; BB 1; BB 2; BB 3; BB_Exit] in
    test g Cfg_convenience.SSA.walk_bb_successors_inclusive (Helpers.bbl2trace expected);
    test g Cfg_convenience.SSA.walk_bb_predecessors_inclusive (Helpers.bbl2trace (List.rev expected))


  let if_then_else () =
    let edges = List.map Helpers.bbp2vp [(BB_Entry, BB 1); (BB 1, BB 2); (BB 1, BB 3); (BB 2, BB_Exit); (BB 3, BB_Exit)] in
    let g = Helpers.vpl2g edges in
    let test g direction expected_if expected_else =
      let result = direction Helpers.add2trace g "" in
      let desc = Printf.sprintf "%s = %s || %s = %s" expected_if result expected_else result in
      desc @? ((expected_if = result) || (expected_else = result))
    in
    let if_branch = [BB_Entry; BB 1; BB 2; BB 3; BB_Exit] in
    let else_branch = [BB_Entry; BB 1; BB 3; BB 2; BB_Exit] in
    test g Cfg_convenience.SSA.walk_bb_successors_inclusive (Helpers.bbl2trace if_branch) (Helpers.bbl2trace else_branch);
    test g Cfg_convenience.SSA.walk_bb_predecessors_inclusive (Helpers.bbl2trace (List.rev if_branch))
      (Helpers.bbl2trace (List.rev else_branch))

  let simple_loop () =
    let edges = List.map Helpers.bbp2vp [(BB_Entry, BB 1); (BB 1, BB 2); (BB 2, BB 3); (BB 3, BB 1); (BB 3, BB_Exit)] in
    let g = Helpers.vpl2g edges in
    let test g direction expected =
      let result = direction Helpers.add2trace g "" in
      assert_equal ~printer:identity expected result in
    let expected = [BB_Entry; BB 1; BB 2; BB 3; BB_Exit] in
    test g Cfg_convenience.SSA.walk_bb_successors_inclusive (Helpers.bbl2trace expected);
    test g Cfg_convenience.SSA.walk_bb_predecessors_inclusive (Helpers.bbl2trace (List.rev expected))


  let inner_loop () =
    let edges = List.map Helpers.bbp2vp [
        (BB_Entry, BB 1);
        (BB 1, BB 2);
        (BB 2, BB 3);
        (BB 3, BB 2);
        (BB 3, BB 4);
        (BB 4, BB 1);
        (BB 4, BB_Exit);
      ] in
    let g = Helpers.vpl2g edges in
    let test g direction expected =
      let result = direction Helpers.add2trace g "" in
      assert_equal ~printer:identity expected result in
    let expected = [BB_Entry; BB 1; BB 2; BB 3; BB 4; BB_Exit] in
    test g Cfg_convenience.SSA.walk_bb_successors_inclusive (Helpers.bbl2trace expected);
    test g Cfg_convenience.SSA.walk_bb_predecessors_inclusive (Helpers.bbl2trace (List.rev expected))
end

let suite =
  "suite" >::: [
    "straight" >:: Tests.straight;
    "if_then_else" >:: Tests.if_then_else;
    "simple_loop" >:: Tests.simple_loop;
    "inner_loop" >:: Tests.inner_loop;
  ]

let () = ignore(run_test_tt_main suite)
