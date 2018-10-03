open OUnit
open BatPervasives

module OUnitExt
= struct
  let raises f =
    try
      f ();
      None
    with e ->
      Some e

  let assert_not_raises ?msg exn (f: unit -> 'a) =
    let pexn = Printexc.to_string in
    let get_error_string () =
      let str =
        Format.sprintf
          "didn't expected exception %s, but exception was raised."
          (pexn exn)
      in
      match msg with
      | None ->
        assert_failure str

      | Some s ->
        assert_failure (Format.sprintf "%s\n%s" s str)
    in
    match raises f with
    | None ->
      ()
    | Some e ->
      if exn = e
      then assert_failure (get_error_string ())
      else ()
end

module Helpers =
struct
  let no_implementation () =
    skip_if true "No implementation to pass the test case."

  let always_fail () =
    assert_bool "Always fail" false

  let program_from_string ?(scope=Grammar_private_scope.default_scope ()) s =
    Parser.program_from_lexbuf (Lexing.from_string s) ~scope

  let program_from_list ?(scope=Grammar_private_scope.default_scope ()) l =
    program_from_string ~scope (String.concat "\n" l)

  (* XXX: this assumes only one basic block with statements*)
  let ast2ssa ast =
    let pipeline_name = "transfer_function_test_pipeline" in
    let g = Cfg_ssa.of_ast ast in
    let _,g' = List.fold_left (fun (ctx, g) pass ->
        Analysis_pass.apply_ssa_cfg_pass ~pipeline_name ~keypref:(Some "TF") ctx "ast2ssa" g pass)
        (Analysis_pass.default_pipeline_ctx, g)
        (List.map Analysis_pass.make_pass [`ComputeDataDependencies;
                                           `ComputeFunctionInputs;
                                           `RewriteLoadStores;
                                           `ComputeDataDependencies;
                                           `ComputeCollapsibleLoads;
                                           `CollapseLoads;
                                          ])
    in
    (* BB_Entry -> BB -> BB_Exit *)
    if (Cfg.SSA.G.nb_vertex g') = 3
    then
      begin
        let entry = Cfg.SSA.find_vertex g' Cfg.BB_Entry in
        let succ = Cfg.SSA.G.succ g' entry in
        if (List.length succ) = 1
        then Cfg.SSA.get_stmts g' (List.hd succ)
        else failwith "Unexpected number of successors ast to ssa conversion!"
      end
    else failwith "Unexpected number of BBs in ast to ssa conversion!"

  let compute_tf p =
    let p' = Ssa_ext.of_prog (ast2ssa p) in
    Transfer_function.compute_for_bb p'

  let expect_incomputable ?(msg="Expected an incomputable exception for an irreducible store and load sequence") p =
    let raises () = compute_tf p in
    assert_raises ~msg (Transfer_function.Incomputable "Irreducible store and load sequence") raises

  let expect_computable ?(msg="Expected a computable transfer function") p =
    let raises () = compute_tf p in
    OUnitExt.assert_not_raises ~msg (Transfer_function.Incomputable "Irreducible store and load sequence") raises

  let value_of_string s =
    let i = Big_int_Z.big_int_of_string s in
    Ssa_ext.Value.Int (i, Type.Reg 32 )
end

module Tests =
struct
  module Incomputable =
  struct
    let irreducable_store_load () =
      let p,_ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[R_EBP:u32, e_little]:u32";
        ] in
      Helpers.expect_incomputable p

    let overlapping_store_load_1 () =
      let p,_ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [R_EDX:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[R_EDX:u32 + 2:u32, e_little]:u32";
        ] in
      Helpers.expect_incomputable p

    let overlapping_global_store_load_1 () =
      let p, _ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [0x80000000:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[0x7FFFFFFF:u32, e_little]:u32";
        ]
      in
      Helpers.expect_incomputable ~msg:"Expected an incomputable exception for an overlapping global store and load" p

    let overlapping_global_store_load_2 () =
      let p, _ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [0x80000000:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[0x80000000:u32, e_little]:u32";
        ]
      in
      Helpers.expect_computable p

    let overlapping_global_store_load_3 () =
      let p, _ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [0x80000000:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[0x80000002:u32, e_little]:u32";
        ]
      in
      Helpers.expect_incomputable ~msg:"Expected an incomputable exception for an overlapping global store and load" p

    let mem_store_before_array_load () =
      let p, _ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [R_EAX:u32 - R_EBX:u32, e_little]:u32 = 0x1:u32";
          "R_ECX:u32 = mem:?u32[R_ESP:u32 - 0x4:u32, e_little]:u32";
        ]
      in
      Helpers.expect_incomputable ~msg:"Expected an incomputable exception for a memory store before array load" p

    let array_store_before_mem_load () =
      let p, _ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [R_ESP:u32 - 0x4:u32, e_little]:u32 = 0x1:u32";
          "R_ECX:u32 = mem:?u32[R_EAX:u32 - R_EBX:u32, e_little]:u32";
        ]
      in
      Helpers.expect_incomputable ~msg:"Expected an incomputable exception for a memory store before array load" p
  end

  module Computable =
  struct
    let overlapping_store_load_1 () =
      let p,_ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [R_EDX:u32 + 8:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[R_EDX:u32 + 8:u32, e_little]:u32";
        ] in
    Helpers.expect_computable p

    let non_overlapping_store_load_1 () =
      let p,_ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [R_EDX:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[R_EDX:u32 + 4:u32 + 8:u32, e_little]:u32";
        ] in
      Helpers.expect_computable p

    let non_overlapping_global_store_load_1 () =
      let p, _ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [0x80000000:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = pad:u32(mem:?u32[0x7FFFFFFF:u32, e_little]:u8)";
        ]
      in
      Helpers.expect_computable p

    let non_overlapping_global_store_load_2 () =
      let p, _ = Helpers.program_from_list [
          "mem:?u32 = mem:?u32 with [0x80000000:u32, e_little]:u32 = R_EAX:u32";
          "R_EAX:u32 = mem:?u32[0x80000004:u32, e_little]:u32";
        ]
      in
      Helpers.expect_computable p

    let array_load_before_mem_load () =
      let p,_ = Helpers.program_from_list [
          "R_EAX:u32 = mem:?u32[R_ESP:u32 - 0x4:u32, e_little]:u32";
          "R_EBX:u32 = mem:?u32[R_ECX:u32 - R_EDX:u32, e_little]:u32";
        ]
      in
      Helpers.expect_computable p

    let mem_load_before_array_load () =
      let p,_ = Helpers.program_from_list [
          "R_EBX:u32 = mem:?u32[R_ECX:u32 - R_EDX:u32, e_little]:u32";
          "R_EAX:u32 = mem:?u32[R_ESP:u32 - 0x4:u32, e_little]:u32";
        ]
      in
      Helpers.expect_computable p

    let array_load_before_array_store () =
      let p,_ = Helpers.program_from_list [
          "R_EBX:u32 = mem:?u32[R_ESP:u32 - 0x4:u32, e_little]:u32";
          "mem:?u32 = mem:?u32 with [R_ESP:u32 - 0x4:u32, e_little]:u32 = 0x1:u32";
        ]
      in
      Helpers.expect_computable p

    let mem_load_before_mem_store () =
      let p,_ = Helpers.program_from_list [
          "R_EBX:u32 = mem:?u32[R_EAX:u32 - R_ECX:u32, e_little]:u32";
          "mem:?u32 = mem:?u32 with [R_EAX:u32 - R_ECX:u32, e_little]:u32 = 0x1:u32";
        ]
      in
      Helpers.expect_computable p
  end

  module Misc =
  struct
    let no_inputs () =
      Helpers.no_implementation ();
  end
end

let suite =
  "suite" >::: [
    "Incomputable" >::: [
      (*
       * XXX: These all need to be redone.
      *)
(*
      "irreducable_store_load" >:: Tests.Incomputable.irreducable_store_load;
      "overlapping_store_load_1" >:: Tests.Incomputable.overlapping_store_load_1;
      "overlapping_global_store_load_1" >:: Tests.Incomputable.overlapping_global_store_load_1;
      "overlapping_global_store_load_2" >:: Tests.Incomputable.overlapping_global_store_load_2;
      "overlapping_global_store_load_3" >:: Tests.Incomputable.overlapping_global_store_load_3;
      "mem_store_before_array_load" >:: Tests.Incomputable.mem_store_before_array_load;
      "array_store_before_mem_load" >:: Tests.Incomputable.array_store_before_mem_load;
*)
    ];
    "Computable" >::: [
(*
      "overlapping_store_load_1" >:: Tests.Computable.overlapping_store_load_1;
      "non_overlapping_store_load_1" >:: Tests.Computable.non_overlapping_store_load_1;
      "non_overlapping_global_store_load_1" >:: Tests.Computable.non_overlapping_global_store_load_1;
      "non_overlapping_global_store_load_2" >:: Tests.Computable.non_overlapping_global_store_load_2;
      "array_load_before_mem_load" >:: Tests.Computable.array_load_before_mem_load;
      "mem_load_before_array_load" >:: Tests.Computable.mem_load_before_array_load;
      "array_load_before_array_store" >:: Tests.Computable.array_load_before_array_store;
      "mem_load_before_mem_store" >:: Tests.Computable.mem_load_before_mem_store;
*)
    ];
    "Misc" >::: [
(*      "no_inputs" >:: Tests.Misc.no_inputs; *)
    ]
  ]

let () =
  Outdir.set_outdir "deleteme-transfer-function";
  ignore(run_test_tt_main suite)
