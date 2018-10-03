module Tree = Imtree.Tree(Int64)

let build_tree intervals =
  let open Int64 in
  List.fold_left (fun tree (low, high) ->
    Tree.insert tree (of_int low, of_int high)) Tree.empty intervals

let test_tree (intervals, expected) =
  let tree = build_tree intervals in
  let treestr = Tree.to_string tree in
  if (String.compare treestr expected) <> 0 then begin
    Printf.eprintf "Trees differ:\nexpected: %s\ngot: %s\n"
      expected treestr;
    failwith "Tree mismatch"
  end
  
let test_trees =
  [
    (* Whitespace matters! *)
    ([(0, 4); (5, 6);], "[(0, 4); (5, 6)]");
    ([(0, 4); (4, 6);], "[(0, 6)]");
    ([(0, 4); (7, 8); (4, 7);], "[(0, 8)]");
    ([(0, 4); (8, 9); (10, 12); (14, 15); (1, 62);], "[(0, 62)]");
  ]

let () =
  List.iter test_tree test_trees;
  Printf.printf "Successfully executed %d tests\n" (List.length test_trees)
