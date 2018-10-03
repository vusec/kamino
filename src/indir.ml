
class type base_indir_type =
  object
    method npairs : int
    method path : string
  end

class type summarized_indir_type =
  object
    inherit base_indir_type
    method nclusters : int
  end

class type completed_indir_type =
  object
    inherit summarized_indir_type
    method success : (unit, string list) BatResult.t
  end

class type successful_indir_type =
  object
    inherit completed_indir_type
    method nresults : int
  end

class base_indir path =
  object
    val batch = Batch.from_file (Printf.sprintf "%s/spec" path)
    val path = path
    method npairs =
      let runs = Batch.runs batch in
      match runs with
      | [] ->
        (* Not a priori invalid, just no known usecase ATM *)
        failwith "Why are we generating a batch file w/o runs?"
      | _ :: _ :: _ ->
        failwith "Can't handle multiple runs yet"
      | [run] ->
        List.length (Batch.Run.inlines run)
    method path = path
  end

(* Functions have been summarized *)
class summarized_indir path =
  object
    inherit base_indir path
    (* XXX: coverage *)
    method nclusters =
      List.length (BatList.of_enum (BatFile.lines_of (Printf.sprintf "%s/clusters" path)))
  end

(* Execution finished *)
class completed_indir path =
  object
    inherit summarized_indir path
    method success =
      (* XXX: result.log is misnamed *)
      let compl = (Printf.sprintf "%s/result.log" path) in
      let lines = BatFile.lines_of compl in
      match BatEnum.peek lines with
      | None ->
        failwith (Printf.sprintf "%s is empty!" compl)
      | Some line ->
        let re = Str.regexp "^success" in
        if Str.string_match re line 0 then
          BatResult.Ok ()
        else
          BatResult.Bad (BatList.of_enum lines)
  end

(* Has found something *)
class successful_indir path =
  object
    inherit completed_indir path
    method nresults =
      let open FileUtil in
      let f acc el = el :: acc in
      List.length (find Is_file (Printf.sprintf "%s/results" path) f [])
  end

type states = {
  bare: base_indir list;
  summarized: summarized_indir list;
  completed: completed_indir list;
  successful: successful_indir list;
}

let states_empty = {
  bare = [];
  summarized = [];
  completed = [];
  successful = [];
}

let states_aggregate st1 st2 =
  (* The lhs will be our accumulator, so will probably have more elements *)
  {
    bare = st2.bare @ st1.bare;
    summarized = st2.summarized @ st1.summarized;
    completed = st2.completed @ st1.completed;
    successful = st2.successful @ st1.successful;
  }

let states_to_str {bare; summarized; completed; successful} =
  let nbare = List.length bare in
  let nsum = List.length summarized in
  let ncomp = List.length completed in
  let nsucc = List.length successful in
  Printf.sprintf "bare: %d, summarized: %d, completed: %d, successful: %d"
    nbare nsum ncomp nsucc

let states_in_progress {bare; summarized; completed; successful} =
  (List.length bare) + (List.length summarized)

let states_total {bare; summarized; completed; successful} =
  (List.length bare) + (List.length summarized) + (List.length completed) +
  (List.length successful)

let do_binary acc path =
  let open FileUtil in
  let mk_p rel = Printf.sprintf "%s/%s" path rel in
  if test Is_dir (mk_p "results") then
    let indir = new successful_indir path in
    {acc with successful = indir :: acc.successful}
  else if test Is_file (mk_p "result.log") then
    let indir = new completed_indir path in
    {acc with completed = indir :: acc.completed}
  else if test Is_file (mk_p "clusters") then
    let indir = new summarized_indir path in
    {acc with summarized = indir :: acc.summarized}
  else
    let indir = new base_indir path in
    {acc with bare = indir :: acc.bare}

let binary_states binary_paths =
  List.fold_left do_binary states_empty binary_paths
