module D = Debug.Make(struct let name = "Embarassingly_parallel" and default=`Debug end)
open D

type 'a workfunc_result = {
  ret : 'a;
  bench : string
}

type exn_with_bt = {
  (*
   * Exceptions are not marshaled properly, we need to convert them
   * to strings in the process they were raised in.
   *)
  e : string;
  bt : string;
}

let exns_with_bts_to_string ewbs =
  let ewb_to_s ewb =
    Printf.sprintf "%s\n%s" ewb.e ewb.bt
  in
  Print.list_to_string ~enclosing:("", "") ~sep:"\n---\n" ewb_to_s ewbs

let update_bench mb =
  let mb = new Perfacc.marshalled_bench mb in
  mb#replay ()

let debug = ref false
let set_debug v = debug := v

let map_list f l =
  let workfunc el =
    try
(*      dprintf "workfunc: entry"; *)
      Printexc.record_backtrace true;
      let pid = Unix.getpid () in
(*      dprintf "workfunc: after getpid"; *)
      Outdir.with_file_out (Printf.sprintf "worker-%d.out" pid)
        (fun nstdout ->
(*           dprintf "workfunc: with nstdout";*)
           Unix.dup2 (Unix.descr_of_out_channel nstdout) Unix.stdout;
(*           dprintf "workfunc: after first dup";*)
           Outdir.with_file_out (Printf.sprintf "worker-%d.err" pid)
             (fun nstderr ->
(*                dprintf "workfunc: with nstderr";*)
                Unix.dup2 (Unix.descr_of_out_channel nstderr) Unix.stderr;
(*                dprintf "workfunc: after second dup";*)
                let res = f el in
                BatResult.Ok res))
    with e ->
      let bt = Printf.sprintf "Backtrace (may be inaccurate): %s"
        (Printexc.get_backtrace ())
      in
      let estr = Printexc.to_string e in
      BatResult.Bad {e = estr; bt = bt}
  in
  let debug_workfunc el =
    (*
     * Don't catch exceptions. It often happens that we'll get a useless
     * stacktrace for exceptions going through analysis_pass.ml at least,
     * so our best bet is to synchronously throw the exception, so that
     * it can be correlated with the debug output. A sad state of affairs.
     *)
    BatResult.Ok (f el)
  in
  let get_ress_exns results =
    let rec inner ress exns rss = match rss with
      | [] -> (ress, exns)
      | x :: rest ->
        (match x with
        | BatResult.Ok res -> inner (res :: ress) exns rest
        | BatResult.Bad exn -> inner ress (exn :: exns) rest)
    in
    inner [] [] results
  in
  let results = match !debug with
    | true -> List.map debug_workfunc l
    | false -> ForkWork.map_list ~fail_fast:true workfunc l
  in
  let ress, exns = get_ress_exns results in

  (* Update the Perfacc data anyway *)
  let bs = List.map (fun x -> x.bench) ress in
  List.iter update_bench bs;

  let results = List.map (fun x -> x.ret) ress in
  (results, exns)
