module D = Debug.Make(struct let name = "Perfacc" and default=`NoDebug end)
open D

let global_stats = BatHashtbl.create 10
let scope = BatDynArray.create ()

let output_on_stdout = ref false

class type child_stats_t =
object
  method get_full_path : string
  method get_mean : float
  method get_n : int
  method get_m2 : float
  method get_children : child_stats_t BatDynArray.t
  method get_min : float
  method get_min_desc : string
  method get_max : float
  method get_max_desc : string
  method get_name : string
  method get_stddev : float
  method register_child : child_stats_t -> unit
  method register_self : unit -> unit
  method register_sample : float -> string -> unit
  method merge_children : child_stats_t -> unit
  method merge : child_stats_t -> unit
  method to_s : int -> string
end

class child_stats name scope_path : child_stats_t =
object(self)
  val mutable mean = 0.
  val mutable m2 = 0.
  val mutable n = 0
  val mutable min = infinity
  val mutable max = neg_infinity
  val mutable min_desc = "n/a"
  val mutable max_desc = "n/a"
  val children = BatDynArray.create ()
  val base_path = scope_path
  val full_path = scope_path ^ "." ^ name
  method get_full_path = full_path
  method get_mean =
    assert(mean > -0.1);
    mean
  method get_n = n
  method get_m2 = m2
  method get_children = children
  method get_min = min
  method get_min_desc = min_desc
  method get_max = max
  method get_max_desc = max_desc
  method get_stddev =
    if n > 1 then
      let variance = m2 /. (float (n - 1)) in
      sqrt variance
    else
      nan
  method get_name = name
  method register_child (ch : child_stats_t) =
    dprintf "%s#register_child(%s)" name ch#get_full_path;
    (* If the child exists, we should have found it in
     * the global_stats and never reached here.
    *)
    if (BatEnum.exists (fun x ->
      (String.compare x#get_name ch#get_name) = 0)
          (BatDynArray.enum children)) then begin
      dprintf "%s already exists" ch#get_full_path;
      failwith "duplicate child"
    end;
    BatDynArray.add children ch
  method register_self () =
    let fp = self#get_full_path in
    dprintf "register_self %s" fp;
    try
      ignore(BatHashtbl.find global_stats fp)
    with Not_found ->
      begin
        dprintf "register_self: not_found";
        BatHashtbl.add global_stats fp (self :> child_stats_t);
        BatDynArray.iter (fun ch ->
          ch#register_self ()) children
      end
  method register_sample x desc =
    dprintf "%s#register_sample(%f)" name x;
    let delta = x -. mean in
    n <- n + 1;
    mean <- mean +. (delta /. (float n));
    m2 <- m2 +. (delta *. (x -. mean));
    if x < min then begin
      min <- x;
      min_desc <- desc
    end;
    if x > max then begin
      max <- x;
      max_desc <- desc
    end
  method merge_children other =
    let print_children s =
      dprintf "Children of %s" s#get_name;
      BatDynArray.iter (fun ch ->
        dprintf "child: %s" ch#get_name) s#get_children;
      dprintf "---"
    in
    dprintf "merge_children %s %s:" name other#get_name;
    print_children self;
    print_children other;
    let sorted da =
      dprintf "dynary pre sort len: %d" (BatDynArray.length da);
      let ary = BatDynArray.to_array da in
      dprintf "ary pre sort len: %d" (Array.length ary);
      Array.sort (fun a b ->
        String.compare a#get_name b#get_name) ary;
      ary
    in
    let group_arys ary1 ary2 pred =
      let wrapl = List.map (fun x -> (Some x, None)) in
      let wrapr = List.map (fun x -> (None, Some x)) in
      let len1 = Array.length ary1 in
      let len2 = Array.length ary2 in
      let rec inner acc off1 off2 =
        dprintf "inner: len1=%d len2=%d off1=%d off2=%d"
          len1 len2 off1 off2;
        if off1 = len1 then
          let rem = Array.sub ary2 off2 (len2 - off2) in
          dprintf "rem: %d" (Array.length rem);
          List.append acc (wrapr (Array.to_list rem))
        else if off2 = len2 then
          let rem = Array.sub ary1 off1 (len1 - off1) in
          List.append acc (wrapl (Array.to_list rem))
        else
          let el1 = Array.get ary1 off1 in
          let el2 = Array.get ary2 off2 in
          let cmp = pred el1 el2 in
          if cmp = 0 then
            inner ((Some el1, Some el2) :: acc) (off1 + 1) (off2 + 1)
          else if cmp > 0 then
            inner ((None, Some el2) :: acc) off1 (off2 + 1)
          else
            inner ((Some el1, None) :: acc) (off1 + 1) off2
      in
      inner [] 0 0
    in
    let mine = sorted children in
    let theirs = sorted other#get_children in
    let grouped = group_arys mine theirs (fun a b ->
      String.compare a#get_name b#get_name)
    in
    dprintf "grouped: %d" (List.length grouped);
    let right = BatList.filter_map (fun grp ->
      match grp with
      | (None, Some x) ->
        dprintf "right: %s" x#get_name;
        Some x
      | Some a, Some b ->
        dprintf "leftright: %s %s" a#get_name b#get_name;
        a#merge b;
        None
      | Some a, None ->
        dprintf "left: %s" a#get_name;
        None
      | None, None ->
        failwith "can't happen") grouped
    in
    (* merge in the children present only on the rhs *)
    List.iter (fun ch ->
      (*
       * The RHS stats might not have been added to
       * /this/ process's global_stats.
      *)
      begin
        try
          let prev_stats = BatHashtbl.find global_stats ch#get_full_path in
          prev_stats#merge ch
        with Not_found -> ch#register_self ();
      end;
      self#register_child ch) right;
    dprintf "LHS children";
    print_children self;
    ()
  method merge other =
    dprintf "merge: %s %s" name other#get_name;
    assert (name = other#get_name);
    let delta = other#get_mean -. mean in
    let new_n = n + other#get_n in
    let n_a = float n in
    let n_b = float other#get_n in
    dprintf "our_mean: %f, their_mean: %f" mean other#get_mean;
    mean <- mean +. (delta *. (n_b /. (float new_n)));
    m2 <- m2 +. other#get_m2 +. ((delta *. delta) *. ((n_a *. n_b) /. (float new_n)));
    n <- new_n;
    assert(mean > -0.01);
    assert(m2 > -0.01);
    if other#get_min < min then begin
      min <- other#get_min;
      min_desc <- other#get_min_desc
    end;
    if other#get_max > max then begin
      max <- other#get_max;
      max_desc <- other#get_max_desc
    end;
    self#merge_children other
  method to_s lvl =
    let chstr = BatDynArray.fold_left (fun acc ch ->
      let just = BatString.repeat " " (lvl * 2) in
      Printf.sprintf "%s%s%s" acc just (ch#to_s (lvl + 1))) "" children
    in
    (*
     * Note: because of parallel execution, the total CPU time
     * can be way larger than the total time of a "parent" object
     *)
    let mdesc = match String.contains max_desc '\n' with
      | true -> Printf.sprintf "%s%s%s" Print.fo max_desc Print.fc
      | false -> max_desc
    in
    Printf.sprintf "%s: tot %.2f, n: %d, mean: %f, stddev: %f [max %f (%s)]\n%s"
      name ((float n) *. self#get_mean) n self#get_mean self#get_stddev max mdesc chstr
end

let current_scope_path () =
  BatDynArray.fold_left (fun acc el ->
    Printf.sprintf "%s.%s" acc el#get_name) "" scope

class basic_bench name =
object(self)
  val mutable stats = None
  val mutable initialized = false
  method get_name = name
  method get_stats () =
    match stats with
    | Some s ->
      (s :> child_stats)
    | None ->
      let str = Printf.sprintf "%s: no stats stored" name in
      failwith str
  method private register_stats stats =
    dprintf "register_stats %s" stats#get_full_path;
    stats#register_self ();
    if BatDynArray.length scope > 0 then begin
      let parent = BatDynArray.last scope in
      let pstats = parent#get_stats () in
      pstats#register_child stats
    end
  method initialize provided_stats =
    ignore(match provided_stats with
    | None ->
      stats <- Some
        (try
           BatHashtbl.find global_stats ((current_scope_path ()) ^ "." ^ name)
         with Not_found ->
           let nstats = new child_stats name (current_scope_path ()) in
           self#register_stats nstats;
           nstats
        );
    | Some s ->
      dprintf "provided stats";
      try
        let prev_stats = BatHashtbl.find global_stats s#get_full_path in
        prev_stats#merge s;
        stats <- Some prev_stats
      with Not_found ->
        self#register_stats s;
        stats <- Some s);
    initialized <- true
  method completion duration desc =
    assert(initialized = true);
    let st = self#get_stats () in
    st#register_sample duration desc;
end


let bench_dump_key = ref None

let set_bench_dump_key value =
  match !bench_dump_key with
  | Some _ ->
    begin
      if value = None then
        bench_dump_key := None
      else
        failwith "tried to reset bench_dump_key"
    end
  | None -> bench_dump_key := value

class bench name =
object(self)
  inherit basic_bench name as super
  val mutable start_time = 0.
  val mutable desc = ""
  method start descr =
    dprintf "%s#bench.start (%s) [pid %d (%d)]" name descr (Unix.getpid ()) (Unix.getppid ());
    super#initialize None;
    desc <- descr;
    start_time <- Unix.gettimeofday ();
    (* Ocaml 3.12 manual, section 3.12 (yes, not a copy-paste error) *)
    BatDynArray.add scope (self :> bench)
  method stop ?(features=[]) () =
    dprintf "%s#bench.stop (%s)" name desc;

    let end_time = Unix.gettimeofday () in
    let total = end_time -. start_time in

    ignore(match !bench_dump_key with
        | None -> ()
        | Some key ->
          let key = Printf.sprintf "%s/%s" key name in
          let open Sexplib in
          let sexp = Sexp.List [
              Conv.sexp_of_float total;
              Conv.sexp_of_list Conv.sexp_of_float features;
              Sexp.Atom (String.escaped desc);
            ] in
          Outdir.with_file_out ~append:true key (fun oc ->
              let fmt = Format.formatter_of_out_channel oc in
              Sexp.pp_mach fmt sexp;
              Format.pp_print_newline fmt ();
              Format.pp_print_flush fmt ();
            )
      );
    super#completion total desc;

    let last = BatDynArray.last scope in
    if not (last = (self :> bench)) then begin
      let last_str = (last#get_stats ())#get_full_path in
      let self_str = (self#get_stats ())#get_full_path in
      let str = Printf.sprintf "CRAP: last %s, self %s" last_str self_str in
      failwith str
    end;
    if (BatDynArray.length scope) = 1 then begin
      let root = BatDynArray.last scope in
      if !output_on_stdout then
        Printf.printf "BENCH STATS:\n%s%!" ((root#get_stats ())#to_s 1)
      else dprintf "BENCH STATS:\n%s%!" ((root#get_stats ())#to_s 1)
    end;
    BatDynArray.delete_last scope
end

class synthesized_bench name =
object(self)
  inherit basic_bench name as super
  method fakeit duration descr =
    super#initialize None;
    super#completion duration descr
end

class marshalled_bench mbench =
  let bench = Marshal.from_string mbench 0 in
  let name = bench#get_name in
object
  inherit basic_bench name as super
  method replay () =
    dprintf "replaying %s" name;
    let nstats = bench#get_stats () in
    super#initialize (Some nstats);
    dprintf "done replaying %s" name;
end
