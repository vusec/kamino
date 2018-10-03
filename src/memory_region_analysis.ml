module D = Debug.Make(struct let name = "Memory_region_analysis" and default=`Debug end)
open D

open Ssa
open Ktype.Exceptions
module Helpers = Analysis_helpers.SSA
open Analysis_helpers.Var
open Crappy_vsa

  module Sinkpath :
  sig
    type t
    val to_string : t -> string
    val follow : t -> Var.t -> t
    val sink : t -> Var.t
    val compare : t -> t -> int
    val of_var : Var.t -> t
    val includes : t -> Var.t -> bool
    val path : t -> Var.t list
  end =
  struct
    type t = {
      vrg_path : Var.t list
    }
    let to_string {vrg_path} =
      let s = Print.list_to_string ~enclosing:("", "") ~sep:" -> "
          Pp.var_to_string vrg_path in
      Printf.sprintf "(sinkpath %s)" s
    let follow sinkpath var =
      if List.mem var sinkpath.vrg_path then begin
        (* Caller should have caught this *)
        let s = Printf.sprintf "Adding %s to sinkpath %s would make a circle"
            (Pp.var_to_string var) (to_string sinkpath) in
        failwith s
      end else begin
        {vrg_path = var :: sinkpath.vrg_path}
      end
    let sink {vrg_path} = match vrg_path with
      | [] -> failwith "Tried to get sink from empty path"
      | sink :: _ -> sink
    let compare sink1 sink2 =
      Var.compare (sink sink1) (sink sink2)
    let of_var v = {vrg_path = [v]}
    let includes {vrg_path} var =
      try
        ignore (List.find (fun v ->
            Var.compare var v = 0) vrg_path);
        true
      with Not_found -> false
    let path {vrg_path} = vrg_path
  end

  module SinkSet = BatSet.Make(Sinkpath)

  let sinkset_to_str sinkset =
    Print.enum_to_string ~enclosing:("{", "}") ~sep:(", ")
      Sinkpath.to_string (SinkSet.enum sinkset)

module type VarReductionEdgeSig
=
sig
  type t
  type label = t
  val compare : t -> t -> int
  val default : t
  val create : Type.binop_type -> Ssa.value -> t
  val offsets : t -> (Big_int_Z.big_int * Big_int_Z.big_int)
  val binop : t -> Type.binop_type
  val value : t -> Ssa.value
  val to_string : t -> string
end

module type VsaOracleSig =
sig
  val bounds_for_val : Ssa.value -> (Big_int_Z.big_int * Big_int_Z.big_int)
end


module VarReductionEdge (VsaOracle : VsaOracleSig) : VarReductionEdgeSig =
struct
  (*
   * The edge is labeled with an ssa value. I.e.
   *     v2 -- (val) --> v1
   * means that v2 = v1 - val
   *)
  type t = (Type.binop_type * Ssa.value)
  type label = t
  let compare (_, a) (_, b) = match (a, b) with
    | Ssa.Lab _, _
    | _, Ssa.Lab _ -> failwith "Label in VarReductionEdge"
    | Ssa.Int _, Ssa.Var _-> -1
    | Ssa.Var _, Ssa.Int _ -> 1
    | Ssa.Int (bi_a, _), Ssa.Int (bi_b, _) -> Big_int_Z.compare_big_int bi_a bi_b
    | Ssa.Var a, Ssa.Var b -> Var.compare a b
  let default =
    (* Should never be used, we always set our own label *)
    (Type.PLUS, Ssa.Int (Big_int_Z.big_int_of_int 0, Type.Reg 0))
  let create binop value = (binop, value)
  let offsets (_, value) = VsaOracle.bounds_for_val value
  let binop = fst
  let value = snd
  let to_string (binop, value) =
    Printf.sprintf "(%s %s)" (Pp.binop_to_string binop)
      (Pp.value_to_string value)
end

type vrg_rewrite_type =
  | VRGRewritePhi of Var.t list
  | VRGRewriteJustIndex of Var.t
  | VRGRewriteIndexBinopConstant of Var.t * Type.binop_type * (Big_int_Z.big_int * Type.typ)
  | VRGRewriteConstantBinopIndex of (Big_int_Z.big_int * Type.typ) * Type.binop_type * Var.t
  | VRGRewriteNothing

exception Cannot_map_to_region of string

  let choose_vrg_path sinkpath exp =
    let open Ssa in
    let open Big_int_Z in
    let in_sinkpath v = Sinkpath.includes sinkpath v in
    match exp with
    | BinOp (Type.PLUS, Var v, Int (d, t))
    | BinOp (Type.PLUS, Int (d, t), Var v) ->
      assert (in_sinkpath v);
      Some (v, Type.PLUS, Int (Arithmetic.to_sbig_int (d, t), t))
    | BinOp (Type.PLUS, Var v1, Var v2) ->
      if in_sinkpath v1 then begin
        Some (v1, Type.PLUS, Var v2)
      end else begin
        assert(in_sinkpath v2);
        Some (v2, Type.PLUS, Var v1)
      end
    | BinOp (Type.MINUS, Var v, Int (d, t))
    | BinOp (Type.MINUS, Int (d, t), Var v) ->
      assert (in_sinkpath v);
      Some (v, Type.MINUS, Int (Arithmetic.to_sbig_int (d, t), t))
    | BinOp (Type.MINUS, Var v1, Var v2) ->
       (*
        * Umm, here we should be deciding based on the sinkpath,
        * but if v2 is in the sinkpath, then we can't just use v1
        * as the operand. XXX!
        *)
        Some (v1, Type.MINUS, Var v2)
(*
   XXX: We don't want to be adding shifts to the VRG as we can't
   do Bellman-Ford on it then. However, we could possibly do BF on
   it by calculating the lower/upper weights (for BF purposes) based
   on the VSA information of the source of the edge and the binop,
   ssa.value. One would need to modify VarReductionWeightLowBound{,Negated}
   and vertex_path_sum appropriately. Currently we're in deadline mode.
    | BinOp (Type.LSHIFT, Var v1, (Int (d, t) as ssaint)) ->
      Some (v1, Type.LSHIFT, ssaint)
*)
    | Val (Var v) ->
      Some (v, Type.PLUS, Int (zero_big_int, Type.Reg 32))
    | _ -> None

  (*
   * Given a definitions map fd ("Find Definition"), try to
   * resolve var as (input_var +/- constant). Return a tuple of
   * (base_var, low, high) if we could do that, else return None.
   *)
  let reduce_var vsa_info cfg ~ptr sinkpath =
    dprintf "reduce_var %s: sinkpath = %s" (Pp.var_to_string ptr) (Sinkpath.to_string sinkpath);
    let base = Sinkpath.sink sinkpath in
    let open Big_int_Z in
    (*
     * XXX: this needs to be moved out of reduce_var, no need to
     * recalc every time.
     *)
    let module VsaOracle = struct
      let bounds_for_val = CrappyVSA.bounds_for_val vsa_info
    end in
    let module VarReductionEdge = VarReductionEdge(VsaOracle) in
    let module VRG =
      Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Var)(VarReductionEdge)
    in
    let module VarReductionWeightLowBound =
    struct
      type t = Big_int_Z.big_int
      type edge = VRG.E.t
      let weight edge_t =
        let edge = VRG.E.label edge_t in
        let lb, ub = VarReductionEdge.offsets edge in
        (* We're trying to calculate the minimal sum; add accordingly *)
        match VarReductionEdge.binop edge with
        | Type.PLUS ->
          lb
        | Type.MINUS ->
          let open Big_int_Z in
          min_big_int (minus_big_int lb) (minus_big_int ub)
        | _ ->
          failwith "unexpected binop in VarReductionWeightLowBound"
      let compare = Big_int_Z.compare_big_int
      let add = add_big_int
      let zero = Big_int_Z.big_int_of_int 0
    end
    in
    let module VarReductionWeightLowBoundNegated =
    struct
      type t = Big_int_Z.big_int
      type edge = VRG.E.t
      let weight edge_t =
        let edge = VRG.E.label edge_t in
        let open Big_int_Z in
        (* We're trying to calculate the minimal sum, but we negate
         * all edge weights first.
        *)
        let orig_lb, orig_ub = VarReductionEdge.offsets edge in
        let lb, ub = (minus_big_int orig_lb, minus_big_int orig_ub) in
        match VarReductionEdge.binop edge with
        | Type.PLUS ->
          min_big_int lb ub
        | Type.MINUS ->
          (*
           * Here we would negate the bounds again, getting the
           * original values. The minimal of those is the lb.
           *)
          orig_lb
        | _ ->
          failwith "unexpected binop in VarReductionWeightLowBoundNegated"
      let compare = Big_int_Z.compare_big_int
      let add = Big_int_Z.add_big_int
      let zero = Big_int_Z.big_int_of_int 0
    end
    in
    let dump_vrg =
      let module VRG_printer =
      struct
        include VRG
        let default_edge_attributes _ = [`Style `Solid]
        let edge_attributes e =
          [`Label (VarReductionEdge.to_string (VRG.E.label e))]
        (*
         * The dot language has issues with node names containing
         * a '.', so we replace all occurrences with  '_'
         *)
        let vertex_name v = Str.global_replace (Str.regexp "\\.") "_" (Pp.var_to_string v)
        let default_vertex_attributes _ = [`Shape `Box]
        let vertex_attributes _ = [`Shape `Box]
        let graph_attributes _ = [`Orientation `Landscape]
        let get_subgraph _ = None
      end
      in
      let module VRG_dot = Graph.Graphviz.Dot(VRG_printer) in
      VRG_dot.output_graph
    in
    let vertex_path_sum low_high vrg vertices =
      match vertices with
      | [] -> failwith "vertex_path_sum on empty list"
      | _ ->
        (*
         * We prepend the last vertex to the list so that we'll also
         * account for the last -> first edge. This nicely takes care
         * of the [v] (i.e. self-loop) case.
         *)
        let last = BatList.last vertices in
        let sum, _ = List.fold_left (fun (sum, v1) v2 ->
            let edge =
              try
                VRG.find_edge vrg v1 v2
              with Not_found -> failwith "Couldn't find VRG edge!"
            in
            let lab = VRG.E.label edge in
            let offsets = VarReductionEdge.offsets lab in
            let lb, ub = offsets in
            let binop = VarReductionEdge.binop lab in
            let open Big_int_Z in
            let opnd = match low_high, binop with
              | (`OffsetLow, Type.PLUS) ->
                (* Trying to get min sum and this is a PLUS, add the low bound *)
                lb
              | (`OffsetHigh, Type.PLUS) ->
                (* Want the max sum and this is a PLUS, add the high bound *)
                ub
              | (`OffsetLow, Type.MINUS) ->
                let min = min_big_int (minus_big_int lb) (minus_big_int ub) in
                min
              | (`OffsetHigh, Type.MINUS) ->
                let max = max_big_int (minus_big_int lb) (minus_big_int ub) in
                max
              | _ ->
                failwith (Printf.sprintf "Unexpected binop: %s"
                            (Pp.binop_to_string binop))
            in
            (Big_int_Z.add_big_int sum opnd, v2)
          )
            (Big_int_Z.big_int_of_int 0, last) vertices
        in
        sum
    in
    let cycle_analysis vrg =
      let cycles =
        let nb_vertex = VRG.nb_vertex vrg in
        if nb_vertex > 1 then begin
          try
            let module J = Johnson.Make(VRG) in
            J.find_all_cycles vrg
          with Not_found -> failwith "WHYYY"
        end else if nb_vertex = 0 then
          []
        else begin
          let v = List.hd (VRG.fold_vertex (fun v _ -> [v]) vrg []) in
          try
            ignore(VRG.find_edge vrg v v);
            (* self-loop *)
            [[v]]
          with Not_found -> []
        end
      in
      dprintf "Johnson: Found %d cycles" (List.length cycles);
      List.iter (fun vs ->
          let cycle = Print.list_to_string ~enclosing:("", "") ~sep:" -> "
              Pp.var_to_string
              vs
          in
          dprintf "cycle: %s" cycle;
        ) cycles;
      let got_neg, got_pos = List.fold_left (fun (got_neg, got_pos) cycle ->
          let open Big_int_convenience in
          (*
           * No need to sum around the path if we already know we have a
           * a negative/positive cycle.
           *)
          let got_neg = match got_neg with
            | true -> true
            | false ->
              begin
                (*
                 * Get the lowest sum possible by only looking at the low bounds.
                 *)
                let sum = vertex_path_sum `OffsetLow vrg cycle in
                sum <% bi0
              end
          in
          let got_pos = match got_pos with
            | true -> true
            | false ->
              begin
                let sum = vertex_path_sum `OffsetHigh vrg cycle in
                sum >% bi0
              end
          in
          (got_neg, got_pos)
        ) (false, false) cycles
      in
      (got_neg, got_pos)
    in
    let rec chase_def vrg sinkpath var = function
      | Move (_, Load (_, _, _, _), _) ->
          (*
           * If this variable has been loaded from memory, we consider it
           * a basereg, so resolution stops here.
           *)
        dprintf "VRG: definition is a Load";
        Some vrg
      | Move (_, Phi vs, []) ->
        (* XXX:          ^^^ not handled properly
         * We need to rewrite any Load(, phi()) stuff to use the correct index.
        *)
        let vrg = Some (VRG.add_vertex vrg var) in
        dprintf "Added %s to the VRG" (Pp.var_to_string var);
        List.fold_left (fun vrg v ->
            match vrg with
            | None -> None
            | Some vrg ->
              let vrg =
                if VRG.mem_vertex vrg v then begin
                  dprintf "VRG: Stop chasing seen variable.";
                  Some vrg
                end else begin
                  dprintf "VRG: Chasing new variable.";
                  vrg_add_var (VRG.add_vertex vrg v) sinkpath v
                end
              in
              begin
                match vrg with
                | None -> None
                | Some vrg ->
                  let bi0 = Big_int_Z.big_int_of_int 0 in
                  let edge = VarReductionEdge.create Type.PLUS (Int (bi0, Type.Reg 32)) in
                  let vrg = VRG.add_edge_e vrg (var, edge, v) in
                  Some vrg
              end) vrg (List.filter (Sinkpath.includes sinkpath) vs)
      | Move (_, exp, _) ->
        begin
          dprintf "VRG: choose_vrg_path(%s)" (Pp.ssa_exp_to_string exp);
          match choose_vrg_path sinkpath exp with
          | Some (v, binop, operand) ->
            dprintf "VRG: got (%s, %s, %s)" (Pp.var_to_string v)
              (Pp.binop_to_string binop)
              (Pp.value_to_string operand);
            let edge = VarReductionEdge.create binop operand in
            let vrg = VRG.add_edge_e vrg (var, edge, v) in
            vrg_add_var vrg sinkpath v
          | None ->
            (*
             * Cannot follow the path to the base ptr, probably b/c we run
             * into something other than a +/-.
             *)
            raise (Confusing_function "VRG: couldn't express as (var, off)")
        end
      | _ -> failwith "definition is not a Move"
    and vrg_add_var vrg sinkpath var =
      if not (VRG.mem_vertex vrg var) then begin
        let str = Printf.sprintf "%s is not in the VRG!" (Pp.var_to_string var) in
        raise (Confusing_function str)
      end;
      dprintf "VRG: vrg_add_var %s" (Pp.var_to_string var);
      match CrappyVSA.def_for_var vsa_info var with
      | None -> (* Input variable *)
        dprintf "VRG: no definition for %s" (Pp.var_to_string var);
        Some vrg
      | Some loc ->
        begin
          let def = Helpers.get_stmt_at cfg loc in
          dprintf "VRG: definition of %s: %s" (Pp.var_to_string var)
            (Pp.ssa_stmt_to_string def);
          match Var.typ var with
          | Type.Reg x when x = 32 ->
            (* If x < 32, this definitely isn't a pointer, stop chasing
             * and rely on the VSA information to deduce bounds from the
             * VRG.
            *)
            chase_def vrg sinkpath var def
          | _ ->
            Some vrg
        end
    in
    let find_shortest_path_weight vrg var target =
      let module BF = Graph.Path.BellmanFord(VRG)(VarReductionWeightLowBound) in
      let all_shortest = BF.all_shortest_paths vrg var in
      BF.H.find all_shortest target
    in
    let find_longest_path_weight vrg var target =
      let module BF = Graph.Path.BellmanFord(VRG)(VarReductionWeightLowBoundNegated) in
      let all_shortest = BF.all_shortest_paths vrg var in
      let w = BF.H.find all_shortest target in
      Big_int_Z.minus_big_int w
    in
    let vrg_reduce_var vrg ~ptr ~base =
      (*
       * Trying to find a path from var to "the exit node":
       * 1. if the VRG has only positive cycles, then the interval
       * extends to positive infinity. However, we can still use
       * bellman-ford to get the min bound.
       * 2. if the vrg has only negative cycles, then the interval
       * definitely extends to negative infinity. Let -VRG be the graph
       * we get when flipping the signs of the weights in the original
       * VRG. Then, all negative cycles become positive cycles. We
       * can use bellman-ford to get the shortest path for -VRG.
       * The found path is the path with the maximum weight for the
       * original VRG, so that gives us the max bound.
       *
       * NOTE: I know what you're thinking: isn't the longest-path
       * problem NP-hard? Well, it seems the NP-hardness of the problem
       * enters the picture when one is trying to find the _simple_
       * longest path. Have not been able to find any literature
       * reference that clarifies that, however.
       *
       * 3. if there are both positive and negative cycles, the
       * interval extends from (-inf, inf).
       * 4. If there are no cycles, it's a DAG. We can find a non-infinite
       * min/max with the same trick.
       *)
      (*
       * Note: find_reduction_target might change the VRG (see its body),
       * it's needed both for our BF runs here and for deciding what to
       * rewrite.
       *)
(*
      let (vrg, base) = find_reduction_target vrg var in
*)
      let got_neg, got_pos = cycle_analysis vrg in
      let min, max = match got_neg, got_pos with
        | false, false ->
          (* No cycles or only cycles of 0 sum *)
          let min = find_shortest_path_weight vrg ptr base in
          let max = find_longest_path_weight vrg ptr base in
          (Some min, Some max)
        | false, true ->
          (* Only positive cycles, just need to find min bound *)
          let min = find_shortest_path_weight vrg ptr base in
          let max = None in
          (Some min, max)
        | true, false ->
          (* Only negative cycles, just need to find max bound *)
          let min = None in
          let max = find_longest_path_weight vrg ptr base in
          (min, Some max)
        | true, true ->
          (* Both negative and positive cycles, can get any value
           * out of that
          *)
          (None, None)
      in
      let b2s default = function
        | Some b -> Big_int_Z.string_of_big_int b
        | None -> default
      in
      dprintf "VRG: reduced %s to (%s, %s, %s)"
        (Pp.var_to_string ptr) (Pp.var_to_string base)
        (b2s "-inf" min) (b2s "+inf" max);
      (vrg, base, min, max)
    in
    dprintf "VRG: reduce_var: %s" (Pp.var_to_string ptr);
    let vrg = VRG.add_vertex VRG.empty ptr in
    let vrg = vrg_add_var vrg sinkpath ptr in
    match vrg with
    | None ->
      dprintf "VRG: reduce_var: failed";
      None
    | Some vrg ->
      begin
        dprintf "Calculated VRG:";
        dump_vrg stdout vrg;
        output_string stdout "\n";
        try
          let (vrg, base_var, low, high) = vrg_reduce_var vrg ~ptr ~base in
          let ret = (base_var, low, high) in
          Some ret
        with Cannot_map_to_region str -> (* XXX: can't get here *)
          dprintf "reduce_var: Could not map %s to region: %s"
            (Pp.var_to_string ptr) str;
          None
      end

  let collect_rvars stmt =
    let visitor = object
      inherit Ssa_visitor.nop
      val mutable rvars = []
      method get_rvars = rvars
      method visit_rvar v =
        rvars <- v :: rvars;
        Type.SkipChildren
    end in
    ignore(Ssa_visitor.stmt_accept visitor stmt);
    visitor#get_rvars

  let rec chase_def ~ptr fd cfg sinks sinkpath stmt =
    dprintf "sinks_for_var_chase_def (%s)" (Pp.ssa_stmt_to_string stmt);
    let try_vars sinks_acc var =
      if Var.compare ptr var = 0 ||
         Sinkpath.includes sinkpath var then begin
        (*
         * Stop if we have already seen the variable or if we cycled back
         * to the pointer we started out with (can happen in the presence
         * of phis).
         *)
        sinks_acc
      end else begin
        (* The sinkpath of course needs to be the one on entry, for each var *)
        let sinkpath = Sinkpath.follow sinkpath var in
        sinks_for_var_inner ~ptr fd cfg sinks_acc sinkpath
      end
    in
    match stmt with
    | Ssa.Move (_, Ssa.Load (_, _, _, _), _) ->
      (*
       * If this variable has been loaded from memory, we consider it
       * a basereg, so resolution stops here.
       *)
      dprintf "chase_def: definition is a Load";
      SinkSet.add sinkpath sinks
    | Ssa.Move (_, Ssa.Phi vs, []) ->
      List.fold_left try_vars sinks vs
    | Ssa.Move (_, _, _) as stmt ->
      let rvars = collect_rvars stmt in
      List.fold_left try_vars sinks rvars
    | _ ->
      sinks
  and sinks_for_var_inner ~ptr fd cfg sinks sinkpath =
    (* Get the latest var in the path; this is a potential sink *)
    let var = Sinkpath.sink sinkpath in
    dprintf "sinks_for_var_inner %s" (Pp.var_to_string var);

    match Var.typ var with
    | Type.Reg _ ->
      begin
        if SinkSet.mem (Sinkpath.of_var var) sinks then begin
          sinks
        end else begin
          match vh_find fd var with
          | None ->
            (* No def, it's an input. Can be a pointer *)
            SinkSet.add sinkpath sinks
          | Some loc ->
            begin
              let def = Helpers.get_stmt_at cfg loc in
              chase_def ~ptr fd cfg sinks sinkpath def
            end
        end
      end
    | _ ->
      sinks

  let sinks_for_var fd cfg ptr =
    sinks_for_var_inner ~ptr fd cfg SinkSet.empty (Sinkpath.of_var ptr)

  let var_is_not_pointer vsa_info var =
    let si = CrappyVSA.si_for_val vsa_info (Ssa.Var var) in
    (* XXX: here we only rely on the VSA info, but perhaps we can deduce what
       is a pointer by dataflow from a value that clearly is not a pointer. Perhaps
       by first marking definite pointers. Then, everything that participates in
       addition with them is not a pointer? Waving hands a bit.
     *)
    CrappyVSA.SI.is_in_zero_page si

  let value_definitely_is_ptr cfg value =
    match value with
    | Ssa.Lab _ ->
      let s = Printf.sprintf "value_definitely_is_ptr on label (%s)"
          (Pp.value_to_string value) in
      failwith s
    | _ ->
      let is_ptr vertex = Pointerness.is_pointer cfg vertex value in
      let exitbbs = Cfg_convenience.SSA.get_exit_bbs cfg in
      begin
        try
          (* If we find one exit path where the value is not definitely
           * a pointer, we can't return 'true'
           *)
          ignore(List.find (fun exit_bb ->
              not (is_ptr exit_bb)) exitbbs);
          false
        with Not_found -> true
      end

  let filter_sinks cfg vsa_info sinks =
    dprintf "filter_sinks: %s" (sinkset_to_str sinks);
    let pointers = SinkSet.filter (fun sinkpath ->
        let path_plausible sinkpath =
          try
            (*
             * The path is plausible unless an intermediate value is
             * clearly not a pointer.
             *)
            ignore(List.find (var_is_not_pointer vsa_info) (Sinkpath.path sinkpath));
            false
          with Not_found -> true
        in
        path_plausible sinkpath) sinks in
    match SinkSet.cardinal pointers with
    | 0 ->
      dprintf "Filtered away all sinks (%s), must be a global"
          (sinkset_to_str sinks);
      []
    | 1 ->
      begin
        BatList.of_enum (SinkSet.enum pointers)
      end
    | _ ->
      begin
        let definite_pointers = SinkSet.filter (fun sinkpath ->
            let sinkval = Var (Sinkpath.sink sinkpath) in
            value_definitely_is_ptr cfg sinkval) pointers
        in
        match SinkSet.cardinal definite_pointers with
        | 0 ->
          let s = Printf.sprintf "More than one sink (%s) and no definite pointers"
              (sinkset_to_str sinks) in
          dprintf "filter_sinks: %s" s;
          BatList.of_enum (SinkSet.enum pointers)
        | 1 ->
          (*
           * Exactly one definite pointer; assume this is the base ptr.
           *)
          BatList.of_enum (SinkSet.enum definite_pointers)
        | _ ->
          (*
           * This can legitimately happen, but it should be so rare that
           * it's more likely we messed up and declared a definite pointer
           * something that really wasn't.
           *)
          let s = Printf.sprintf "More than one definite pointers: %s
                                  (started from %s)"
              (sinkset_to_str definite_pointers) (sinkset_to_str pointers) in
          failwith s
      end

  let sinkpaths_for_var vsa_info cfg var =
    dprintf "sinkpath_for_var: %s" (Pp.var_to_string var);
    let sinks = sinks_for_var (CrappyVSA.fd vsa_info) cfg var in
    if SinkSet.is_empty sinks then begin
      [Sinkpath.of_var var] (* Fresh var: input or var = Load() *)
    end else begin
      filter_sinks cfg vsa_info sinks
    end

