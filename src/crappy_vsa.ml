
module CrappyVSA = struct
  module D = Debug.Make(struct let name = "CrappyVSA" and default=`Debug end)
  open D

  open Ktype.Exceptions
  open Analysis_helpers.Var

  type t = {
    fd : Depgraphs.DDG_SSA.location Var.VarHash.t;
    vsa_out : Hvsa.SimpleVSA.DFP.G.V.t -> Hvsa.SimpleVSA.DFP.L.t;
  }

  let wrap_hvsa f x =
    try
      f x
    with Hvsa.Bug str ->
      raise (Confusing_function str)

  let calculate cfg descr =
    let (_, fd, _) = Depgraphs.DDG_SSA.compute_dd cfg in
    dprintf "About to do HVSA (%s)" descr;
    (*
     * Note: it would be nice to be able to use VSA here, but
     * - BAP's SimpleVSA tracks all vars and fails when it encounters
     *   a times/divide/etc operator.
     * - RegionVSA and AlmostVSA get stuck consuming CPU in the
     *   simple loop example with constant bounds (possibly
     *   because of AbsEnv issues (alluded to here:
     *   http://edmcman.bitbucket.org/blog/2012/09/24/success/),
     *   but haven't looked into it.
     *)
(*
       dprintf "About to do VSA";
       let vsa_in, vsa_out = Vsa.RegionVSA.DF.worklist_iterate g in
       dprintf "Done with VSA";
*)
    let _, vsa_out = wrap_hvsa Hvsa.SimpleVSA.DF.worklist_iterate cfg in
    let vsa_out = wrap_hvsa vsa_out in
    dprintf "Done with HVSA (%s)" descr;
    {fd; vsa_out;}

  let fd t = t.fd

  let def_for_var t var =
    vh_find t.fd var

  let si_for_val t value =
    let ((scale, lb, ub), str) = match value with
      | Ssa.Lab _ -> failwith "Tried to do VSA on an SSA label"
      | Ssa.Int (bi, _) ->
        let open Big_int_Z in
        let n = int64_of_big_int bi in
        ((Int64.zero, n, n), (Pp.value_to_string value))
      | Ssa.Var var ->
        begin
          let varstr = Pp.var_to_string var in
          match vh_find t.fd var with
          | None ->
            let str = Printf.sprintf "Couldn't find definition for var %s"
                (Pp.var_to_string var) in
            dprintf "%s" str;
            let typ = Var.typ var in
            (Vsa.SI.top (Typecheck.bits_of_width typ), varstr)
          | Some (vertex, _) ->
            let vsa_varmap = t.vsa_out vertex in
            match varmap_find vsa_varmap var with
            | None ->
              let str = Printf.sprintf "Couldn't get VSA information for var %s"
                  varstr in
              failwith str
            | Some si -> (si, varstr)
        end
    in
    dprintf "si_for_val(%s): (%s, %s, %s)" str
    (Int64.to_string scale) (Int64.to_string lb) (Int64.to_string ub);
    (scale, lb, ub)

  let bounds_for_val t value =
    let (_, lb, ub) = si_for_val t value in
    let open Big_int_Z in
    (big_int_of_int64 lb, big_int_of_int64 ub)

  module SI = struct
    let is_constant = function
      | (0L, l, h) when l = h -> true
      | _ -> false
        
    let not_pointer si =
      let (_, lb, ub) = si in
      let open Int64 in
      (* XXX: this needs to be better thought out *)
      (* if compare lb zero < 0 true then begin *)
      if true then begin
        let range = sub ub lb in
        let lim = shift_left one 24 in
        dprintf "si_not_pointer: range is %s, lim is %s"
          (Int64.to_string range)
          (Int64.to_string lim);
        if compare range minus_one = 0 then begin
          false
        end else begin
          compare range lim < 0
        end
      end else
        false

    let is_in_zero_page si =
      let open Int64 in
      let lim = Int64.of_int 4096 (* XXX: i386 *) in
      let (_, lb, ub) = si in
      let range = sub ub lb in
      if compare range minus_one = 0 then begin
        false
      end else if compare range lim < 0 &&
                compare lb zero < 0 &&
                  compare ub zero > 0 then begin
      true
      end else begin
        false
      end
  end

end
