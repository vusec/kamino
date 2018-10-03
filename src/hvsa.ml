module VM = Var.VarMap

open Big_int_Z
open Util
open Type
open Ssa

module D = Debug.Make(struct let name = "HVSA" and default=`NoDebug end)
open D


exception Unimplemented of string
exception Bug of string

let rec uint64_gcd x y =
  if y = 0L then x
  else uint64_gcd y (int64_urem x y)

module I = Int64
(* some operators to make this more readable *)
let (&%) = I.logand
let (|%) = I.logor
let (^%) = I.logxor
let (+%) = I.add
let (-%) = I.sub
let bnot = I.lognot


let bits_of_width = Typecheck.bits_of_width

let fwd_transfer_stmt_to_block f g node latice =
  List.fold_left (fun l n -> f n l) latice (Cfg.SSA.get_stmts g node)

(* FIXME: find a better way to get the stack pointer *)
let sp = List.find (fun (Var.V(_,n,_)) -> n = "R_ESP") (Asmir.decls_for_arch Asmir.arch_i386)


(** Strided Intervals *)
module SI =
struct
(* FIXME: some of these functions can return a stride of 1 for a singleton *)

  (** unsigned stride * signed lower bound * signed upper bound *)
  type t = int64 * int64 * int64

  let to_string (s,lb,ub) = Printf.sprintf "%Lu[%Ld,%Ld]" s lb ub

  let highbit k =
    if k = 1 then 1L else I.shift_left 1L (k-1)

  let extend k i =
    if k <> 64 then
      let k' = 64-k in I.shift_right(I.shift_left i k') k'
    else i

  let trunc k i =
    if k <> 64 then
      let k' = 64-k in I.shift_right_logical(I.shift_left i k') k'
    else i

  let maxi k = highbit k -% 1L
  let mini k = extend k (highbit k)
  let top k = (1L, mini k, maxi k)

  let single x = (0L,x,x)
  let of_bap_int i t = single (extend (bits_of_width t) i)

  let zero = single 0L
  let one = single 1L
  let minus_one = single (-1L)


  let is_reduced k (s,lb,ub) =
    assert(k>0 && k<=64);
    if not (lb >= mini k) then
      Some "lb < mini k"
    else if not (ub <= maxi k) then
      Some "ub > maxi k"
    else if s = 0L then
      if lb = ub then
        None
      else
        Some "s is 0 and lb <> ub"
    else begin
      if not (lb < ub) then
        Some (Printf.sprintf "lb (%#Lx) >= (%#Lx) ub" lb ub)
      else begin
        let r1 = I.rem lb s
        and r2 = I.rem ub s
        in
        if r1 = r2 then
          None
        else begin
          if r2 -% r1 = s then
            None
          else begin
            let str = Printf.sprintf "Not in reduced form because r2 -%% r1 \
                                      (%#Lx) <> s (%#Lx)" (r2 -% r1) s in
            Some str
          end
        end
      end
    end

  let check_reduced k si =
    match is_reduced k si with
    | None -> ()
    | Some str ->
      raise (Bug (string_of_int k ^ "-bit Strided Interval " ^ to_string si ^
                " not in reduced form: " ^ str))

  let check_reduced2 k si1 si2 =
    check_reduced k si1; check_reduced k si2


  let renorm k ((a,b,c) as si) =
    let si' = if b = c then (0L,b,b) else si in
      check_reduced k si';
      si'

  let renormbin f k x y = renorm k (f k x y)
  let renormun f k x = renorm k (f k x)


  (** Addition of strided intervals *)
  let add k ((s1,lb1,ub1) as a) ((s2,lb2,ub2) as b) =
    check_reduced2 k a b;
    let lb' = lb1 +% lb2
    and ub' = ub1 +% ub2 in
    let u = lb1 &% lb2 &% bnot lb' &% bnot(ub1 &% ub2 &% bnot ub')
    and v = ((lb1 ^% lb2) |% bnot(lb1 ^% lb'))
      &% (bnot ub1 &% bnot ub2 &% ub')
    and highbit = highbit k
    in
      if (u |% v) &% highbit = highbit then
        top k
      else (uint64_gcd s1 s2, extend k lb', extend k ub')

  let add = renormbin add

  (** Negation of a strided interval *)
  let neg k ((s,lb,ub) as si) =
    check_reduced k si;
    if lb <> extend k (highbit k) then
      (s, I.neg ub, I.neg lb)
    else if lb = ub then
      single (mini k)
    else
      top k

  let neg = if debug() then renormun neg else neg

  (** Subtractionf of strided intervals *)
  let sub k a b =
    add k a (neg k b)


  let minor k a b c d =
    let rec loop m =
      let cont() = loop (I.shift_right_logical m 1) in
      if m = 0L then a |% c
      else if bnot a &% c &% m <> 0L then
        let temp = (a |% m ) &% I.neg m in
        if int64_ucompare temp b <= 0 then
          temp |% c
        else cont()
      else if a &% bnot c &% m  <> 0L then
        let temp = (c +% m) &% I.neg m in
        if int64_ucompare temp d <= 0 then
          temp  |% a
        else cont()
      else
        cont()
    in
    loop (highbit k)

  let maxor k a b c d =
    let rec loop m =
      let cont() = loop (I.shift_right_logical m 1) in
      if m = 0L then b |% d
      else if b &% d &% m <> 0L then
        let temp1 = (b -% m) |% (m -% 1L) in
        let temp2 = (d -% m) |% (m -% 1L) in
        if int64_ucompare temp1 a >= 0 then
          temp1 |% d
            else if int64_ucompare temp2 c >= 0 then
              temp2 |% b
            else cont()
      else
        cont()
    in
    loop (highbit k)

  let ntz x =
    let y = I.neg x &% (x -% 1L) in
    let rec bits n y =
      if y = 0L then n else bits (n+1) (I.shift_right y 1)
    in
    bits 0 y


  (** Bitwise OR *)
  let logor k ((s1,lb1,ub1) as a) ((s2,lb2,ub2) as b) =
    check_reduced2 k a b;
    let t = min (ntz s1) (ntz s2) in
    let s' = I.shift_left 1L t in
    let lowbits = (lb1 |% lb2) &% (s' -% 1L) in
    let (lb', ub') = match (lb1 < 0L, ub1 < 0L, lb2 < 0L, ub2 < 0L) with
      | (true, true, true, true)
      | (true, true, false, false)
      | (false, false, true, true)
      | (false, false, false, false) ->
        (minor k lb1 ub1 lb2 ub2, maxor k lb1 ub1 lb2 ub2)
      | (true, true, true, false) ->
        (lb1, -1L)
      | (true, false, true, true) ->
        (lb2, -1L)
      | (true, false, true, false) ->
        (min lb1 lb2, maxor k 0L ub1 0L ub2)
      | (true, false, false, false) ->
        (minor k lb1 (-1L) lb2 ub2, maxor k 0L ub1 lb2 ub2)
      | (false, false, true, false) ->
        (minor k lb1 ub1 lb2 (-1L), maxor k lb1 ub1 lb2 ub2)
      | _ -> failwith "Impossible: check_reduced prevents this"
    in
    let highmask = bnot(s' -% 1L) in
    (s', (lb' &% highmask) |% lowbits, (ub' &% highmask) |% lowbits)

  let logor = renormbin logor

  (** Bitwise NOT *)
  let lognot (_k:int) (s,l,u) =
    (s, bnot u, bnot l)

  let lognot = if debug() then renormun lognot else lognot

  (** Bitwise AND *)
  let logand k x y =
    lognot k (logor k (lognot k x) (lognot k y))

  (** Bitwise XOR *)
  let logxor k x y =
    let n = lognot k
    and o = logor k in
    o (n(o (n x) y)) (n(o x (n y)))

  (** FIXME: Signed or unsigned modulus? *)
  let modulus k (s1,a,b) (s2,c,d) =
    if b = 0L then single 0L
    else
      (1L,0L, int64_umin b d)

  let modulus = renormbin modulus

(* shifting by more than k or by negative values
 * will be the same as shifting by k. *)
  let toshifts k =
    let f x = if x > Int64.of_int k || x < 0L then k else Int64.to_int x in
    function
    | (0L,x,y) ->
      assert(x=y);
      let s = f x in  (s,s)
    | (_s,x,y) ->
      if x < 0L then
        if y >= 0L then
          (* FIXME: using stride information could be useful here *)
          (0, k)
        else (k,k)
      else (* x >= 0L *)
        (f x, f y)

  let mk_rshift shifter k ((s1,a,b) as x) y =
    check_reduced2 k x y;
    let (z1,z2) = toshifts k y
    and aa = trunc k a
    and bb = trunc k b
    and shift n z = extend k (shifter n z)in
    let a1 = shift aa z1
    and a2 = shift aa z2
    and b1 = shift bb z1
    and b2 = shift bb z2
    and s' = int64_umax (Int64.shift_right_logical s1 z2) 1L in
    let l = min (min a1 a2) (min b1 b2)
    and u = max (max a1 a2) (max b1 b2) in
    renorm k (s',l,u)

  (** Logical right-shift *)
  let rshift = mk_rshift Int64.shift_right_logical

  (*
   * Try to only handle the trivial cases, the BAP implementation
   * seems to get significantly confused in some cases. -- agg
   *)
  let rshift k ((scale, lb, ub) as x) y =
    check_reduced2 k x y;
    match y with
    | (0L, sw, sw') ->
      assert(Int64.compare sw sw' = 0);
      if sw > Int64.of_int k || sw < 0L then begin
        (* All the bits get shifted away *)
        (0L, 0L, 0L)
      end else begin
        let sw = I.to_int sw in
        let negate x =
          (* Two's complement: x = - x *)
          I.add (I.lognot x) I.one
        in
        let make_pos x =
          if I.compare x I.zero < 0 then
            (true, negate x)
          else
            (false, x)
        in
        let neg_lb, lb = make_pos lb in
        let neg_ub, ub = make_pos ub in

        dprintf "after make_pos: %s %s" (I.to_string lb) (I.to_string ub);
        let lb = I.shift_right_logical lb sw in
        let ub = I.shift_right_logical ub sw in
        dprintf "after shift_right_logical: %s %s" (I.to_string lb) (I.to_string ub);
        let lb = if neg_lb then negate lb else lb in
        let ub = if neg_ub then negate ub else ub in
        dprintf "after maybe_neg: %s %s" (I.to_string lb) (I.to_string ub);

        let ffs = match Misc.ffs scale with
          | None -> 0 (* No need to shift *)
          | Some x -> x (* Don't lose any 1s *)
        in
        let rshift = min sw ffs in
        dprintf "sw = %d, ffs = %d" sw ffs;
        let scale = I.shift_right_logical scale rshift in
        (scale, min lb ub, max lb ub)
      end
    | _ ->
      top k

  let rshift = renormbin rshift

  (** Arithmetic right-shift *)
  let arshift = mk_rshift Int64.shift_right

  let lshift k x y =
    check_reduced2 k x y;
    match y with
    | (0L, sw, sw') ->
      assert(Int64.compare sw sw' = 0);
      let open Big_int in
      let bi_mini = big_int_of_int64 (mini k) in
      let bi_maxi = big_int_of_int64 (maxi k) in
      if sw > Int64.of_int k || sw < 0L then begin
        (* All the bits get shifted away *)
        (0L, 0L, 0L)
      end else begin
        let sw = Int64.to_int sw in
        let (scale, lb, ub) = x in
        let saturated_shift sat b shift =
          let bi = big_int_of_int64 b in
          let bi = shift_left_big_int bi shift in
          if compare_big_int bi bi_mini < 0 then
            (true, mini k)
          else if compare_big_int bi bi_maxi > 0 then
            (true, maxi k)
          else
            (sat, Int64.shift_left b shift)
        in
        let sat = false in
        let sat, lb = saturated_shift sat lb sw in
        let sat, ub = saturated_shift sat ub sw in
        let scale =
          if sat then
            (*
             * If we reached saturation, then the scale has
             * to be 1. Otherwise we'll fail check_reduced.
             *)
            1L
          else
            Int64.shift_left scale sw
        in
        (scale, lb, ub)
      end
    | (_, _, _) -> (* Punt on non-constant shift *)
      top k

  let lshift = renormbin lshift

  let times k x y =
    check_reduced2 k x y;
    match (x, y) with
    | (0L, x, x'), (0L, y, y') ->
      assert (Int64.compare x x' = 0);
      assert (Int64.compare y y' = 0);
      let open Big_int in
      let x = big_int_of_int64 x in
      let y = big_int_of_int64 y in
      let bi = mult_big_int x y in
      let bi = extract_big_int bi 0 64 in
      let res = int64_of_big_int bi in
      (0L, res, res)
    | (0L, x, x'), y
    | y, (0L, x, x') ->
      (*
       * We have a SI times a constant. The scale will always be multiplied
       * by the constant. The bounds, however may wrap around. In that case,
       * we'd have to produce two SIs, [min_int ... blah], [bleh .. max_int],
       * which we can't represent. So in that case we use top.
       *)
      assert (Int64.compare x x' = 0);
      let open Big_int in
      let bi_mini = big_int_of_int64 (mini k) in
      let bi_maxi = big_int_of_int64 (maxi k) in
      let (scale, lb, ub) = y in
      let mult_detect_overflow a b =
        let a = big_int_of_int64 a in
        let b = big_int_of_int64 b in

        let res = mult_big_int a b in
        if compare_big_int res bi_mini < 0 then
          None
        else if compare_big_int res bi_maxi > 0 then
          None
        else
          Some (int64_of_big_int res)
      in
      let lb = mult_detect_overflow lb x in
      let ub = mult_detect_overflow ub x in
      begin
        match (lb, ub) with
        | Some lb, Some ub ->
          begin
            match mult_detect_overflow scale x with
            | Some scale ->
              (scale, lb, ub)
            | None ->
              top k
          end
        | _ -> top k
      end
    | _ ->
      (* Can't handle this yet *)
      top k

  let times = renormbin times

  (* construct these only once *)
  let yes = single (-1L)
  and no = single 0L
  and maybe = (1L, -1L, 0L)

  let eq k ((s1,a,b) as x) ((s2,c,d) as y) =
    check_reduced2 k x y;
    if a = b && a = c && a = d then
      yes
    else if b < c || d < a then
      no
    else
      let s' = uint64_gcd s1 s2 in
      let r1 = int64_urem a s'
      and r2 = int64_urem c s' in
      if r1 = r2 then
        maybe
      else
        no

  let union (s1,a,b) (s2,c,d) =
    let s' = uint64_gcd s1 s2 in
    if s' = 0L then
      if a = b && c = d then
        let u = max a c
        and l = min a c in
        (u -% l, l, u)
      else failwith "union: strided interval not in reduced form"
    else
      let r1 = I.rem a s' (* not right when s' is negative. *)
      and r2 = I.rem c s' in
      if s' > 0L && r1 = r2 then
        (s', min a c, max b d)
      else (1L, min a c, max b d)

  let union x y =
    let (a,b,c) as res = union x y in
    if b = c then (0L,b,b) else (check_reduced 64 res; res)


  let rec fold f (s,a,b) init =
    if a = b then f a init
    else fold f (s, a+%s ,b) (f a init)

end (* module SI *)

exception Would_return_top

(* Very simplified version of VSA, with no bounding *)
module SimpleVSA =
struct
  module DFP =
  struct
    module G = Cfg.SSA.G
    module L =
    struct
      type t = SI.t VM.t
      let top = VM.empty
      let equal = VM.equal (=)
      let meet x y =
        VM.fold
          (fun k v res ->
             try
               let v' = VM.find k y in
               let si = SI.union v v' in
               VM.add k si res
             with Not_found ->
               VM.add k v res
          )
          x y
    end
    let s0 _ = G.V.create Cfg.BB_Entry
    let init g = L.top
    let dir = GraphDataflow.Forward

    let binop_to_si_function avar_k = function
      | PLUS -> SI.add
      | MINUS -> SI.sub
      | AND -> SI.logand
      | OR -> SI.logor
      | XOR -> SI.logxor
      | MOD -> SI.modulus
      | RSHIFT -> SI.rshift
      | ARSHIFT -> SI.arshift
      | EQ -> SI.eq
      | NEQ -> fun k x y -> SI.lognot k (SI.eq k x y)
      | LSHIFT -> SI.lshift
      | TIMES -> SI.times
      | DIVIDE
      | SDIVIDE
      | SMOD
      | LT
      | LE
      | SLT
      | SLE -> (fun k _ _ -> SI.top avar_k)

    let unop_to_si_function = function
      | NEG -> SI.neg
      | NOT -> SI.lognot

    let bits_of_val = function
      | Int(_,t) -> bits_of_width t
      | Var v -> bits_of_width (Var.typ v)
      | Lab _ -> 64 (* FIXME *)

    let rec transfer_stmt s l =
      dprintf "looking at %s" (Pp.ssa_stmt_to_string s);
      match s with
      | Assert(Var _, _)  (* FIXME: Do we want to say v is true? *)
      | Assert _ | Jmp _ | CJmp _ | Label _ | Comment _
      | Halt _ ->
        l
      | Move(v, e, _) ->
        try
          let top v = SI.top (bits_of_width(Var.typ v)) in
          let find v = VM.find v l in
          let do_find v =  try find v with Not_found -> top v  in
          let val2si ?(raise_on_top=false) = function
            | Int(i,t) ->
              begin
                let bi = Arithmetic.to_sbig_int (i, t) in
                try
                  SI.of_bap_int (int64_of_big_int bi) t
                with Failure str as fail ->
                  dprintf "val2si: Fail: %s (%s, %s, %s)" str (Big_int_Z.string_of_big_int i) (Pp.typ_to_string t)
                    (Big_int_Z.string_of_big_int bi);
                  raise fail
              end
            | Lab _ -> raise(Unimplemented "No SI for labels (should be a constant)")
            | Var v ->
              if raise_on_top then begin
                raise Would_return_top
              end else begin
                do_find v
              end
          in
          try
            let new_si = match e with
              | Val x ->
                val2si x
              | BinOp(op, x, y) ->
                let f = binop_to_si_function (bits_of_width (Var.typ v)) op in
                let k = bits_of_val x in
                let r = f k (val2si x) (val2si y) in
                SI.check_reduced k r;
                r
              | UnOp(op, x) ->
                let f = unop_to_si_function op in
                let k = bits_of_val x in
                let r = f k (val2si x) in
                SI.check_reduced k r;
                r
              | Phi(x::xs) ->
                List.fold_left
                  (fun i y -> SI.union i (do_find y))
                  (do_find x) xs
              | Phi [] ->
                failwith "Encountered empty Phi expression"

(* This tries to preserve strides for loop variables, but takes too long, and
   wasn't working.
                    | Phi xs ->
                        let res = List.fold_left
                          (fun res y ->
                             try let l = find y in
                               match res with None -> Some l
                                 | Some l' -> Some(SI.union l l')
                             with Not_found -> res
                          )
                          None xs
                        in
                          (match res with
                             | Some l -> l
                             | None -> raise Not_found
                          )
*)
              | Cast(CAST_SIGNED, _, vl) ->
                val2si vl
              (* This can result in non-reduced SIs currently *)
              | Cast(CAST_UNSIGNED, t, vl) ->
                begin
                  let k = bits_of_val vl
                  and k' = bits_of_width t
                  and (s,a,b) as si = val2si  vl in
                  dprintf "YYY: vl %s, si %s" (Pp.value_to_string vl) (SI.to_string si);
                  let d = 64-k in
                  let f x = I.shift_right (I.shift_left x d) d in
                  if k <> 64 && k <> k' then begin
                    assert(k' > k);
                    (s, f a, f b)
                  end else
                    si
                end
              | Cast(CAST_HIGH, t, vl) ->
                let k = bits_of_val vl
                and k' = bits_of_width t
                and (s,a,b) as si = val2si vl in
                let f x = I.shift_right x (k - k') in
                let g scale =
                  (*
                   * We can (must) right shift the scale, as long as we
                   * don't lose any set bits.
                   *)
                  dprintf "scale is %s" (Int64.to_string scale);
                  let ffs = match Misc.ffs scale with
                    | None -> 0 (* No need to shift *)
                    | Some x -> x
                  in
                  let rshift = min (k - k') ffs in
                  dprintf "'k - k = %d, ffs = %d" (k - k') ffs;
                  I.shift_right_logical scale rshift
                in
                if k' <> k then begin
                  (g s, f a, f b)
                end else
                  si
              | Cast(CAST_LOW, t, vl) ->
                raise(Unimplemented "FIXME")
              | _ ->
                let str = Printf.sprintf "unimplemented expression type %s"
                    (Pp.ssa_exp_to_string e)
                in
                raise(Unimplemented str)
            in
            let new_si = SI.renorm (bits_of_width (Var.typ v)) new_si in
            if try VM.find v l <> new_si with Not_found -> true then begin
              dprintf "adding %s = %s" (Pp.var_to_string v) (SI.to_string new_si);
              VM.add v new_si l
            end else
              l
          with Unimplemented s | Invalid_argument s ->
            begin
              dprintf "%s" s;
              VM.add v (top v) l
            end
        with Invalid_argument _ | Not_found ->
          l

    let transfer_function = fwd_transfer_stmt_to_block transfer_stmt

  end

  module DF = GraphDataflow.Make(DFP)

end (* module SimpleVSA *)
