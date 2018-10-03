open Sexplib.Std

type bbcmp_counts = {
  n_total : int;
  n_partial : int;
  n_sub : int;
  n_sup : int;
} with sexp
  (*
   * Interpretation of typical classification results:
   * (ExactOnly, OverlapTotal) -> I/O Equivalent functions (strict)
   *   For every output location of the LHS function, we have declared
   *   it equivalent to an output location of the RHS function and vice-versa.
   * (ExactOnly, OverlapSubset) -> LHS inlined in the RHS (strict)
   *   Not only that, but it so happens that the BBs of the inlined function
   *   are entirely separate from those of the caller (not that we care about
   *   that distinction).
   * (SubsetAndExact, OverlapTotal) -> LHS inlined in the RHS (strict)
   *   Even though we have total CFG coverage, there are additional outputs
   *   on the RHS, so the functions are not equivalent, but the RHS effects
   *   all the computations and side-effects of the LHS.
   * (SubsetAndExact, OverlapSubset) -> LHS inlined in the RHS (strict)
   *   Again, there are additional outputs/computation in the RHS, so that
   *   this is simply in inlining site of the LHS.
   * <Respectively for Superset>
   * (Fuzzy, OverlapTotal ^ OverlapSuperset ^ OverlapSubset) -> fuzzy inline
   *   This _looks_ like something was inlined here but, depending on the
   *   number of partials in our fragment, we can't say much.
   *)
type fuzziness =
  | ExactOnly
  | SubsetAndExact
  | SupersetAndExact
  | Fuzzy of (float * bbcmp_counts) with sexp

type overlap =
  | OverlapTotal of int
  | OverlapSubset of int
  | OverlapSuperset of int
  | OverlapPartial of (int * int) with sexp

type cfgcmp_res = {
  fuzziness : fuzziness;
  overlap : overlap;
}

type func_cmp_flags =
      (*
       * CFGs isomorphic and the Ast statements just after lifting are
       * exactly the same modulo variable indices, labels and attributes.
       *)
  | FIdenticalFunctions
      (*
       * Functions had isomorphic CFGs right after lifting (i.e. converting
       * the unmodified stmts to an AST CFG w/o going through our pipeline).
       *)
  | FIsomorphicVanilla
      (*
       * Function CFGs are isomorphic after all passes. If this flag is not
       * set, we cannot hope to get an exact match.
       *)
  | FIsomorphicFinal with sexp

let cfgcmp_res_of_sexp sexp =
  let open Sexplib.Sexp in
  match sexp with
  | List [Atom "classification"; fuzz; overlap;] ->
    begin
      {
        fuzziness = fuzziness_of_sexp fuzz;
        overlap = overlap_of_sexp overlap;
      }
    end
  | _ ->
    let s = Printf.sprintf "cfgcmp_res_of_sexp: %s" (to_string_hum sexp) in
    failwith s

let cfgcmp_res_to_sexp res =
  Sexplib.Sexp.List [Sexplib.Sexp.Atom "classification";
             sexp_of_fuzziness res.fuzziness;
             sexp_of_overlap res.overlap;]

let cfgcmp_res_to_string res =
  let open BatPervasives in
  res |> cfgcmp_res_to_sexp |> Sexplib.Sexp.to_string_hum
