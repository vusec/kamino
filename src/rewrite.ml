module D = Debug.Make(struct let name = "Rewrite" and default=`Debug end)
open D

module type Lang = sig
  module Exp : sig
    type t
    val walk : t -> (t -> t) -> t
    val is_equal : t -> t -> bool
    val to_string : t -> string
  end
end

module type Rule = sig
    type t
    type term

    val create : string -> ?description:string -> (term -> term) -> t

    val name : t -> string
    val description : t -> string
    val apply : t -> term -> term
end

module Ssa_ext = struct
  module Exp = Ssa_ext.Expression

  module Lang : Lang with type Exp.t = Exp.t =
  struct
    module Exp = struct
      type t = Exp.t
      let walk e f =
        let open Ssa_ext_visitor in
        let visitor = object(self)
          inherit rnop
          method visit_exp e =
            ChangeTo (f e)
        end in
        exp_accept visitor e

      let is_equal = Exp.equal

      let to_string e = Exp.to_string e
    end
  end

  module ExpRule : Rule with type term := Exp.t = struct
    type t = {
      name: string;
      description: string;
      f: Exp.t -> Exp.t
    }

    let create name ?(description="") f =
      {name; description; f}

    let name t = t.name
    let description t = t.description
    let apply t exp = t.f exp
  end

end

module Make_exp(L:Lang)(R:Rule with type term := L.Exp.t) = struct
    let rewrite rules exp =
      let apply_rule exp rule =
        dprintf "Trying rule '%s' (%s) on:\n%s" (R.name rule)
          (R.description rule) (L.Exp.to_string exp);
        let exp' = R.apply rule exp in
        if not (L.Exp.is_equal exp exp') then
          dprintf "Successfully rewrote %s -> %s"
            (L.Exp.to_string exp)
            (L.Exp.to_string exp');
        exp'
      in
      let apply_rules exp = List.fold_left apply_rule exp rules in
      let rec fixpoint_apply exp =
        let exp' = L.Exp.walk exp apply_rules in
        if L.Exp.is_equal exp exp' then exp'
        else fixpoint_apply exp' in
      fixpoint_apply exp
end

module Ssa_ext_exp_rewriter = Make_exp(Ssa_ext.Lang)(Ssa_ext.ExpRule)
