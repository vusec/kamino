module TaintOrder = struct
    type t = Type.taint_type
    let compare = Pervasives.compare
end

module TaintSet = Set.Make(TaintOrder)
