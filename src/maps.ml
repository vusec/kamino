(* Define polymorphic maps with integer keys.  *)
module IntMap = Map.Make(BatInt)
module Int32Map = Map.Make(Int32)
module Int64Map = Map.Make(Int64)
