class base_indir : string ->
  object
    method npairs : int
    method path : string
  end

class summarized_indir : string ->
  object
    inherit base_indir
    method nclusters : int
  end

class completed_indir : string ->
  object
    inherit summarized_indir
    method success : (unit, string list) BatResult.t
  end

class successful_indir : string ->
  object
    inherit completed_indir
    method nresults : int
  end

type states = {
  bare: base_indir list;
  summarized: summarized_indir list;
  completed: completed_indir list;
  successful: successful_indir list;

}

val states_to_str : states -> string
val states_in_progress : states -> int
val states_total : states -> int
val states_aggregate : states -> states -> states
val binary_states : string list -> states
