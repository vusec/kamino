type range = (int64 * int64) list

type fn_loc = {
  name: string;
  range: range;
}

type ranges = {
  ranges: range list;
}

type inline_instance = {
  caller: fn_loc;
  inline: fn_loc;
  callees: ranges;
}

type binary_inline_info = {
  binary: string;
  inlines: inline_instance list;
}

val binary_inline_info_from_file : string -> binary_inline_info
val spec_of_inline_info : string -> string option
val spec_for_binary_self_scan : string -> string option
val dump_example : unit -> unit
