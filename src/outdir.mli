val set_outdir : string -> unit
val get_outpath : ?append:bool -> string -> out_channel
val with_file_out : ?append:bool -> string -> (out_channel -> 'a) -> 'a
