module D = Debug.Make(struct let name = "Outdir" and default=`NoDebug end)
open D

let outdir = ref None

let set_outdir path =
  assert(!outdir = None);
  outdir := Some path;
  let error s err =
    match err with
    | `DirnameAlreadyUsed _ -> ()
    | _ -> failwith s
  in
  FileUtil.mkdir ~error ~parent:true path

let get_outpath ?(append=false) =
  let htbl = BatHashtbl.create 100 in
  let rec get key =
    try
      let oc = BatHashtbl.find htbl key in
      (try
         ignore(Unix.descr_of_out_channel oc);
         oc
       with Sys_error "Bad file descriptor" ->
         (*
          * If the user closed the out_channel, simply
          * remove it from the hashtable and restart
          *)
         BatHashtbl.remove htbl key;
         get key)
    with Not_found ->
      (match !outdir with
      | None -> stdout
      | Some p ->
        let fullpath = Printf.sprintf "%s/%s" p key in
        let dn = FilePath.dirname fullpath in
        dprintf "fullpath: %s" fullpath;
        dprintf "dirname: %s" dn;
        if 0 <> String.compare dn p then begin
        let error s err =
            match err with
            | `DirnameAlreadyUsed _ -> ()
            | _ -> failwith s
            in
            FileUtil.mkdir ~error ~parent:true dn
        end;
        let oc = match append with
          | true -> open_out_gen [Open_creat; Open_append] 0o600 fullpath
          | false -> open_out fullpath in
        BatHashtbl.add htbl key oc;
        oc)
  in
  get

let with_file_out ?(append=false) filename f =
  let oc = get_outpath ~append filename in
  let finalizer () = if oc != stdout then close_out oc in
  Misc.finally finalizer f oc
