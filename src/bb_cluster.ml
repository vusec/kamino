module D = Debug.Make(struct let name = "Bb_cluster" and default=`Debug end)
open D

module HashableString = Misc.HashableString;;
module StringHashtbl = BatHashtbl.Make(HashableString)

(* XXX For now we hardcode the cluster description, but really should be passed to a functor *)
type cluster_description = string * BatBitSet.t * BatBitSet.t list

let cluster_name (name,_,_) = name
(*
  A collection of BBs that share some common property.
  The idea is that we compare BBs from different binaries
  by comparing bbclusters that share a given property
*)
type cluster_elem = Bb.bb_summary
type cluster_elems = cluster_elem BatSet.t
type cluster = cluster_description * cluster_elems

let cluster_to_string cl =
  let elems = BatList.of_enum (BatSet.enum cl) in
  let to_s bbsum =  Cfg.bbid_to_string bbsum.Bb.id in
  Print.list_to_string ~enclosing:("(", ")") ~sep:", " to_s elems

module HashableCluster =
struct
  type t = cluster_description

  let equal d1 d2 = (cluster_name d1) = (cluster_name d2)

  let hash d = BatHashtbl.hash (cluster_name d)
end

module ClusterHashtbl = BatHashtbl.Make(HashableCluster)

type classifier_config = HashableString.t list StringHashtbl.t
(* Classifies a given BB into a cluster. Clusters are keyed by name *)
module type BBClassifierSig =
sig
  val classify : classifier_config -> Ktype.analyzed_func -> Bb.bb_summary -> cluster_description list
end;;


module type BBClusterManagerSig =
sig
  type t
  val create : Ktype.analyzed_prog -> t
  val dump : t -> unit
  val add : t -> Ktype.analyzed_func -> Bb.bb_summary -> unit
  val add_config : t -> string -> string -> unit
  val get_cluster : t -> cluster_description -> cluster_elems option
  val keys : t -> cluster_description BatEnum.t
  val values : t -> cluster_elems BatEnum.t
  val enum : t -> cluster BatEnum.t
  val get_classifier_config : t -> classifier_config
end;;

(* Holds the identified bbclusters for a program *)
module BBClusterManager = functor (Classifier : BBClassifierSig) ->
struct
  module Htbl = ClusterHashtbl
  type t = (cluster_elems ClusterHashtbl.t * Ktype.analyzed_prog * classifier_config)
  let create priv = (ClusterHashtbl.create 10, priv, StringHashtbl.create 8 )
  let dump (htbl, _, _) =
    ClusterHashtbl.iter (fun k v ->
        dprintf "key: %s elems: %s" (cluster_name k) (cluster_to_string v)
      ) htbl
  let add (clustermgr, priv, config) afunc bb_summary =
    let skip = match bb_summary.Bb.tfs with
      | None -> true
      | Some _ -> false in
    if not skip then begin
      let klasses = Classifier.classify config afunc bb_summary in
      List.iter (fun klass ->
          let prev_cluster =
            try
              Some (ClusterHashtbl.find clustermgr klass)
            with Not_found ->
              None
          in
          let ncluster = match prev_cluster with
            | Some cluster ->
              BatSet.add bb_summary cluster
            | None -> BatSet.add bb_summary BatSet.empty
          in
          (* also works as 'add' *)
          ClusterHashtbl.replace clustermgr klass ncluster) klasses
    end
  let add_config (_,_,config) key value =
    let values = StringHashtbl.find_default config key [] in
    StringHashtbl.replace config key (value :: values)
  let get_cluster (cmgr,_,_) k =
    if ClusterHashtbl.mem cmgr k
    then Some (ClusterHashtbl.find cmgr k)
    else None
  let keys (cmgr,_,_) = ClusterHashtbl.keys cmgr
  let values (cmgr,_,_) = ClusterHashtbl.values cmgr
  let enum (cmgr,_,_) = ClusterHashtbl.enum cmgr
  let get_classifier_config (_,_,conf) = conf
end;;

module BBClassifyByFunc =
struct
  let classify _ afunc bbsum =
    List.map (fun fname ->
        (fname, BatBitSet.empty (), []))
      (Function_info.Function.symbols afunc.Ktype.function_info)
end;;

(* Just a proof of concept *)
module BBClassifyByCardinality =
struct
  let classify _ _ bbsum =
    match bbsum.Bb.tfs with
    | None -> []
    | Some tfs ->
      let module StringMap = BatMap.Make(String) in
      [(Printf.sprintf "%d" (StringMap.cardinal tfs),
       BatBitSet.empty (), [])]
end;;

module ClassifyByMeasureVector =
struct
  let classify config afunc bbsum =
    dprintf "CLASSIFY: %s %s" (Function_info.Function.to_string afunc.Ktype.function_info)
      (Cfg.bbid_to_string bbsum.Bb.id);
    let measures = [(module Measure.BbTransferFunctionCardinality : Measure.S);]
    in
    let feature_list = List.map (fun m ->
      let module M = (val m : Measure.S) in
        (* We measure output expressions separately and pass a nil to comply with the interface. *)
      M.measure (afunc,bbsum, Ssa_ext.Expression.Unknown ("nil",Type.Reg 1))
    ) measures
    in
    let bits_per_feature = 8 in
    let to_bitset featlist =
      let set_8bits_at bitset idx value =
        assert (value >= 0);
        assert (value < 256);
        List.fold_left (fun bitset i ->
          dprintf "value = %d, i = %d" value i;
          match (value lsr i) land 1 with
          | 0 ->
            bitset
          | 1 ->
            dprintf "setting bit at idx %d" (idx + i);
            BatBitSet.set bitset (idx + i);
            bitset
          | _ -> failwith "can't get here"
        ) bitset [0; 1; 2; 3; 4; 5; 6; 7;]
      in
      let (bs, _) = List.fold_left (fun (bitset, idx) feat ->
        let feat = feat mod (bits_per_feature * 8) in
        let nbitset = set_8bits_at bitset idx feat in
        (nbitset, idx + 8)
      ) (BatBitSet.empty (), 0) featlist
      in
      bs
    in
    let string_of_bitset bs =
      let str = BatIO.output_string () in
      BatBitSet.print str bs;
      BatIO.close_out str
    in
    let featbits = to_bitset feature_list in
    dprintf "feature_list: %s"
        (Print.list_to_string (Printf.sprintf "%02i") feature_list);
    let bitstr = string_of_bitset featbits in
    dprintf "bitset: %s" bitstr;
    [(bitstr, BatBitSet.empty (), [])]
end

module BBClassifyByTag =
struct
  let classify config func _ =
    match Function_info.Function.begin_address func.Ktype.function_info with
    | Some addr -> begin
        match StringHashtbl.find_option config (Int64.to_string addr) with
        | Some tags ->
           List.fold_left
             (fun acc tag -> (tag, BatBitSet.empty (), []) :: acc) [] tags
        | None -> []
      end
    | None -> []
end

(* We use this to be able to reference the .t type easily *)
(* module ByFunc = BBClusterManager(BBClassifyByFunc);; *)

(* module type BBClusterManagerConcreteSig = module type of ByFunc;; *)

let bbclustermanagerfactory str =
  let module Classifier = (val (match str with
  | "ByFunc" -> (module BBClassifyByFunc : BBClassifierSig)
  | "ByCard" -> (module BBClassifyByCardinality : BBClassifierSig)
  | "ByMeasureVector" -> (module ClassifyByMeasureVector : BBClassifierSig)
  | "ByTag" -> (module BBClassifyByTag : BBClassifierSig)
  | _ -> failwith (Printf.sprintf "Unknown classifier: %s" str))
      : BBClassifierSig) in
  let module Ret = BBClusterManager(Classifier) in
  (module Ret : BBClusterManagerSig)
