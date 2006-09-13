
(* define all basic data types *)

module Type =
    struct
        type t = Comptypes.mixlist
        type bt = Basictype.mixtype
    end

module Fmap = Gmap.Make(
    struct
        type t = Type.bt
        type c = Comptypes.Set.set
        let make () = new Comptypes.Set.set
    end)

(*
with Comptypes.Mtlist.listobj are multisets
*)
module FmapM = Gmap.Make(
    struct
        type t = Type.bt
        type c = Comptypes.Mtlist.listobj
        let make () = new Comptypes.Mtlist.listobj
    end)

module Hmap = Hmap.Make(
    struct
        type t = Type.t
        let copy = Comptypes.copy
        let to_string = Comptypes.string_of_mixlist
    end
)

module Store =
    struct
        type store = Fmap.map
        let copy s = s#copy
        let to_string s = s#to_string
        let make () = new Fmap.map
    end

module History =
    struct
        type store = Hmap.map
        let copy s = s#copy
        let to_string s = s#to_string
        let make () = new Hmap.map
    end

module Variable =
    struct
        type store = Hmap.map
        let copy s = s#copy
        let to_string s = s#to_string
        let make () = new Hmap.map
    end

type history_type = History | Variable

module Substitution = Sbl.Make
