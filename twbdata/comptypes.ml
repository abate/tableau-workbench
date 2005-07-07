
open Basictype

module Set = Sets.Make(
    struct
        type t = Basictype.mixtype
        let copy = Basictype.copy
        let to_string = Basictype.string_of_mixtype
    end
)

module Setofsets = Sets.Make(
    struct
        type t = Set.set
        let copy s = s#copy 
        let to_string v = v#to_string
    end
)

module Setoftupleset = Sets.Make(
    struct
        type t = (Set.set * Set.set)
        let copy (s1,s2) = (s1#copy, s2#copy)
        let to_string (v1,v2) =
            Printf.sprintf "(%s,%s)" v1#to_string v2#to_string
    end
)

module Mtlist = Listobj.Make(
     struct
        type t = Basictype.mixtype
        let copy = Basictype.copy
        let to_string = Basictype.string_of_mixtype
    end   
)

type mixlist = [
    |`L of Mtlist.listobj
    |`S of Set.set
    |`SS of Setofsets.set
    |`SoTS of Setoftupleset.set
    |mixtype
]

let copy s = 
    match s with
    |`L(l) -> `L(l#copy)
    |`S(s) -> `S(s#copy)
    |`SS(s) -> `SS(s#copy)
    |`SoTS(s) -> `SoTS(s#copy)
    |#mixtype as mt -> Basictype.copy mt

let string_of_mixlist = function
    |`L(l) -> l#to_string 
    |`S(s) -> s#to_string
    |`SS(s) -> s#to_string
    |`SoTS(s) -> s#to_string
    |#mixtype as mt -> Basictype.string_of_mixtype mt
