
module Set = Sets.Make(
    struct
        type t = Basictype.mixtype
        let copy = Basictype.copy
        let to_string = Basictype.string_of_mixtype
    end
)

module Mtlist = Listobj.Make(
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

module Listoftupleset = Listobj.Make(
    struct
        type t = (Set.set * Set.set)
        let copy (s1,s2) = (s1#copy, s2#copy)
        let to_string (v1,v2) =
            Printf.sprintf "(%s,%s)" v1#to_string v2#to_string
    end
)


module Listofsets = Listobj.Make(
     struct
        type t = Set.set
        let copy s = s#copy 
        let to_string v = v#to_string
    end   
)
;;

type mixlist = [
    |`Mtlist of Mtlist.listobj
    |`Listofsets of Listofsets.listobj
    |`Set of Set.set
    |`Setofsets of Setofsets.set
    |`Setoftupleset of Setoftupleset.set
    |`Listoftupleset of Listoftupleset.listobj
]

let copy : mixlist -> mixlist = function 
    |`Mtlist(l) -> `Mtlist(l#copy)
    |`Listofsets(l) -> `Listofsets(l#copy)
    |`Set(s) -> `Set(s#copy)
    |`Setofsets(s) -> `Setofsets(s#copy)
    |`Setoftupleset(s) -> `Setoftupleset(s#copy)
    |`Listoftupleset(s) -> `Listoftupleset(s#copy)

let string_of_mixlist : mixlist -> string = function
    |`Mtlist(l) -> l#to_string 
    |`Listofsets(l) -> l#to_string 
    |`Set(s) -> s#to_string
    |`Setofsets(s) -> s#to_string
    |`Setoftupleset(s) -> s#to_string
    |`Listoftupleset(s) -> s#to_string
