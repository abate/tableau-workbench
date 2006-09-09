
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

module Setoftermint = Sets.Make(
    struct
        type t = (Basictype.mixtype * int)
        let copy (t,i) = (t,i)
        let to_string (t,i) =
            Printf.sprintf "(%s,%d)" (Basictype.string_of_mixtype t) i
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
    |`List of Mtlist.listobj
    |`ListSet of Listofsets.listobj
    |`Set of Set.set
    |`Singleton of Set.set
    |`SetSet of Setofsets.set
    |`SetFormulaInt of Setoftermint.set
    |`SetSetSet of Setoftupleset.set
    |`ListSetSet of Listoftupleset.listobj
]

let copy : mixlist -> mixlist = function 
    |`List(l) -> `List(l#copy)
    |`ListSet(l) -> `ListSet(l#copy)
    |`Set(s) -> `Set(s#copy)
    |`Singleton(s) -> `Singleton(s#copy)
    |`SetSet(s) -> `SetSet(s#copy)
    |`SetFormulaInt(s) -> `SetFormulaInt(s#copy)
    |`SetSetSet(s) -> `SetSetSet(s#copy)
    |`ListSetSet(s) -> `ListSetSet(s#copy)

let string_of_mixlist : mixlist -> string = function
    |`List(l) -> l#to_string 
    |`ListSet(l) -> l#to_string 
    |`Set(s) -> s#to_string
    |`Singleton(s) -> s#to_string
    |`SetSet(s) -> s#to_string
    |`SetFormulaInt(s) -> s#to_string
    |`SetSetSet(s) -> s#to_string
    |`ListSetSet(s) -> s#to_string
