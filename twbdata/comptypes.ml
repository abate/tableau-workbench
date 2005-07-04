
open Basictype
open Listobj

module Set = Sets.Make(struct type t = Basictype.mixtype end)

module Setofsets = Sets.Make(
    struct type t = [
        |Basictype.mixtype 
        |`Set of Set.set
    ]
    end
)

module Setoftupleset = Sets.Make(
    struct type t = [
        |Basictype.mixtype 
        |`TupleofSet of (Set.set * Set.set)
    ]
    end
)

type mixlist = [
    |`L of mixtype listobj
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
    |`L(l) -> l#string_of Basictype.string_of_mixtype 
    |`S(s) -> s#string_of Basictype.string_of_mixtype
    |`SS(s) -> s#string_of Set.string_of
    |`SoTS(s) -> s#string_of Setoftupleset.string_of
    |#mixtype as mt -> Basictype.string_of_mixtype mt
