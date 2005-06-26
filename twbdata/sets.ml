
open Basictype
open Store

module OriginalSet = Set

module Set = OriginalSet.Make (
        struct
            type t = mixtype
            let compare = compare
        end
);;

class set =
    object
        inherit [mixtype] store_open
        val mutable data = Set.empty

        method data = data
        method assign s = {< data = s#data >}
        method add e = {< data = Set.add e data >}
        (* XXX *)
        method del e = {< >}
        method export = El(Set.elements data)
        method copy = {< data = data >}
    end
;;

(*
let add t <set(s)> = Set.add t s
let add t = function
|`S(s)::[] -> s#assign (Set.add t s#data)
|_ -> failwith "add: wrong parameters"


let compare <set(s1),set(s2)> = Set.compare s1 s2
let compare = function
|`S(s1)::`S(s2)::[] -> Set.compare s1#data s2#data
|_ -> failwith "compare: wrong parameters"


let add <set(s1),setofsets(s2)> = SetofSets.add s1 s2
let add = function
|`S(s1)::`SS(s2)::[] -> SetofSets.add s1#data s2#data
|_ -> failwith "add: wrong parameters"
*)

