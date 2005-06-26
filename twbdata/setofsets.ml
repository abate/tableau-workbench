
open Basictype
open Store
open Sets

type mixtype1 = [
    |`Set of set
    |mixtype
]
;;

module SetofSet = OriginalSet.Make (
        struct
            type t = mixtype1
            let compare = compare
        end
);;

class setofset =
    object
        inherit [mixtype1] store_open
        val mutable data = SetofSet.empty

        method data = data
        method assign s = {< data = s#data >}
        method add e = {< data = SetofSet.add e data >}
        (* XXX *)
        method del e = {< >}
        method export =
            Cont (
                List.map (function
                    |`Set e -> (e#export: mixtype ext_rep_open :> mixtype1
                    ext_rep_open)
                    |#mixtype1 -> failwith "setofset - export: wrong type"
                    ) (SetofSet.elements data)
                )
        method copy = {< data = data >}
    end
;;

