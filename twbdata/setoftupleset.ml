
open Basictype
open Store
open Sets

type mixtype2 = [
    |`TupleofSet of (set * set)
    |mixtype
]

module SetofTupleSet = OriginalSet.Make (
        struct
            type t = mixtype2
            let compare = compare
        end
)

class setoftupleset =
    object
        inherit [mixtype2] store_open
        val mutable data = SetofTupleSet.empty

        method data = data
        method assign s = {< data = s#data >}
        method add e = {< data = SetofTupleSet.add e data >}
        (* XXX *)
        method del e = {< >}
        method export =
            Cont (
                List.map (function
                    |`TupleofSet (e1,e2) ->
                            Cont([
                                (e1#export: mixtype ext_rep_open :> mixtype2
                                ext_rep_open);
                                (e2#export: mixtype ext_rep_open :> mixtype2
                                ext_rep_open)
                            ])
                    |#mixtype2 -> failwith "setoftupleset - export: wrong type"
                    ) (SetofTupleSet.elements data)
                )
        method copy = {< data = data >}
    end


