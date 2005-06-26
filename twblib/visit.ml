
open Llist

module Make (T:Tree.S) (S:Strategy.S) =
    struct
    open T
    (* generic depth first search. build is the function that builds the tree,
    * synth the function that synthethizes the result.
    * THIS IS THE TWB CORE *)
    (* S.last () unpop the strategy context stack *)
    let depth_first_builder_res build synth node =
        let (rule,context) = S.next node in
        let rec vis r c = 
            match build r c with
            |Tree(l) -> 
                    let n =
                        synth r (Llist.map (vis r c) l)
                    in let _ = S.last () in n
            |Leaf(_) as i ->
                    let n =
                        synth r (LList(i,lazy(Empty)))
                    in let _ = S.last () in n
        in vis rule context 

    end
