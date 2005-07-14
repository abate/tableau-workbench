
type 'a tree =
    |Tree of 'a Llist.llist
    |Leaf of 'a

    (*
module type S =
    sig
        type node 
        type tree
    end

module Make(N : sig type node end) = 
    struct
        type node = N.node
        type tree = node t
    end
*)
