
open Llist

module type S =
    sig
        type node 
        type tree =
            |Tree of node llist
            |Leaf of node
    end

module Make(N : sig type node end) = 
    struct
        type node = N.node
        type tree =
            |Tree of node llist
            |Leaf of node
    end

