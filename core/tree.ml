
type 'a tree =
    |Tree of 'a Llist.llist
    |Leaf of 'a

type 'a result =
    |Node of 'a
    |TacticError
