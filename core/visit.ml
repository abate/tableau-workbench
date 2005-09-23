
open Llist
open Tree

module Make (R:Rule.S) (S: Strategy.S 
    with type rule = R.rule 
    with type node = R.node
    with type context = R.context
) =
    struct
        (* generic depth first search.
         * THIS IS THE TWB CORE *)
        (* XXX: the default here is Open for NoMoreRules, but it should
         * be user defined *)
        let rec visit strategy state node =
            try
                let (rule,context,newstate) = strategy#next state node in
                match rule#down context with
                |Tree(l) -> rule#up (Llist.map (visit strategy newstate) l)
                |Leaf(_) as n -> rule#up (LList(n,lazy(Empty)))
            with Strategy.NoMoreRules -> Leaf(node)

    end
