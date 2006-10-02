
open Tree
open Llist

module Make(N:Node.S)
            (R:Rule.S with type node = N.node)
            (S:Strategy.S
            with type rule = R.rule
            with type node = R.node
            with type context = R.context
            )
(*:
    sig
        val visit : (S.node -> S.m) -> R.node -> R.tree Llist.llist
    end
*)
= struct

    module Cache = Cache.Make(N)
    open S

    let table = ref (new Cache.cache true)

    let tl s =
        try Llist.tl s
        with Llist.LListEmpty -> Llist.empty

    let rec aux_visit traversal str state node =
        Llist.ifte
        (str node)
        (fun ms ->
            let ((rule,context),newstate) = ms state in
            Llist.bind (Llist.determ(newstate)) (fun (MState.Cont cont) ->
                traversal cont (tl(newstate)) rule context (rule#down context)
            )
        )
        (
            Llist.ifte
            (Llist.determ(state))
            (fun (MState.Cont cont) -> memo_visit traversal cont (tl(state)) node)
            (Llist.return (Leaf(node)))
        )

    and dfs str state rule context = function
        |Leaf(_) as tree -> Llist.return (rule#up context (Llist.return tree))
        |Tree(l) -> Llist.return (
            rule#up context (Llist.bind l (memo_visit ~cache:rule#use_cache dfs str state)))

    and memo_visit ?(cache=false) dfs strategy state node =
        if cache then
            try !table#find node 
            with Not_found ->
                let res = aux_visit dfs strategy state node in
                !table#add node res;
                res
        else aux_visit dfs strategy state node
    ;;

    let visit cache strategy node =
        table := cache;
        memo_visit dfs strategy Llist.empty node 

end
