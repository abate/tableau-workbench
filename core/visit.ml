
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

    let rec aux_visit traversal str state node =
        Llist.bind (str node) (fun ((rule,context),newstate) ->
            match newstate,state with
            |[],[] -> 
                    Llist.return (rule#up context (
                        match rule#down context with
                        |Leaf(_) as tree -> Llist.return (tree)
                        |Tree(l) -> Llist.map (fun n -> Leaf(n)) l
                    ))

            |[], Cont(hd) :: tl ->
                    traversal hd rule context tl (rule#down context)
            
            |Cont(hd) :: tl, _ ->
                    (traversal hd rule context (tl@state) (rule#down context))
        )

    and dfs str rule context state = function
        |Leaf(_) as tree ->
                Llist.return (rule#up context (Llist.return tree))
        |Tree(l) -> 
                let res =
                    Llist.bind l
                    (memo_visit ~cache:rule#use_cache dfs str state)
                in
                if Llist.is_empty res then 
                    Llist.return (rule#up context (
                        Llist.map (fun n -> Leaf(n)) l
                        )
                    )
                else Llist.return (rule#up context res)

    and memo_visit ?(cache=false) dfs str state node =
        if cache then
            try !table#find node 
            with Not_found ->
                let res = aux_visit dfs str state node in
                !table#add node res;
                res
        else
            aux_visit dfs str state node
    ;;

    let visit cache str node =
        table := cache;
        memo_visit dfs str [] node 

end
