
open Tree
open Llist

module Make(N:Node.S)
            (R:Rule.S with type node = N.node)
            (S:Strategy.S
            with type rule = R.rule
            with type node = R.node
            with type context = R.context
            )
(* :
    sig
        val visit : (S.node -> S.ans) -> S.node -> R.tree
    end
*)
= struct
    
    let ex = function
        |S.Cont h -> h
        |S.Nil -> (fun _ -> [])

   module Cache = Cache.Make(N)

   let table = ref (new Cache.cache)

   let rec traversal rule context str cont = function
        |Leaf(_) as tree -> rule#up context (Llist.of_list [tree])
        |Tree(l) -> rule#up context (Llist.map (aux_visit rule#use_cache str cont) l)

    and aux_visit cache strategy cont =
        fun node ->
            (* here we try to save time by caching previously computed 
             * results *)
            try !table#find node with
            Not_found ->
                let result =
                    try
                        begin match strategy node with
                        |(rule,cxt,h::l)::_ ->
                                traversal rule cxt (ex h) (l@cont) (rule#down cxt)
                        |(rule,cxt,[])::_ -> 
                                begin match cont with
                                |h::l -> traversal rule cxt (ex h) (l) (rule#down cxt)
                                |[] -> (rule#down cxt)
                                end
                        |[] -> Leaf(node)
                        end
                    with (S.NoMoreRules newnode) ->
                        begin match cont with
                        |h::l -> aux_visit cache (ex h) l newnode
                        |[] -> Leaf(newnode)
                        end
                in
                if cache
                then begin !table#add node result; result end
                else result

    let visit cache strategy node =
        table := cache; 
        aux_visit false strategy [] node

end
