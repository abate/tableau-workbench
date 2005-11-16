
open Llist
open Tree

module Make (N: Node.S)
    (C: Cache.S with type node = N.node)
    (R: Rule.S with type node = N.node)
    (S: Strategy.S 
    with type rule = R.rule 
    with type node = R.node
    with type context = R.context)
    :
        sig
            val visit : C.cache -> S.strategy -> S.state -> N.node -> R.tree
            val visit_nocache : S.strategy -> S.state -> N.node -> R.tree
            val visit_min : S.strategy -> S.state -> N.node -> R.tree
        end
= struct

    let is_none = function None -> true | _ -> false
    let is_some e = not(is_none e)
    let get = function None -> raise Not_found |Some(n) -> n

    let visit (cache : C.cache) ( strategy : S.strategy ) state node =
        let rec __visit strategy state ?resnode node =
            try
                let (rule,context,newstate) =
                    strategy#next state resnode node
                in
                let resultnode () = 
                    match rule#down context with
                    |Tree(l) ->
                            begin match
                            rule#up context
                            (Llist.map (fun n -> __visit strategy newstate n) l)
                            with Leaf(n) -> n |_ -> failwith "visit" end
                    |Leaf(_) as n -> 
                            begin match
                            rule#up context (LList(n,lazy(Empty)))
                            with Leaf(n) -> n |_ -> failwith "visit" end
                in
                if cache#mem node then
                    __visit strategy newstate ~resnode:(get(cache#find node)) node
                else 
                    let res = resultnode () in
                    let _ = cache#add node res in
                    __visit strategy newstate ~resnode:res node
            with Strategy.NoMoreRules ->
                if is_none resnode then Leaf(node)
                else Leaf(get resnode)
        in __visit strategy state node

    let visit_nocache ( strategy : S.strategy ) state node =
        let rec __visit strategy state ?resnode node =
            try
                let (rule,context,newstate) =
                    strategy#next state resnode node
                in
                let resultnode = 
                    match rule#down context with
                    |Tree(l) ->
                            begin match
                            rule#up context
                            (Llist.map (fun n -> __visit strategy newstate n) l)
                            with Leaf(n) -> n |_ -> failwith "visit" end
                    |Leaf(_) as n -> 
                            begin match
                            rule#up context (LList(n,lazy(Empty)))
                            with Leaf(n) -> n |_ -> failwith "visit" end
                in __visit strategy newstate ~resnode:resultnode node
            with Strategy.NoMoreRules ->
                if is_none resnode then Leaf(node)
                else Leaf(get resnode)
        in __visit strategy state node

    let visit_min ( strategy : S.strategy ) state node =
        let rec __visit strategy state node = 
            try
                let (rule,context,newstate) = strategy#next state None node in
                match rule#down context with
                |Tree(l) ->
                        rule#up context (Llist.map (__visit strategy newstate) l)
                |Leaf(_) as n -> rule#up context (LList(n,lazy(Empty)))
            with Strategy.NoMoreRules -> Leaf(node)
        in __visit strategy state node
        
end
