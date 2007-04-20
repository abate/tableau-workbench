
module Make(N:Node.S)(R: Rule.S with type node = N.node)
= struct

    open Tree

    type node = R.node
    type rule = R.rule
    type context = R.context

    type res = ((rule * context) * continuation) Llist.llist
    and continuation = Cont of (node -> res) | End
    and m = ((rule * context) * continuation) Llist.llist

    type tactic =
        |Skip
        |Fail
        |Rule of R.rule
        |Cut of tactic
        |Seq of tactic * tactic
        |Alt of tactic * tactic
        |Mu of (string * tactic)
        |Var of string

    module Cache = Cache.Make(N)   
    let table = ref (new Cache.cache true)

    let rec visit_aux env acc = function
        |Skip -> fun n ->
                begin match acc with
                |[] -> Llist.return (Leaf(n)) (* no more rules applicable *)
                |h::t -> visit_aux env t h n 
                end
        |Fail -> fun _ -> Llist.mzero
        |Rule(rule) -> fun n ->
                Llist.bind (Llist.return (lazy(rule#check n))) (fun cxt ->
                    let context = Lazy.force(cxt) in
                    let up = rule#up context in
                    match (context#is_valid) with 
                    |true -> (* the rule is applicable *)
                            begin match rule#down context,acc with
                            |Leaf(n),_  -> (* and is a terminal rule *)
                                    Llist.return (up (Llist.return (Leaf(n))))
                            |Tree(l),[] -> (* but no more rules applicable *)
                                    Llist.return (up (Llist.map (fun n -> Leaf(n)) l))
                            |Tree(l),h::t -> (* and keep going *)
                                    let f = memo_visit env ~cache:rule#use_cache t h 
                                    in Llist.map up (Llist.xmerge (Llist.map f l))
                            end
                    |false -> Llist.mzero
                )
        |Seq(t1,t2) -> visit_aux env (t2::acc) t1 
        |Cut(t1)    -> fun n -> Llist.determ (visit_aux env acc t1 n)
        |Alt(t1,t2) -> fun n ->
                Llist.mplus (visit_aux env acc t1 n) (visit_aux env acc t2 n)
        |Mu(x,t) -> visit_aux ((x,t)::env) acc t
        |Var(x)  ->
                try visit_aux env acc (List.assoc x env)
                with Not_found -> failwith "Variable not defined"

    and memo_visit env ?(cache=false) acc str node =
        if cache then
            try !table#find node
            with Not_found ->
                let res = visit_aux env acc str node in
                !table#add node res;
                res
        else
            visit_aux env acc str node
    ;;

    let visit cache t n = visit_aux [] [] t n

end
