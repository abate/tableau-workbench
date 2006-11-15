
module type S =
sig
    type node 
    type rule
    type context 

    type res = ((rule * context) * continuation list)
    and continuation = Cont of (node -> res Llist.llist)
    type m = res Llist.llist

    type tactic =
        |Skip
        |Fail
        |Rule of rule
        |Cut of tactic
        |Seq of tactic * tactic
        |Alt of tactic * tactic
        |Mu of (string * tactic)
        |Var of string

    val strategy : (string * tactic) list -> tactic -> node -> m

end

module Make(N:Node.S)(R: Rule.S with type node = N.node)
= struct

    type node = R.node
    type rule = R.rule
    type context = R.context
    
    type res = ((rule * context) * continuation list)
    and continuation = Cont of (node -> res Llist.llist)
    type m = res Llist.llist

    type tactic =
        |Skip
        |Fail
        |Rule of R.rule
        |Cut of tactic
        |Seq of tactic * tactic
        |Alt of tactic * tactic
        |Mu of (string * tactic)
        |Var of string

    let rec strategy env = function
        |Skip -> fun n ->
                Llist.bind (Llist.return (lazy(R.skip#check n))) (fun cxt ->
                    Llist.return ((R.skip,Lazy.force(cxt)), [])
                )
        |Fail -> fun _ -> Llist.mzero
        |Rule(rule) -> fun n ->
                Llist.bind (Llist.return (lazy(rule#check n))) (fun cxt ->
                    Llist.bind (Llist.guard ((Lazy.force(cxt))#is_valid)) (fun _ ->
                        Llist.return ((rule,Lazy.force(cxt)), [])
                    )
                )
        |Cut(t)     -> fun n -> Llist.determ (strategy env t n)
        |Alt(t1,t2) -> fun n -> Llist.mplus (strategy env t1 n) (strategy env t2 n)
        |Seq(t1,t2) -> fun n ->
                Llist.bind (strategy env t1 n) (fun (r,stack) ->
                    Llist.return (r, stack @ [(Cont(strategy env t2))])
                    )
        |Mu(x,t) -> strategy ((x,t)::env) t
        |Var(x)  ->
                try strategy env (List.assoc x env)
                with Not_found -> failwith "Variable not defined"

end
