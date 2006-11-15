
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
        |Repeat of tactic

    val strategy : tactic -> node -> m

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
        |Repeat of tactic

    let rec strategy = function
        |Skip -> fun n ->
                Llist.bind (Llist.return (lazy(R.skip#check n))) (fun cxt ->
                    Llist.return ((R.skip,Lazy.force(cxt)), [])
                )
        |Fail -> fun _ -> Llist.mzero
        |Rule(rule) -> fun n ->
                (* the check should be delayed as much as possible *)
                Llist.bind (Llist.return (lazy(rule#check n))) (fun cxt ->
                    Llist.bind (Llist.guard ((Lazy.force(cxt))#is_valid)) (fun _ ->
                        Llist.return ((rule,Lazy.force(cxt)), [])
                    )
                )
        |Cut(t)     -> fun n -> Llist.determ (strategy t n)
        |Alt(t1,t2) -> fun n -> Llist.mplus (strategy t1 n) (strategy t2 n)
(*        |CAlt(b,t1,t2) -> Llist.mplus (strategy t1 n) (strategy t2 n) *)
        |Seq(t1,t2) -> fun n ->
                Llist.bind (strategy t1 n) (fun (r,stack) ->
                    Llist.return (r, stack @ [(Cont(strategy t2))])
                    )
        |Repeat(t) -> strategy (Cut(Alt(Seq(t,Repeat(t)),Skip)))

end
