
module type S =
sig
    type node 
    type rule
    type context 

    module MState :
      sig
        type res = (rule * context)
        type continuation = Cont of (node -> res m Llist.llist)
        and csstack = continuation Llist.llist
        and state = csstack
        and 'a m = state -> 'a * state
      end

    type tactic =
        |Skip
        |Fail
        |Rule of rule
        |Cut of tactic
        |Seq of tactic * tactic
        |Alt of tactic * tactic
        |Repeat of tactic

    type m = MState.res MState.m Llist.llist
    val strategy : tactic -> node -> m

end

module Make(N:Node.S)(R: Rule.S with type node = N.node)
= struct

    type node = R.node
    type rule = R.rule
    type context = R.context
    
    module MState = struct
        type res = (rule * context)
        type continuation = Cont of (node -> res m Llist.llist)
        and csstack = continuation Llist.llist
        and state = csstack
        and 'a m = state -> ('a * state)

        let return a = fun s -> (a,s)
        let bind m f = fun s -> let (a,s') = m s in f a s'

        let run f = fun s -> f s
        let show m = let (a,_) = m Llist.empty in a
        let fetch = fun s -> return s s
        let store = fun s -> fun _ -> return () s
        let update f = fun s -> return () (f s)
    end
    type m = MState.res MState.m Llist.llist

    type tactic =
        |Skip
        |Fail
        |Rule of R.rule
        |Cut of tactic
        |Seq of tactic * tactic
        |Alt of tactic * tactic
        |Repeat of tactic

    let rec strategy = function
        |Skip -> fun n -> Llist.return (MState.return (R.skip,R.skip#check n))
        |Fail -> fun _ -> Llist.mzero
        |Rule(rule) -> fun n ->
                (* the check should be delayed as much as possible *)
                Llist.bind (Llist.return (lazy(rule#check n))) (fun cxt ->
                    Llist.bind (Llist.guard ((Lazy.force(cxt))#is_valid)) (fun _ ->
                        Llist.return (MState.return (rule,Lazy.force(cxt)))
                    )
                )
        |Cut(t1) -> fun n -> Llist.determ (strategy t1 n)
        |Alt(t1,t2) -> fun n ->
                Llist.determ(Llist.mplus (strategy t1 n) (strategy t2 n))
(*        |CAlt(b,t1,t2) -> Llist.mplus (strategy t1 n) (strategy t2 n) *)
        |Seq(t1,t2) -> fun n ->
                Llist.bind (strategy t1 n) (fun ms ->
                    Llist.return (
                        MState.bind ms (fun a ->
                            let c = Llist.return (MState.Cont (strategy t2)) in
                            fun s -> (a,Llist.append s c)
                            )
                        )
                    )
        |Repeat(t1) -> fun n ->
            let rec loop t1 n =
                Llist.bind (strategy t1 n) (fun ms ->
                    Llist.return (
                        MState.bind ms (fun a ->
                            let c = Llist.return (MState.Cont(loop t1)) in
                            fun s -> (a,Llist.append s c)
                            )
                        )
                    )
            in loop t1 n

end
