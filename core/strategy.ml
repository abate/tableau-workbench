(* this module return the the rule to apply and a new context *)


module type S =
sig
    type node
    type rule
    type context
    
    exception NoMoreRules of node
    type ans = (rule * context * cnt list) list
    and smt = node -> ans
    and cnt = Cont of (node -> ans) | Nil
    type tactic =
        |Skip
        |Rule of rule
        |Seq of tactic * tactic
        |Alt of tactic * tactic
        |Repeat of tactic
    val strategy : tactic -> node -> ans
end

module Make(N:Node.S)(R: Rule.S with type node = N.node)
= struct

    type node = R.node
    type rule = R.rule
    type context = R.context
    
    exception NoMoreRules of node
    type ans = (R.rule * R.context * cnt list) list 
    and smt = R.node -> (R.rule * R.context * cnt list) list
    and cnt = Cont of (R.node -> (R.rule * R.context * cnt list) list) | Nil

    type tactic =
        |Skip
        |Rule of R.rule
        |Seq of tactic * tactic
        |Alt of tactic * tactic
        |Repeat of tactic

    (* LIFO stack: element appended at the end of the list *)
    let push el stack = stack @ [el]
    let return x = [x]
    let bind m f = List.flatten (List.map f m)
    let mzero = []
    let append = List.append

    let rec next tactic ?(cond=true) node =
        match tactic with
        |Skip -> raise (NoMoreRules node) 
        |Rule(rule) ->
                let cxt = rule#check node in
                if cxt#is_valid then return (rule,cxt,[])
                else raise (NoMoreRules node)
        |Seq(t1, t2) ->
                begin try
                    (bind (next t1 ~cond:cond node) (fun (rule,cxt,cnt) ->
                        return (rule,cxt,push (Cont(next t2 ~cond:true)) cnt))
                    )
                with (NoMoreRules newnode) -> next t2 ~cond:false newnode end
        |Alt(t1,t2) ->
                (* this is broken ... I think *)
                append 
                (try next t1 ~cond:cond node with (NoMoreRules node) -> mzero) 
                (try next t2 ~cond:cond node with (NoMoreRules node) -> mzero)
        |Repeat(t1) ->
            let rec loop t1 cond = fun node ->
                  (match cond with
                      |true ->
                              begin try
                                  (bind (next t1 ~cond:cond node) (
                                      fun (rule,cxt,cnt) ->
                                          return
                                          (rule,cxt,push (Cont(loop t1 true)) cnt))
                                  )
                              with (NoMoreRules newnode) ->
                                  loop t1 false newnode
                              end
                      |false -> raise (NoMoreRules node)
                  )
            in loop t1 cond node
    ;;

    let strategy tactic node = next tactic node
end
