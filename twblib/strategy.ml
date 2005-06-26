(** this module return the the rule to apply and a new context *)

open Zipper

module type S =
    sig
        type rule
        type node
        type rule_context
        val init : rule tree -> unit
        val next : node -> rule * rule_context
        val last : unit -> unit
    end
 
module Make (R:Rule.S) : S =
    struct

    type rule = R.rule
    type rule_context = R.rule_context
    type node = R.node
    
    (* the content strategy contains a stack of pointers to the
     * zipper *)
    class ['a] strategy_context = object
        val mutable context : 'a list = []
        method del =
            try context <- List.tl context
            with Failure "tl" -> failwith "del in strategy"
        method peek =
            try List.hd context 
            with Failure "hd" -> failwith "peek in strategy"
        method push h = context <- h::context
    end
    
    let context = ref (new strategy_context)
    let init s = (!context)#push (s,Top)
    
    (* visit navigate the strategy tree looking for the next rule to
     * apply. Visit calls rule#check node and return a rule, a rule context 
     * and the strategy_context *)
    let visit ((t,p) as pointer) node =
        match t with
        |Tree(Rule(rule),[]) ->
                (* let _ = (!context)#push pointer in*)
                let rule_context = rule#check node in
                (rule, rule_context)
        |_ -> failwith "to be implemented"

    (* next calls rule#check, that returns a enumeration of the node 
     * If the enumeration is not empty, then next return the rule and
     * the enumeration (the rule_context) to the visit. The visit will
     * then use the context to build a new node. If the enumeration is 
     * empty then we'll select an other rule. The rule context is 
     * implicitely stored on the stack in the lazy list inside the 
     * visit structure.
     * *)
    let next node =
        let pointer = (!context)#peek in
        let (r,pen) = visit pointer node in
        ((r, pen) :> (R.rule * R.rule_context))

    let last () = (!context)#del
        
    end

