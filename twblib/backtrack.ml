(** this module apply the rule using the rule_context passed by the strategy. 
    this module is purerly functional *)

module type S =
    sig
        type tree
        type nodeaction
        
        val synth : tree Llist.llist -> tree
    end

module Make(R:Rule.RuleType) : S =
    struct
        type tree = Rule.tree
        type nodeaction = Rule.nodeaction
        
        let synth nodelist nodeaction =
            Tree ( LList (n, lazy(LList(n,lazy(Empty)))) )
    end

