(** this module apply the rule using the rule_context passed by the strategy. 
    this module is purerly functional *)


module type S =
    sig
        type rule_context
        type tree
        val build : rule_context -> tree
    end

module Make(R:Rule.S) : S =
    struct
        type rule_context = R.rule_context
        type tree = R.tree
        
        let build substlist nodepattern =
            Tree ( LList (n, lazy(LList(n,lazy(Empty)))) )
    end

