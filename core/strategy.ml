(** this module return the the rule to apply and a new context *)

exception NoMoreRules

module type S =
    sig
        type rule
        type node
        type state
        type context
        type s = |S |SS of rule |R of rule |E__ 
        class strategy : string ->
          object
            method add :
                string -> ?alt:string -> ?cond:(node -> bool) ->
                    s -> string -> string -> unit
            method next : state -> node option -> node -> rule * context * state
            method start : state
          end
    end
