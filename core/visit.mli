module Make :
  functor (R : Rule.S) ->
    functor
      (S : sig
             type rule = R.rule
             type node = R.node
             type state
             type context = R.context
             type s = S | SS of rule | R of rule | E
             class strategy :
               string ->
               object
                 val automata : (string, s * string * string) Hashtbl.t
                 val start : state
                 method add : string -> s -> string -> string -> unit
                 method next : state -> node -> rule * context * state
                 method start : state
               end
           end) ->
      sig
        val visit :
          < next : 'a ->
                   'b ->
                   < down : 'c -> 'b Tree.tree;
                     up : 'b Tree.tree Llist.llist -> 'b Tree.tree; .. > *
                   'c * 'a;
            .. > ->
          'a -> 'b -> 'b Tree.tree
      end
