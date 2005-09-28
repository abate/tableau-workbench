class type ['a] ct =
  object ('b)
    method get : 'a
    method is_valid : bool
    method set : 'a -> 'b
  end
module type S =
  sig
    type t
    type node
    type context_type
    type context = context_type ct
    type tree = node Tree.tree
    class virtual rule :
      object
        method virtual check : node -> context
        method virtual down : context -> tree
        method virtual up : tree Llist.llist -> tree
      end
  end
