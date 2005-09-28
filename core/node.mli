module type S =
  sig
    type elt
    class node :
      elt ->
      object ('a)
        method copy : 'a
        method get : elt
        method set : elt -> 'a
        method set_status : Data.status -> 'a
        method status : Data.status
        method to_string : string
      end
  end
module type ValType =
  sig type elt val copy : elt -> elt val to_string : elt -> string end
module Make :
  functor (T : ValType) ->
    sig
      type elt = T.elt
      val copy : T.elt -> T.elt
      val elt_to_string : T.elt -> string
      class node :
        T.elt ->
        object ('a)
          val map : T.elt
          val status : Data.status
          method copy : 'a
          method get : T.elt
          method set : T.elt -> 'a
          method set_status : Data.status -> 'a
          method status : Data.status
          method to_string : string
        end
    end
