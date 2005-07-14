
type status =
    | Open
    | Closed
    | User of string (** User defined status *)

(*
module NMap = Map.Make (
    struct
        type t = string
        let compare = compare
    end
)

let copy_NMap copy m = NMap.fold (
        fun k v m' -> NMap.add k (copy v) m' 
    ) m NMap.empty
    *)

module type S =
    sig
      type elt
      class node : elt -> 
          object ('node)
              method get : elt
              method set : elt -> 'node
              method copy : 'node
              method status : status
              method set_status : status -> 'node
          end
    end

module type ValType = 
    sig
        type elt
        val copy : elt -> elt
    end

module Make (T: ValType) = struct

        type elt  = T.elt
        let copy = T.copy 
        
        class node elt =
            object
                val status = Open
                val map = elt

                method get = map
                method set s = {< map = s >}
                
                method copy = {< map = copy map >}

                (** return the status of the node *)
                method status = status

                (** set the status *)
                method set_status s = {< status = s >}

            end
    end
