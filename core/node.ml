
module type S =
    sig
      type elt
      class node : elt -> 
          object ('node)
              method get : elt
              method set : elt -> 'node
              method copy : 'node
              method status : Data.status
              method set_status : Data.status -> 'node
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
                val status = Data.Open
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
