
module type S =
    sig
      type elt
      class node : elt -> 
          object ('node)
              method get : elt
              method set : elt -> 'node
              method copy : 'node
              method to_string : string
          end
    end

module type ValType = 
    sig
        type elt
        val copy : elt -> elt
        val to_string: elt -> string
    end

module Make (T: ValType) = struct

        type elt  = T.elt
        let copy = T.copy 
        let elt_to_string = T.to_string
        
        class node elt =
            object
                val map = elt

                method get = map
                method set s = {< map = s >}
                method copy = {< map = copy map >}
                method to_string =
                    Printf.sprintf "%s" (elt_to_string map)

            end
    end
