
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
                (* by default a node is open *)
                val status = Data.Open
                val map = elt

                method get = map
                method set s = {< map = s >}
                
                method copy = {< map = copy map >}

                (** return the status of the node *)
                method status = status

                (** set the status *)
                method set_status s = {< status = s >}

                method to_string =
                    let status_to_string = function
                    |Data.Open -> "Open"
                    |Data.Closed -> "Closed"
                    |Data.User(s) -> "User( "^s^" )"
                    in
                    Printf.sprintf "Node(%s)\n%s"
                    (status_to_string status)
                    (elt_to_string map)

            end
    end
