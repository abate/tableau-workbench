
type status =
    | Open
    | Closed
    | User of string (** User defined status *)

module NMap = Map.Make (
    struct
        type t = string
        let compare = compare
    end
)

module type S =
    sig
      type store 
      class node :
          object ('a)
              method get : NMap.key -> store
              method set : NMap.key -> store -> 'a
              method copy : 'a  
              method status : status
          end
    end

module NodeCounter =
    struct
    type id_t = { mutable id : int }
    let value = { id = 0 }
    let next () = value.id <- (value.id + 1) ; value.id
    end
;;

module Make (S: sig type store end) =
    struct
        type store = S.store
        class node =
            object
                val id = NodeCounter.next ()
                val status = Open
                val mutable map : store NMap.t = NMap.empty 

                method get name = 
                    try NMap.find name map
                    with Not_found -> failwith "node#get store not found"
                   
                method set name store =
                    {< map = NMap.add name store map >}
                    
                (** copy the acutal node *)
                (* FIXME: this one doesn't copy anything at all !!! *)
                method copy = {< map = map >}

                (** return the status of the node *)
                method status = status

            end
    end


