
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

let copy_NMap copy m = NMap.fold (
    fun k v m' -> NMap.add k (copy v) m' 
    ) m NMap.empty

module type S =
    sig
      type store
      class node :
          object ('node)
              method get : NMap.key -> store
              method set : NMap.key -> store -> 'node
              method copy : 'node
              method status : status
          end
    end
    
module Make (S: sig type store val copy : store -> store end) =
    struct
        type store = S.store
        let copy = S.copy
        
        class node =
            object
                val status = Open
                val mutable map : store NMap.t = NMap.empty

                method get name =
                    try NMap.find name map
                    with Not_found -> failwith "node#get store not found"
                   
                method set name store = {< map = NMap.add name store map >}
                    
                method copy = {< map = (copy_NMap copy map) >}

                (** return the status of the node *)
                method status = status

            end
    end


