
module type ValType =
    sig
        type t
        val copy : t -> t
        val to_string : t -> string
    end

module Make (T : ValType ) = struct

    module Set = Set.Make (
            struct
                type t = T.t
                let compare = compare
            end
    );;

    let copy s = Set.fold (
        fun v s' -> Set.add (T.copy v) s'
    ) s Set.empty
                
    class set =
        object
            val data = Set.empty

            (* XXX: insertion is o(log n) *)
            method add e = {< data = Set.add e data >}

            (* XXX: deletions is o(log n) *)
            method del e = {< data = Set.remove e data >}
            
            (* XXX: copy is o(n) *)
            method copy = {< data = (copy data) >}

            method elements = Set.elements data

            method to_string =
                let s = Set.fold (
                    fun e s -> Printf.sprintf "%s,%s" s (T.to_string e)
                    ) data ""
                in Printf.sprintf "(%s)" s
        end
    ;;
end


class type ['t] st =
    object('store)
        method add : 't -> 'store
        method del : 't -> 'store
        method elements : 't list
        method copy : 'store
        method to_string : string
    end

