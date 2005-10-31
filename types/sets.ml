
class type ['t] st =
    object('a)
        method add : 't -> 'a
        method addlist : 't list -> 'a
        method del : 't -> 'a
        method mem : 't -> bool
        method elements : 't list
        method is_empty : bool
        method filter : ('t -> bool) -> 'a
        method length : int
        method cardinal : int
        method intersect : 'a -> 'a
        method union: 'a -> 'a
        method equal : 'a -> bool
        method copy : 'a
        method empty : 'a
        method to_string : string
    end

module type ValType =
    sig
        type t
        val copy : t -> t
        val to_string : t -> string
    end

module Make (T : ValType ) : 
    sig
       class set : [T.t] st
    end
= struct

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
        object(self : 'a)
            val data = Set.empty

            (* XXX: insertion is o(log n) *)
            method add e = {< data = Set.add e data >}

            method addlist l = {< data = 
                List.fold_left (fun e s -> Set.add s e ) data l >}

            (* XXX: deletions is o(log n) *)
            method del e = {< data = Set.remove e data >}
            
            (* XXX: copy is o(n) *)
            method copy = {< data = (copy data) >}

            method empty = {< data = Set.empty >}

            method mem e = Set.mem e data 

            method filter f = {< data = Set.filter f data >}

            method elements = Set.elements data

            method is_empty = Set.is_empty data

            method cardinal = Set.cardinal data
            method length = self#cardinal

            (* here I create a set and the use inter.
             * XXX: I'm double minded ...
             * the other ways is to expose a method to access the
             * interal represenation of the set, but this will
             * break the data incapsulation ... Friends functions ?? *)
            method intersect (set : 'a) =
                {< data =
                    Set.inter data
                    (List.fold_left
                        (fun e s -> Set.add s e)
                        Set.empty set#elements
                    )
                >}

            method union (set : 'a) =
                {< data =
                    Set.union data
                    (List.fold_left
                        (fun e s -> Set.add s e)
                        Set.empty set#elements
                    )
                >}
                    
            method equal (set : 'a) =
                Set.equal
                data 
                (List.fold_left
                    (fun e s -> Set.add s e)
                    Set.empty set#elements
                )
            
            method to_string =
                let s = Set.fold (
                    fun e s ->
                        if s = "" then Printf.sprintf "%s" (T.to_string e)
                        else Printf.sprintf "%s,%s" s (T.to_string e)
                    ) data ""
                in if s = "" then "" else Printf.sprintf "(%s)" s
        end
    ;;
end



