
class type ['t] st =
    object('a)
        method add : 't -> 'a
        method addlist : 't list -> 'a
        method del : 't -> 'a
        method mem : 't -> bool
        method elements : 't list
        method filter : ('t -> bool) -> 'a
        method copy : 'a
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
        object
            val data = Set.empty

            (* XXX: insertion is o(log n) *)
            method add e = {< data = Set.add e data >}

            method addlist l = {< data = 
                List.fold_left (fun e s -> Set.add s e ) data l >}

            (* XXX: deletions is o(log n) *)
            method del e = {< data = Set.remove e data >}
            
            (* XXX: copy is o(n) *)
            method copy = {< data = (copy data) >}

            method mem e = Set.mem e data 

            method filter f = {< data = Set.filter f data >}

            method elements = Set.elements data
(*
            method pmatch f (sl : string list) =
                let rec empty acc = function
                |1 -> ({< data = Set.empty >})::acc
                |_ as n -> empty (({< data = Set.empty >})::acc) (n-1)
                in
                let l = List.map2 (
                    fun s el -> s#add (f el)
                ) (empty [] (List.length sl)) (Set.elements data) 
                in (List.combine sl l)
*)
            method to_string =
                let s = Set.fold (
                    fun e s -> Printf.sprintf "%s,%s" s (T.to_string e)
                    ) data ""
                in Printf.sprintf "(%s)" s
        end
    ;;
end



