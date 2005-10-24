
module type ValType =
    sig
        type t
        val copy : t -> t
        val to_string : t -> string
    end

module Make (T : ValType) :
    sig
       class listobj : [T.t] Sets.st
    end
= struct

    let copy l = List.fold_left (fun l e -> (T.copy e)::l ) [] l;;

    class listobj =
        object(self : 'a)
            val data = []

            method add e = {< data = e::data >}

            method addlist l = {< data = data@l >}
            
            (* XXX: deletions is o(n) *)
            method del e = {< data = List.filter (fun el -> not(e = el)) data >}

            method mem e = List.mem e data

            (* XXX: copy is o(n) *)
            method copy = {< data = (copy data) >}

            method empty = {< data = [] >}
            
            method filter f = {< data = List.filter f data >}

            method elements = data

            method is_empty = match data with [] -> true | _ -> false

            method length = List.length data
            method cardinal = self#length

            (* this method is dodgy and expensive ... *)
            method intersect (l : 'a) =
                {< data = List.filter (fun e -> List.mem e l#elements) data >}

            (* the union here doesn't remove duplicates *)
            method union (l : 'a) = {< data = (l#elements)@data >}
                
            method equal (l : 'a) =
                List.for_all2 (fun a b -> a = b) data l#elements
            
            method to_string = 
                let l = List.fold_left (
                    fun s e ->
                        if s = "" then Printf.sprintf "%s" (T.to_string e)
                        else Printf.sprintf "%s;%s" s (T.to_string e)
                    ) "" data
                in if l = "" then "" else Printf.sprintf "[%s]" l 
            
        end
end

