
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
        object
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
            
            method to_string = 
                let l = List.fold_left (
                    fun s e -> Printf.sprintf "%s;%s" s (T.to_string e)
                    ) "" data
                in Printf.sprintf "[%s]" l 
            
        end
end

