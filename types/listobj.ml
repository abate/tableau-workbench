
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

    (* we need to reverse the list to maintain the order the the elements *)
    let copy l = List.fold_left (fun l e -> (T.copy e)::l ) [] (List.rev l);;

    (* This is a stack *)
    class listobj =
        object(self : 'a)
            val data = []
            val mutable modified = true
            val mutable to_string_cache = ""

            method add e = {<
                modified = true;
                to_string_cache = "";
                data = e::data
            >}

            method add_filter f e =
                let data' = List.filter (fun el -> f e el) data in
                {< 
                    modified = true;
                    to_string_cache = "";
                    data = e::data'
                >}

            method addlist l = {<
                modified = true;
                to_string_cache = "";
                data = (List.fold_left (fun d e -> e::d) data l )
            >}
            
            (* XXX: deletions is o(n) *)
            method del e = {<
                modified = true;
                to_string_cache = "";
                data = List.filter (fun el -> not(e = el)) data
            >}

            method mem e = List.mem e data

            (* XXX: copy is o(n) *)
            method copy = {< data = (copy data) >}

            method empty = {<
                modified = true;
                to_string_cache = "";
                data = []
            >}
            
            method filter f = {<
                modified = true;
                to_string_cache = "";
                data = List.filter f data
            >}

            (* we return elements as a stack *)
            method elements = List.rev data

            method head = List.hd data

            method is_empty = match data with [] -> true | _ -> false

            method length = List.length data
            method cardinal = self#length

            (* this method is dodgy and expensive ... *)
            method intersect (l : 'a) = {<
                modified = true;
                to_string_cache = "";
                data = List.filter (fun e -> List.mem e l#elements) data
            >}

            (* the union here doesn't remove duplicates *)
            method union (l : 'a) = {< 
                modified = true;
                to_string_cache = "";
                data = (l#elements)@data
            >}
                
            method is_equal (l : 'a) =
                List.for_all2 (fun a b -> a = b) data l#elements
            
            method to_string =
                if modified then begin 
                    let i = ref (-1) in 
                    let l = List.fold_left (
                        fun s e ->
                            incr i;
                            if s = "" then Printf.sprintf "\n%d:%s" !i (T.to_string e)
                            else Printf.sprintf "%s\n%d:%s" s !i (T.to_string e)
                        ) "" (self#elements) 
                    in
                    let l = if l = "" then "" else Printf.sprintf "[%s]" l in
                    modified <- false;
                    to_string_cache <- l;
                    to_string_cache
                end else to_string_cache 
            
        end
end

