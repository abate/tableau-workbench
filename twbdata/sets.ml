
module Make (T : sig type t end) = struct

    module Set = Set.Make (
            struct
                type t = T.t
                let compare = compare
            end
    );;

    let copy_Set s = Set.fold (fun v s' -> Set.add v s' ) s Set.empty
                
    class set =
        object
            inherit [T.t] Store.store_open
            val mutable data = Set.empty

            (* XXX: insertion is o(log n) *)
            method add e = {< data = Set.add e data >}

            (* XXX: deletions is o(log n) *)
            method del e = {< data = Set.remove e data >}
            
            (* XXX: copy is o(n) *)
            method copy = {< data = (copy_Set data) >}

            method string_of f =
                let s = Set.fold (
                    fun e s -> Printf.sprintf "%s,%s" s (f e)
                    ) data ""
                in Printf.sprintf "(%s)" s
        end
    ;;

    let string_of s = s#string_of
end
