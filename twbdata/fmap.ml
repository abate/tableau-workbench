
(* this is the data structure to store formulae/basictypes
 * and it's optimized to retrive formulae according to a
 *  pattern *)

module type ValType =
    sig
        type t
        type c = t Sets.st
        val make : unit -> c
    end

module Make(T: ValType) = struct
    
    module FMap = Map.Make (
        struct
            type t = int
            let compare = compare
        end
    )

    (* XXX: don't know... maybe this can be more flexible *)
    let copy m = FMap.fold (
        fun k v m' -> FMap.add k (v#copy) m'
    ) m FMap.empty

    class fmap matchpatt =
        object(self)

            val data : T.c FMap.t = FMap.empty

            (* this method pattern match the formula and return an int *)
            method private pattern = matchpatt
            
            method addlist ?(id) l =
                let newdata = 
                    match id with
                    |None | Some(0) ->
                            List.fold_left (
                                fun fm e -> self#addel fm e
                            ) data l
                    |Some(p) ->
                            let s =
                                try FMap.find p data
                                with Not_found -> T.make ()
                            in
                            let s' = List.fold_left (
                                fun s e -> s#add e
                            ) s l
                            in FMap.add p s' (FMap.remove p data)
                in {< data = newdata >}

            method private addel fm e =
                let p = self#pattern e in
                let s = try FMap.find p data with Not_found -> T.make ()
                in FMap.add p (s#add e) (FMap.remove p data)

            (* insertion is O(log n) *)
            method add e = {< data = self#addel data e >}

            (* given a pattern return a sbl *)
            (* find is O(log n) *)
            method get p =
                try (FMap.find p data)#elements
                with Not_found -> []
            
            (* deletions is o(log n) *)
            method del e = {< data = (FMap.remove (self#pattern e) data) >}
            
            (* copy is o(n) *)
            method copy = {< data = (copy data) >}

            method to_string = ""
        end
        
end
