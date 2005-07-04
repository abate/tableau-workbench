
(* this is the data structure to store formulae/basictypes
 * and it's optimized to retrive formulae according to a
 *  pattern *)

module Make(T: sig type t end) = struct
    
    module FMap = Map.Make (
        struct
            type t = int
            let compare = compare
        end
    )

    let copy_FMap m = FMap.fold (fun k v m' -> FMap.add k v m' ) m FMap.empty


    class fmap matchpatt =
        object(self)

            val mutable data : T.t list FMap.t = FMap.empty

            (* this method pattern match the formula and return an int *)
            method private pattern = matchpatt
            
            (* O(m * log n) if id = None or Some(0) 
             * O(log n) of od = Some(p) *)
            method addlist ?(id) l =
                let newdata = match id with
                |None | Some(0) ->
                        List.fold_left (
                            fun fm e -> self#addel fm e
                        ) data l
                |Some(p) ->
                        let oldlist = try FMap.find p data with Not_found -> []
                        in FMap.add p (l@oldlist) (FMap.remove p data)
                in {< data = newdata >}

            (* insertion is O(log n) *)
            (* FMap.add p (e::oldlist) (FMap.remove p data) because I want to
             * have only one binding per key *)
            method private addel fm e =
                let p = self#pattern e in
                let oldlist = try FMap.find p fm with Not_found -> []
                in FMap.add p (e::oldlist) (FMap.remove p data)

            (* insertion is O(log n) *)
            method add e = {< data = self#addel data e >}

            (* given a pattern return a sbl *)
            (* find is O(log n) *)
            method get p = 
                print_int p ; print_endline " kkk";
                try FMap.find p data with Not_found -> [] 
            
            (* deletions is o(log n) *)
            method del e = {< data = (FMap.remove (self#pattern e) data) >}
            
            (* copy is o(n) *)
            method copy = {< data = (copy_FMap data) >}

            method string_of f =
                let s = FMap.fold (
                    fun k vl s ->
                        let sl = List.fold_left (
                            fun s e -> Printf.sprintf "%s;%s" s (f e)
                            ) "" vl
                        in Printf.sprintf "%s%d -> [%s]\n" s k sl
                    ) data ""
                in Printf.sprintf "fmap:-------\n%s---------\n" s
        end
    ;;
end
