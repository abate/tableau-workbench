
(* this is the data structure to store formulae/basictypes
 * and it's optimized to retrive formulae according to a
 * pattern *)

class type ['t,'c] mt =
  object ('a)
    method add : 't -> 'a
    method addlist : ?id:string -> 't list -> 'a
    method copy : 'a
    method del : 't -> 'a
    method replace : string -> 'c -> 'a
    method get : string -> 'c
    method to_string : string
  end


module type ValType =
    sig
        type t
        type c = t Sets.st
        val make : unit -> c
    end

module Make(T: ValType) :
    sig
        class map : (T.t -> string) -> [T.t, T.c] mt
    end
= struct
    
    module FMap = Map.Make (
        struct
            type t = string
            let compare = compare
        end
    )

    let copy m = FMap.fold (
        fun k v m' -> FMap.add k (v#copy) m'
    ) m FMap.empty

    class map matchpatt =
        object(self)

            val data : T.c FMap.t = FMap.empty

            (* this method pattern match the formula and return a string  *)
            method private pattern = matchpatt
            
            method addlist ?(id) l =
                let newdata = 
                    match id with
                    |None | Some ("") ->
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
                let s = try FMap.find p fm with Not_found -> T.make ()
                in FMap.add p (s#add e) (FMap.remove p fm)

            (* insertion is O(log n) *)
            method add e = {< data = self#addel data e >}

            (* given a pattern return an element list *)
            (* find is O(log n) *)
            method get = function
            |"" -> FMap.fold (fun _ v s -> s#addlist (v#elements)) data (T.make ())
            |_ as p ->
                    try (FMap.find p data)
                    with Not_found -> T.make ()

            method private filter f p =
                try (FMap.find p data)#filter f
                with Not_found -> T.make ()
            
            (* deletions is o(log n) *)
            method del e =
                try let p = (self#pattern e) in
                    let s = (FMap.find p data)#del e in
                    {< data = FMap.add p s (FMap.remove p data) >}
                with Not_found -> {< >}
            
            method replace p s = 
                {< data = FMap.add p s (FMap.remove p data) >}
                
            (* copy is o(n) *)
            method copy = {< data = (copy data) >}

            method to_string = 
                FMap.fold (
                    fun k v s -> Printf.sprintf "%s%s" s (v#to_string)
                ) data ""
                    
        end
        
end
