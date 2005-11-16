
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
    method empty : 'a
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
    
    let copy h =
        Hashtbl.fold (fun k v tbl ->
            Hashtbl.add tbl k (v#copy) ; tbl
        ) h (Hashtbl.create (Hashtbl.length h))

    class map matchpatt =
        object(self)

            val data : (string,T.c) Hashtbl.t = Hashtbl.create 10

            (* this method pattern match the formula and return a string  *)
            method private pattern = matchpatt
            
            method private addel fm e =
                let p = self#pattern e in
                let s = try Hashtbl.find fm p with Not_found -> T.make () in 
                let _ = Hashtbl.replace fm p (s#add e)
                in fm 
 
            method addlist ?(id) l =
                let newdata = 
                    match id with
                    |None | Some ("") ->
                            List.fold_left (fun fm e ->
                                self#addel fm e
                            ) (copy data) l
                    |Some(p) ->
                            let s =
                                try Hashtbl.find data p
                                with Not_found -> T.make ()
                            in
                            let s' = List.fold_left (
                                fun s e -> s#add e
                            ) s l
                            in
                            let data' = copy data in
                            let _ = Hashtbl.replace data' p s' 
                            in data'
                in {< data = newdata >}

            method add e = {< data = self#addel (copy data) e >}

            method get = function
            |"" -> Hashtbl.fold (fun _ v s -> s#addlist (v#elements)) data (T.make ())
            |_ as p -> try (Hashtbl.find data p) with Not_found -> T.make ()

            method private filter f p =
                try (Hashtbl.find data p)#filter f
                with Not_found -> T.make ()
            
            method del e =
                try let p = (self#pattern e) in
                    let s = (Hashtbl.find data p)#del e in
                    let data' = copy data in
                    let _ = Hashtbl.replace data' p s
                    in {< data = data' >}
                with Not_found -> {< >}
            
            method replace p s = 
                let data' = copy data in
                let _ = Hashtbl.replace data' p s in
                {< data = data' >}
                
            method copy = {< data = copy data >}

            method empty = {< data = Hashtbl.create 10 >}

            method to_string = 
                Hashtbl.fold (
                    fun k v s ->
                        if s = "" then Printf.sprintf "%s" (v#to_string)
                        else if (v#to_string) = "" then s
                        else Printf.sprintf "%s\n%s" s (v#to_string)
                ) data ""
                    
        end
        
end
