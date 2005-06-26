class virtual ['t] super =
    object(self: 's)
        method virtual add : 't -> unit
        method virtual copy : 's
    end

class one = 
    object
    inherit [int] super
        method add t = ()
        method copy = {<>}
    end

class two =
    object
    inherit [int] super
        val data : int list = []
        method add t = ()
        method copy = {<>}
        method get = List.hd data
    end

type mt = [
|`One of one
|`Two of two
]

let hash = 
    let h = Hashtbl.create 10 in
    Hashtbl.add h "one" (`One(new one));
    Hashtbl.add h "two" (`Two(new two));
    h
;;

let get s h =
    try 
        match Hashtbl.find h s with
        |`One(o) -> 0
        |`Two(o) -> o#get
    with Not_found -> failwith "aa"
;;

let o = get "one" hash;;
