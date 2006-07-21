
type 'a llist = 'a cell Lazy.t
and 'a cell = LList of 'a * 'a llist | Empty

exception LListEmpty

let empty = lazy(Empty)
let push e l = lazy(LList(e,l))
let pop s = 
    match Lazy.force s with
    | LList (hd, tl) -> (hd,tl)
    | Empty -> raise LListEmpty

let hd s =
    match Lazy.force s with
    | LList (hd, _) -> hd
    | Empty -> raise LListEmpty

let tl s =
    match Lazy.force s with
    | LList (_, tl) -> tl
    | Empty -> raise LListEmpty

let rec append s1 s2 =
    lazy begin
        match Lazy.force s1 with
        | LList (hd, tl) -> LList (hd, append tl s2)
        | Empty -> Lazy.force s2
    end

let rec flatten ss =
    lazy begin
        match Lazy.force ss with
        | Empty -> Empty
        | LList (hd, tl) ->
            match Lazy.force hd with
            | LList (hd2, tl2) -> LList (hd2, flatten (lazy (LList (tl2, tl))))
            | Empty -> Lazy.force (flatten tl)
    end

let rec map f s =
    lazy begin
        match Lazy.force s with
        | LList (hd, tl) -> LList (f hd, map f tl)
        | Empty -> Empty
    end

let rec filter_map f s =
    lazy begin
        match Lazy.force s with
        | LList (hd, tl) ->
                begin match f hd with
                |Some y -> LList (y, filter_map f tl)
                |None -> Lazy.force(filter_map f tl)
                end
        | Empty -> Empty
    end

let rec filter f s =
    lazy begin
        match Lazy.force s with
        | LList (hd, tl) ->
                begin match f hd with
                |true -> LList (hd, filter f tl)
                |false -> Lazy.force(filter f tl)
                end
        | Empty -> Empty
    end

let reverse =
    let rec loop stack = function
        | LList (hd, tl) -> loop (hd :: stack) (Lazy.force tl)
        | Empty -> stack
    in
    fun s ->
        loop [] (Lazy.force s)

let to_list s = List.rev (reverse s)

let rec of_list = function
    | [] -> lazy(Empty)
    | hd :: tl -> lazy (LList (hd, of_list tl))

let is_empty s =
    match Lazy.force s with
    |Empty -> true
    |_ -> false

type 'a excp = Nothing | Just of ('a * 'a llist)

(* monadic operators *)
let mzero = empty
let return x = push x empty
let bind l f = flatten (map f l)
let mplus = append

let guard b = if b then return () else mzero
let determ m = if is_empty m then mzero else return (hd m)

let msplit s =
    match Lazy.force s with
    |Empty -> return (Nothing)
    |LList (hd, tl) -> return (Just(hd,tl))
let ifte t th el =
    bind (msplit t) (function
        |Nothing -> el
        |Just (sg1,sg2) -> mplus (th sg1) (bind sg2 th)
    )
let once m =
    bind (msplit m) (function
        |Nothing -> mzero
        |Just (sg1,_) -> return sg1
    )

