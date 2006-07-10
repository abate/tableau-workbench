(** lazy list module *)

type 'a llist = LList of 'a * 'a llist Lazy.t | Empty ;;

let empty = Empty

let push hd tl = LList (hd, lazy(tl))

let hd = function
    | Empty -> failwith "hd: empty list"
    | LList (x, _) -> x

let tl = function
    | Empty -> Empty
    | LList (_, xs) -> Lazy.force xs

let rec map f = function
    | Empty -> Empty
    | LList (x, xs) -> LList (f x, lazy( map f (Lazy.force xs)))

let rec filter_map f = function
    | Empty -> Empty
    | LList (x, xs) ->
            begin match f x with
            |Some y -> LList (y, lazy( filter_map f (Lazy.force xs)))
            |None -> filter_map f (Lazy.force xs)
            end

let rec filter f = function
    | Empty -> Empty
    | LList (x, xs) ->
            begin match f x with
            |true -> LList (x, lazy( filter f (Lazy.force xs)))
            |false -> filter f (Lazy.force xs)
            end

let rec append l r = match l with
    | Empty -> r
    | LList (x, xs) ->
        LList (x, lazy (append (Lazy.force xs) r))
    
let rec flatten = function
    | Empty -> Empty
    | LList (x, xs) -> append x (flatten (Lazy.force xs))

let rec interleave = function
    | Empty, ys -> ys
    | LList(x,xs), ys ->  LList(x, lazy(interleave (ys, (Lazy.force xs))))

let rec of_list = function
    |[] -> Empty
    |h::t -> LList(h,lazy (of_list t))

let rec to_list = function
    |Empty -> []
    |LList (x, xs) -> x::(to_list (Lazy.force xs))

(* monadic operators *)
let zero = empty
let return x = push x empty
let bind l f = flatten (map f l)
let plus = append

