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

(* this is not tail rec  ! *)
let rec append l r = match l with
    | Empty -> r
    | LList (x, xs) ->
        LList (x, lazy (append (Lazy.force xs) r))
    
let rec flatten = function
    | Empty -> Empty
    | LList (x, xs) -> append x (flatten (Lazy.force xs))

let rec of_list = function
    |[] -> Empty
    |h::t -> LList(h,lazy (of_list t))

let rec to_list = function
    |Empty -> []
    |LList (x, xs) -> x::(to_list (Lazy.force xs))
