
exception LeftOfTop
exception RightOfTop
exception Bottom
exception UpOfTop
exception TooRight
exception TooLeft

type 'a sort = Or | And | Star | Rule of 'a 

type 'a tree = Tree of 'a sort * 'a tree list

type 'a path =
    |Top
    |Node of 'a tree list * ('a path * 'a sort) * 'a tree list

(* zipper == location *)
type 'a zipper = 'a tree * 'a path

(*move_{left,right,up,down} : 'a zipper -> 'a zipper *)

let move_left (t,p) =
    match p with
    |Top -> raise LeftOfTop
    |Node([],_,_) -> raise TooLeft
    |Node(l::left,upv,right) -> (l,Node(left,upv,t::right))

let move_right (t,p) =
    match p with
    |Top -> raise RightOfTop
    |Node(_,_,[]) -> raise TooRight
    |Node(left,upv,r::right) -> (r,Node(t::left,upv,right))

let move_up (t,p) =
    match p with
    |Top -> raise UpOfTop
    |Node(left,(up,v),right) -> (Tree(v, left @ (t::right)),up)

let move_down (t,p) =
    match t with
    |Tree(v,h::tail) -> (h, Node([],(p,v),tail))
    |Tree(v,[]) -> raise Bottom

