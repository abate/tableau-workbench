
open Datatype

let print (node : Node.node) rule =
    print_endline rule;
    print_endline (node#to_string);
    print_newline ()
;;

exception LeftOfTop
exception RightOfTop
exception Bottom
exception UpOfTop
exception TooRight
exception TooLeft

type 'a sort = {
    node    : 'a;     (* node content *)
    name    :  string (* rule name *)
}

type 'a tree = Tree of 'a sort * 'a tree list
type 'a path =
    |Top
    |Node of 'a tree list * ('a path * 'a sort) * 'a tree list
type 'a zipper = 'a tree * 'a path

class ['a] ptree root =
    object(self)

    val mutable z : 'a zipper = (Tree(root,[]),Top)
       
    method private unwind =
        try
            while true do
                self#move_up
            done
        with UpOfTop -> ()
 
    method tree =
        self#unwind;
        match z with (t,_) -> t

    method move_left =
        match z with
        |(_,Top) -> raise LeftOfTop
        |(_,Node([],_,_)) -> raise TooLeft
        |(t,Node(l::left,upv,right)) -> z <- (l,Node(left,upv,t::right))

    method move_right =
        match z with
        |(_,Top) -> raise RightOfTop
        |(_,Node(_,_,[])) -> raise TooRight
        |(t,Node(left,upv,r::right)) -> z <- (r,Node(t::left,upv,right))

    method move_up =
        match z with
        |(_,Top) -> raise UpOfTop
        |(t,Node(left,(up,v),right)) -> z <- (Tree(v, left @ (t::right)),up)

    method move_down =
        match z with
        |(Tree(v,h::tail),p) -> z <- (h, Node([],(p,v),tail))
        |(Tree(v,[]),_) -> raise Bottom

    method newchild node = 
        match z with
        |(Tree(v,tail),p) ->
                z <- (Tree(node,[]), Node([],(p,v),tail))

    method newsibling node =
        match z with
        |(_,Top) -> raise RightOfTop
        |(t,Node(left,upv,right)) ->
                z <- (Tree(node,[]),Node(t::left,upv,right))
            
end
;;

