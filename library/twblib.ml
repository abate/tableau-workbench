
(* set history operations *)
let add (l,h) = h#addlist l
let notin (l,h) = not(h#mem (List.hd l))
let isin (l,h) = h#mem (List.hd l)
let not_emptyset l = not(l#is_empty)
let clear h = h#empty

let emptyset = clear

(* list operations *)
let not_emptylist = function [] -> false | h::_ -> true
let is_emptylist = function [] -> true | h::_ -> false

(* debug flag *)
let debug = ref false

(* general functions *)
let min (a,b) = min a b
