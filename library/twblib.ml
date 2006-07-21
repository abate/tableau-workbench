
(* set history operations *)
let add (l,h) = h#addlist l
let notin (l,h) = not(h#mem (List.hd l))
let isin (l,h) = h#mem (List.hd l)
let not_emptyset l = not(l#is_empty)
let emptyset h = h#empty

(* list operations *)
let not_emptylist = function [] -> false | _ -> true

(* debug flag *)
let debug = ref false

(* general functions *)
let min (a,b) = min a b
