
open Basictype
open Store

let copy_list l = List.fold_left (fun l e -> e::l ) [] l;;

class ['mt] listobj =
    object
        inherit ['mt] store_open
        val mutable data = []

        method add e = {< data = e::data >}
        
        (* XXX: deletions is o(n) *)
        method del e = {< data = List.filter (fun el -> not(e = el)) data >}

        (* XXX: copy is o(n) *)
        method copy = {< data = (copy_list data) >}
        
        method head = List.hd data
        method tail = {< data = List.tl data >}

        method string_of f = 
            let l = List.fold_left (
                fun s e -> Printf.sprintf "%s;%s" s (f e)
                ) "" data
            in Printf.sprintf "[%s]" l
        
    end
;;

type mixtype_sutype = [
    |`Blurp of (int * int * int list)
    |mixtype
]
;;

class listobj_subtype =
    object
        inherit [mixtype_sutype] listobj
    end
;;

