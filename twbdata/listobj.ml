
open Basictype
open Store

class ['mt] listobj =
    object
        inherit ['mt] store_open
        val mutable data = []

        method data = data
        method assign s = {< data = s#data >}
        method add e = {< data = e::data >}
        (* XXX *)
        method del e = {< >}
        method export = El(data)
        method copy = {< data = data >}
        
        method head = List.hd data
        method tail = {< data = List.tl data >}
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

