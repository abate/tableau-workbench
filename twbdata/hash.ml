

open Basictype
open Sets
open Usertypes

(* l can be a tuple with the set type *)
let init_hash l =
    let h = Hashtbl.create 10 in
    List.iter (fun s -> Hashtbl.add h s (`S (new set))) l;
    h

let add_formula f = function
    |`S set -> set#add (`Formula f)
    |_ -> failwith "add_formula"

let get_key f = "dd";;

let add_to_hash h ?(k = "") f =
    let key = if k = "" then get_key f else k in
    let s =
        try Hashtbl.find h key
        with Not_found ->
            failwith "add_to_hash: formula doesn't match any patterns"
    in
    add_formula f s;
    Hashtbl.replace h key s

let h =
    let h' : (string, mixlist) Hashtbl.t  = init_hash ["dd"] in
    add_to_hash h' (And(Var "a",Var "b")) ;
    h'

