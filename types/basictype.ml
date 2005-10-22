
type core = {
    id: int;
    star: int array;
}

let newcore id star = { id = id; star = star } ;;
let nc = newcore 1 [|0|] ;;

type formula =
    (* Classical logic *)
    |And of core * formula * formula
    |Or of core * formula * formula
    |Imp of core * formula * formula
    |DImp of core * formula * formula
    |Not of core * formula
    |Atom of core * string 
    |Constant of core * string

    (* basic modal logic *)
    |Dia of core * formula
    |Box of core * formula
   
    (* multi-modal logic *) 
    |Diai of int * core * formula
    |Boxi of int * core * formula
    
    (* temporal logic *)
    |Generally of core * formula
    |Sometimes of core * formula
    |Next of core * formula
    |Until of core * formula * formula
    |Before of core * formula * formula
    

type label = int list

type mixtype = [
    |`Int of int
    |`Bool of bool
    |`String of string
    |`Formula of formula
    |`LabeledFormula of (label * formula)
    |`Tuple of (int * int)
    |`Triple of (int * int * int)
    |`FormulaInt of (formula * int)
    |`FormulaTuple of (formula * formula)
    |`FormulaTriple of (formula * formula * formula)
]

(* XXX: to be generalized *)
let unbox = function 
    `Formula a -> a
    |_ -> failwith "unbox "
;;

(* is_marked returns true if the i-th element is equal to 1 *)
let is_marked_core ?(i=0) ?(v=1) n = ( n.star.(i) = v )
let mark_core ?(i=0) ?(v=1) n = ( n.star.(i) <- v ); n
let unmark_core ?(i=0) n = mark_core ~i ~v:0 n

let rec metamark f = function
    |And(c,f1,f2)  -> And(f c,f1,f2)
    |Or(c,f1,f2)   -> Or(f c,f1,f2)
    |Imp(c,f1,f2)  -> Imp(f c,f1,f2)
    |DImp(c,f1,f2) -> DImp(f c,f1,f2)
    |Not(c,f1)     -> Not(f c,f1)
    |Atom(c,s)     -> Atom(f c,s)
    |Constant(c,s)    -> Constant(f c,s)

    |Dia(c,f1)      -> Dia(f c,f1)
    |Box(c,f1)      -> Box(f c,f1)

    |Diai(i,c,f1)  -> Diai(i,f c,f1)
    |Boxi(i,c,f1)  -> Boxi(i,f c,f1)
    
    |Generally(c,f1) -> Generally(f c,f1) 
    |Sometimes(c,f1) -> Sometimes(f c,f1) 
    |Next(c,f1)      -> Next(f c,f1)
    |Until(c,f1,f2)  -> Until(f c,f1,f2)
    |Before(c,f1,f2) -> Before(f c,f1,f2)

;;

let mark_formula f   = `Formula ( metamark mark_core (unbox f));;
let unmark_formula f = `Formula ( metamark unmark_core (unbox f));;

let rec is_marked = function
    |And(c,_,_) 
    |Or(c,_,_)  
    |Imp(c,_,_) 
    |DImp(c,_,_)
    |Not(c,_)    
    |Atom(c,_)    
    |Constant(c,_) 

    |Dia(c,_)    
    |Box(c,_)    

    |Diai(_,c,_) 
    |Boxi(_,c,_) 
    
    |Generally(c,_)
    |Sometimes(c,_)
    |Next(c,_)    
    |Until(c,_,_)
    |Before(c,_,_)

    -> is_marked_core c
;;

let is_marked_formula f = is_marked (unbox f);;

let open_bt v = (v : mixtype :> [> mixtype] ) ;;
let open_bt_list v = (v : mixtype list :> [> mixtype] list ) ;;

(* is this needed (?) *)
let map f l = open_bt_list
    (List.map (function
        |`Formula t -> `Formula (f t)
        |_ -> failwith "only works for `Formula")
    l )
(* FIXME: this doesn't copy anything !!! *)
(* XXX: copy of formulae might be expensive ... *)
(* what's about a mutable part and an immutable part ??? *)
let copy f = f ;;


let rec default_printer = function
    |And(c,f1,f2) ->
            Printf.sprintf "(%s And %s)"
            (default_printer f1)
            (default_printer f2)
    |Or(c,f1,f2) ->
            Printf.sprintf "(%s Or %s)"
            (default_printer f1)
            (default_printer f2)
    |Imp(c,f1,f2) ->
            Printf.sprintf "(%s Imp %s)"
            (default_printer f1)
            (default_printer f2)
    |DImp(c,f1,f2) ->
            Printf.sprintf "(%s DImp %s)"
            (default_printer f1)
            (default_printer f2)
    |Not(c,f) -> Printf.sprintf "(Not %s)" (default_printer f)
    |Atom(c,s) -> s
    |Constant(c,s) -> s

    |Dia(c,f) -> Printf.sprintf "(Dia %s)" (default_printer f)
    |Box(c,f) -> Printf.sprintf "(Box %s)" (default_printer f)

    |Diai(i,c,f) -> Printf.sprintf "(Dia[%d] %s)" i (default_printer f)
    |Boxi(i,c,f) -> Printf.sprintf "(Box[%d] %s)" i (default_printer f)
   
    |Generally(c,f) -> Printf.sprintf "(G %s)" (default_printer f)
    |Sometimes(c,f) -> Printf.sprintf "(F %s)" (default_printer f)
    |Next(c,f)      -> Printf.sprintf "(X %s)" (default_printer f)
    |Until(c,f1,f2) ->
            Printf.sprintf "(%s U %s)"
            (default_printer f1)
            (default_printer f2)
    |Before(c,f1,f2) ->
            Printf.sprintf "(%s Bf %s)"
            (default_printer f1)
            (default_printer f2)
;;

let string_of_formula = ref default_printer ;;

let string_of_mixtype : mixtype -> string = function
    |`Int(i) -> string_of_int i
    |`Bool(b) -> string_of_bool b
    |`String(s) -> s
    |`Formula(f) -> !string_of_formula f
    |`LabeledFormula(il, f) ->
            let label = 
                List.fold_left (fun s i -> s^(string_of_int i) ) "" il in
            let formula = !string_of_formula f in
            Printf.sprintf "%s : %s" label formula
    |`Tuple(i1,i2) ->
            Printf.sprintf "(%d,%d)" i1 i2
            
    |`Triple(i1,i2,i3) ->
            Printf.sprintf "(%d,%d,%d)" i1 i2 i3
            
    |`FormulaInt(f,i) ->
            Printf.sprintf "(%s,%d)"
            (!string_of_formula f) i

    |`FormulaTuple (f1, f2) -> 
            Printf.sprintf "(%s,%s)"
            (!string_of_formula f1)
            (!string_of_formula f2)
            
    |`FormulaTriple (f1,f2,f3) -> 
            Printf.sprintf "(%s,%s,%s)"
            (!string_of_formula f1)
            (!string_of_formula f2)
            (!string_of_formula f3)
;;
