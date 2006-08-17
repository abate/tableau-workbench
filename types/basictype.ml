
type core = {
    id: int;
    star: int array;
}

let newcore id star = { id = id; star = star } ;;

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
    
    (* ctl *)
    |ExX of core * formula
    |AxX of core * formula
    |ExG of core * formula
    |ExF of core * formula
    |AxG of core * formula
    |AxF of core * formula

    (* lck *)
    |EDia of core * formula
    |EBox of core * formula
    |CDia of core * formula
    |CBox of core * formula
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

let open_bt v = (v : mixtype :> [> mixtype] ) ;;
let open_bt_list v = (v : mixtype list :> [> mixtype] list ) ;;

(* is this needed (?) *)
let map f l = open_bt_list
    (List.map (function
        |`Formula t -> `Formula (f t)
        |_ -> failwith "only works for `Formula")
    l )
;;

(* FIXME: this doesn't copy anything !!! *)
(* XXX: copy of formulae might be expensive ... *)
(* what's about a mutable part and an immutable part ??? *)
let copy f = f ;;

let string_of_formula = ref (fun _ -> failwith "printer not defined") ;;

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
