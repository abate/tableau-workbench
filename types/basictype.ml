
type core = {
    id: int;
    star: int array;
}

let newcore id star = { id = id; star = star }
let nc = newcore 1 [|0|]

type formula =
    |And of core * formula * formula
    |Or of core * formula * formula
    |Imp of core * formula * formula
    |DImp of core * formula * formula
    |Not of core * formula
    |Dia of core * formula
    |Box of core * formula
    |Diai of int * core * formula
    |Boxi of int * core * formula

    |Atom of core * string 

type label = int list

type mixtype = [
    |`Int of int
    |`Bool of bool
    |`Formula of formula
    |`LabeledFormula of (label * formula)
    |`Tuple of (int * int)
    |`Triple of (int * int * int)
    |`FormulaTuple of (formula * formula)
    |`FormulaTriple of (formula * formula * formula)
]

let open_bt v = (v : mixtype :> [> mixtype] )
let open_bt_list v = (v : mixtype list :> [> mixtype] list )

(* is this needed (?) *)
let map f l = open_bt_list (List.map f l)

(* FIXME: this doesn't copy anything !!! *)
(* XXX: copy of formulae might be expensive ... *)
(* what's about a mutable part and an immutable part ??? *)
let copy f = f

let rec string_of_formula = function
    |And(c,f1,f2) ->
            Printf.sprintf "(%s And %s)"
            (string_of_formula f1)
            (string_of_formula f2)
    |Or(c,f1,f2) ->
            Printf.sprintf "(%s Or %s)"
            (string_of_formula f1)
            (string_of_formula f2)
    |Imp(c,f1,f2) ->
            Printf.sprintf "(%s Imp %s)"
            (string_of_formula f1)
            (string_of_formula f2)
    |DImp(c,f1,f2) ->
            Printf.sprintf "(%s DImp %s)"
            (string_of_formula f1)
            (string_of_formula f2)
    |Not(c,f) -> Printf.sprintf "(Not %s)" (string_of_formula f)
    |Diai(i,c,f) -> Printf.sprintf "(Dia[%d] %s)" i (string_of_formula f)
    |Boxi(i,c,f) -> Printf.sprintf "(Box[%d] %s)" i (string_of_formula f)
    |Dia(c,f) -> Printf.sprintf "(Dia %s)" (string_of_formula f)
    |Box(c,f) -> Printf.sprintf "(Box %s)" (string_of_formula f)
    |Atom(c,s) -> s
                
let string_of_mixtype : mixtype -> string = function
    |`Int(i) -> string_of_int i
    |`Bool(b) -> string_of_bool b
    |`Formula(f) -> string_of_formula f
    |`LabeledFormula(il, f) ->
            let label = 
                List.fold_left (fun s i -> s^(string_of_int i) ) "" il in
            let formula = string_of_formula f in
            Printf.sprintf "%s : %s" label formula
    |`Tuple(i1,i2) ->
            Printf.sprintf "(%d,%d)" i1 i2
            
    |`Triple(i1,i2,i3) ->
            Printf.sprintf "(%d,%d,%d)" i1 i2 i3
            
    |`FormulaTuple (f1, f2) -> 
            Printf.sprintf "(%s,%s)"
            (string_of_formula f1)
            (string_of_formula f2)
            
    |`FormulaTriple (f1,f2,f3) -> 
            Printf.sprintf "(%s,%s,%s)"
            (string_of_formula f1)
            (string_of_formula f2)
            (string_of_formula f3)

