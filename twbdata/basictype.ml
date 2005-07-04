
type core = {
    id: int;
    star: int array;
}

let newcore id star = { id = id; star = star }

type formula =
    |And of core * formula * formula
    |Or of core * formula * formula
    |Not of core * formula
    |Atom of core * string 

type mixtype = [
    |`Int of int
    |`Bool of bool
    |`Formula of formula
    |`Tuple of (int * int)
    |`Triple of (int * int * int)
    |`FormulaTuple of (formula * formula)
    |`FormulaTriple of (formula * formula * formula)
]

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
    |Not(c,f) -> Printf.sprintf "(Not %s)" (string_of_formula f)
    |Atom(c,s) -> s
                
let string_of_mixtype = function
    |`Int(i) -> string_of_int i
    |`Bool(b) -> string_of_bool b
    |`Formula(f) -> string_of_formula f
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

