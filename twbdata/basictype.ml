
module Substlist = Data.Substlist

type core = {
    id: int;
    star: int array;
}

type formula =
    | And of core * formula * formula
    | Or of core * formula * formula
    | Atom of core * string 

type mixtype = [
    |`Int of int
    |`Bool of bool
    |`Formula of formula
    |`Tuple of (int * int)
    |`Triple of (int * int * int)
    |`FormulaTuple of (formula * formula)
    |`FormulaTruple of (formula * formula * formula)
]

type 'a patt = Var__p of string | Const__p of 'a 
type formula_p =
    | And_p of core * formula_p * formula_p
    | Or_p of core * formula_p * formula_p 
    | Atom_p of core * string
    | Var_p of core * string 
    
type mixtype_p = [
    |`Int_p of int patt
    |`Bool_p of bool patt
    |`Formula_p of formula_p
    |`Tuple_p of (int patt * int patt)
    |`Triple_p of (int patt * int patt * int patt)
    |`FormulaTuple_p of (formula_p * formula_p )
    |`FormulaTruple_p of (formula_p * formula_p * formula_p )
]

let is_var = function
    |`Int_p ( Var__p (_) )
    |`Bool_p ( Var__p (_) )
    |`Formula_p( Var_p (_) )
    |`Tuple_p ( Var__p (_) , Var__p (_) )
    |`Triple_p ( Var__p (_) , Var__p (_), Var__p (_) )
    |`FormulaTuple_p ( Var_p (_), Var_p (_) )
    |`FormulaTruple_p ( Var_p (_), Var_p (_) ,Var_p (_) ) -> true
    |_ -> false

exception FailedMatch

let rec match_formula sbl formula pattern =
    match formula,pattern with
    |And(cf,f1,f2),And_p(cp,p1,p2) when cf = cp ->
            match_formula( match_formula sbl f1 p1 ) f2 p2
    |Or(cf,f1,f2),Or_p(cp,p1,p2) when cf = cp ->
            match_formula( match_formula sbl f1 p1 ) f2 p2
    |Atom(cf,f),Atom_p(cp,p) when f = p && cf = cp -> sbl
    |_, Var_p(_,v) -> Substlist.add v (`Formula(formula)) sbl
    | _ -> raise FailedMatch

let rec match_type sbl formula pattern =
    match formula,pattern with
    |`Int(i),`Int_p(Const__p(c)) when i = c -> sbl
    |`Int(_),`Int_p(Var__p(v)) ->
            Substlist.add v formula sbl
    
    |`Formula(_),`Formula_p(Var_p(c,v)) ->
            Substlist.add v formula sbl
    |`Formula(f),`Formula_p(p) ->
            match_formula sbl f p
    
    |`Tuple(i1,i2),`Tuple_p(Const__p(c1),Const__p(c2)) 
    when i1 = c1 && i2 = c2 -> sbl
    |`Tuple(i1,i2),`Tuple_p(Var__p(v1),Var__p(v2)) ->
            List.fold_left (
                fun s (k,v) -> Substlist.add k (`Int(v)) s
            ) sbl [(v1,i1);(v2,i2)] 
            
    |`Tuple(i1,i2),`Tuple_p(Const__p(c1),Var__p(v2)) when i1 = c1 ->
            Substlist.add v2 (`Int(i2)) sbl
    |`Tuple(i1,i2),`Tuple_p(Var__p(v1),Const__p(c2)) when i2 = c2 ->
            Substlist.add v1 (`Int(i1)) sbl

    | _ -> raise FailedMatch

