
type formula =
    (* Classical logic *)
    |And  of  formula * formula
    |Or   of  formula * formula
    |Imp  of  formula * formula
    |DImp of  formula * formula
    |Not  of  formula
    |Atom of  string 
    |Constant of  string

    (* basic modal logic *)
    |Dia of  formula
    |Box of  formula
   
    (* multi-modal logic *) 
    |Diai of int *  formula
    |Boxi of int *  formula
    
    (* temporal logic *)
    |Generally of  formula
    |Sometimes of  formula
    |Next   of  formula
    |Until  of  formula * formula
    |Before of  formula * formula
    
    (* ctl *)
    |ExX of  formula
    |AxX of  formula
    |ExG of  formula
    |ExF of  formula
    |AxG of  formula
    |AxF of  formula

    (* lck *)
    |EDia of  formula
    |EBox of  formula
    |CDia of  formula
    |CBox of  formula
type label = int list

type mixtype = [
    |`Int of int
    |`Bool of bool
    |`String of string
    |`ListInt of int list
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

let unbox f =
    match open_bt f with
    |`Formula t -> t
    |`LabeledFormula (_,t) -> t
    |_ -> failwith "only works for `Formula and LabeledFormula"
;;

let map f l =
    open_bt_list (
        List.map (fun t ->
            match t with
            |`Formula _ -> `Formula (f (unbox t))
            |`LabeledFormula (l,_) -> `LabeledFormula (l, f (unbox t))
            |_ -> failwith "only works for `Formula and LabeledFormula"
        ) l
    )
;;

(* ???? *)
let copy f = f ;;

let string_of_formula = ref (fun _ -> failwith "printer not defined") ;;

let compare a b =
    match a,b with
    |`LabeledFormula (_,t1),`LabeledFormula (_,t2) -> Pervasives.compare t1 t2
    |_,_ -> Pervasives.compare a b
;;

let string_of_mixtype : mixtype -> string = function
    |`Int(i) -> string_of_int i
    |`Bool(b) -> string_of_bool b
    |`String(s) -> s
    |`ListInt(l) ->  List.fold_left (fun s i -> s^(string_of_int i) ) "" l
    |`Formula(f) -> !string_of_formula f
    |`LabeledFormula(il, f) -> !string_of_formula f
(*            let label = 
                List.fold_left (fun s i -> s^(string_of_int i) ) "" il in
            let formula = !string_of_formula f in
            Printf.sprintf "%s : %s" label formula
            *)
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
