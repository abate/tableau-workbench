
CONNECTIVES
[ "~";"&";"v";"<";">";"U";"*";",";"->";"<->";"[";"]" ]
GRAMMAR
program := 
      * program
    | program U program
    | Atom
    ;

formula :=
     Atom | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | < program > formula 
    | [ program ] formula 
    | ~ formula
    ;

expr := formula ;
END

TABLEAU

  RULE Union < A U B > P === < A > < B > P END
  RULE Star < * A > P === < A > < * A > P END

  RULE K < a > P ; [ a ] X ; Z  --- P ; X END
  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END

END
(*
STRATEGY := 
    let sat = tactic ( (False|Id|And|Or|Star|Union) )
    in tactic ( ( (sat)* ; K )* )

PP := List.map nnf
NEG := List.map neg

MAIN
*)
(*
let a = formula ( Verum ) 
let b = formula ( a v D ) 
let c = formula ( b & ( a v b ) )  
let d = formula ( < B > c ) 
let e = formula ( < * A U B > c & ( c v d ) ) 
let f = formula ( <> c ) 
let g = formula ( { formula ( A ) } v B ) 
let g = formula ( { nnf c } ) 
(* let h = expr ( 1 : < * A U B > c & ( c v d ) ) ;; *)
(* let i = expr ( [1] : b ) ;; *)

let ff = function
    |formula ( D ) -> 1 
    |formula ( < * A U B > e & ( c v d ) ) -> 1 
    |formula ( a & _ ) -> failwith "ff" 
    |formula ( _ ) -> failwith "ff"

(*
let ff = function
    |expr ( 1 : a ) -> 1 
    |expr ( _ ) -> 0
*)
*)
