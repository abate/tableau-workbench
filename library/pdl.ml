
CONNECTIVES
[ "~";"&";"v";"<";">";"U";"*";",";"->";"<->";"[";"]";";" ]
GRAMMAR
program := 
      * program
    | program U program
    | program ; program
    | Atom
;;

formula :=
     Atom | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | < program > formula 
    | [ program ] formula 
    | ~ formula
;;

expr := formula ;;
END

open Twblib
open PdlRewrite
open PdlFunctions

HISTORIES
  Fev : FormulaSet.set := new FormulaSet.set;
  Br  : ListFormulaSet.olist := new ListFormulaSet.olist
END

VARIABLES
  uev : FormulaIntSet.set := new FormulaIntSet.set;
  fev : FormulaIntSet.set := new FormulaIntSet.set;
  status : string := "Undef"
END

TABLEAU

RULE Or 
  { A v B } === A ||| B

  BRANCH [ [ not_emptyset(uev@1) ] ]
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ]
END

RULE UnionD
  { < A U B > P } === < A > P ||| < B > P

  BRANCH [ [ not_emptyset(uev@1) ] ]
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ]
END


RULE StarD
  { < * A > P } === P ||| < A > < * A > P

  BRANCH [ [ not_emptyset(uev@1) ] ]
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ]
END

RULE K 
  { < a > P }  ; [ a ] Y ; Z --- P ; Y

  COND [ loop_check(P, Y, Br) ]
  ACTION [ Br  := push(P, Y, Fev, Br); Fev := emptyset(Fev) ]
  BRANCH [ not_false(uev@1) ]
  BACKTRACK [ uev := setuev_pi(uev@1, uev@2, Br) ]

END

RULE Loop
  < a > P ; [ a ] Y == Stop
  COND [ not_emptylist(< a > P) ]
  BACKTRACK [ uev := setuev_loop(P, Y, Fev, Br) ]
END

RULE And { A & B } === A ; B END
RULE StarB { [ * A ] P } === P ; [ A ] [ * A ] P END
RULE UnionB { [ A U B ] P } === [ A ] P ;  [ B ] P END
RULE SeqB { [ A ; B ] P } === [ A ] [ B ] P END
RULE SeqD { < A ; B > P } === < A > < B > P END

RULE Id
  { P } ; { ~ P } == Stop
  BACKTRACK [ uev := setclose (Br) ]
END

RULE False
  { Falsum } === Stop
  BACKTRACK [ uev := setclose (Br) ]
END

END

STRATEGY := 
    let sat = tactic ( (False ! Id ! And ! Or ! StarD ! StarB ! UnionD ! UnionB ! SeqB ! SeqD) )
    in tactic ( ( (sat)* ; (K  !  Loop) )* )

let exit (uev) = match uev#elements with
    |[] -> "Open"
    |[formula ( Falsum ),_] -> "Closed"
    |_ -> "Closed"

EXIT := exit (uev@1)
PP := List.map nnf
NEG := List.map neg

MAIN
