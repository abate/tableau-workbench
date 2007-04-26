
source K

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer 
        let copy s = s
    end
)

HISTORIES
  DIAMONDS : FormulaSet.set := new FormulaSet.set;
  BOXES    : FormulaSet.set := new FormulaSet.set
END

open Twblib
open Klib

TABLEAU

  RULE K4
  { <> A } ; Z --- A ; BOXES
  COND notin(<> A, DIAMONDS)
  ACTION [ DIAMONDS := add(<> A,DIAMONDS) ]
  END

  RULE NewBox
  { [] A } ; Z === Z
  COND notin(A, BOXES)
  ACTION [
      BOXES    := add(A,BOXES);
      DIAMONDS := emptyset(DIAMONDS)]
  END

  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END
  
END

STRATEGY := 
    let sat = tactic ( (False|Id|And|NewBox|Or) )
    in tactic ( ( (sat)* ; K4 )* )

PP := List.map nnf
NEG := List.map neg

MAIN
