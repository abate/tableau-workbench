
CONNECTIVES [
    "~";"&";"v";"->";"<->";
    "E";"A";"U";"B";
    "AG";"EF";
    "EG";"AF";
    "AX";"EX"
]
GRAMMAR
formula :=
     ATOM | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | E formula B formula
    | E formula U formula
    | A formula B formula
    | A formula U formula
    | AF formula
    | EF formula
    | AG formula
    | EG formula
    | EX formula
    | AX formula
    | ~ formula
;;

expr := formula ;;
END

open Twblib
open CtlMarkFunctions
open CtlRewrite

HISTORIES
  HCore  : ListFormulaSet.olist := new ListFormulaSet.olist
END

VARIABLES
  uev : FormulaIntSet.set := new FormulaIntSet.set;
  mrk : bool := false
END

let nnf = List.map nnf_term 
let id x = x

TABLEAU

  RULE Id { P } ; { ~ P } == Stop 
  BACKTRACK [ mrk := true ]
  END
  RULE False { Falsum } == Stop 
  BACKTRACK [ mrk := true ]
  END

  RULE D
  EX Y ;  (AX P) == EX Verum ; AX P
  COND [ is_emptylist(EX Y) ]
  END

  RULE And P & Q == P ; Q END
  RULE Exb { E P B Q } == nnf(~ Q) ; P v EX (E P B Q) END
  RULE Axb { A P B Q } == nnf(~ Q) ; P v AX (A P B Q) END

  RULE Or
  { P v Q }
  =========
   P ||| Q

  BRANCH [ [ id(mrk@1) ] ] 
  BACKTRACK [ 
      uev := uev_disj(mrk@all, uev@all, P v Q);
      mrk := mrk_disj(mrk@all, uev@all, P v Q)
  ]
  END

  RULE Exu
      { E P U Q }
  ===================
  Q ||| P ; EX (E P U Q)

  BRANCH [ [ id(mrk@1) ] ] 
  BACKTRACK [ 
      uev := uev_disj(mrk@all, uev@all, E P U Q);
      mrk := mrk_disj(mrk@all, uev@all, E P U Q)
  ]
  END 

  RULE Axu
      { A P U Q }
  ===================
  Q ||| P ; AX (A P U Q)

  BRANCH    [ id(mrk@1) ]
  BACKTRACK [ 
      uev := uev_disj(mrk@all, uev@all, A P U Q);
      mrk := mrk_disj(mrk@all, uev@all, A P U Q)
  ]
  END 

  RULE Exx
  { EX P } ; EX X ; AX Y ; Z 
  ==========================
      P ; Y ||| EX X ; AX Y

  COND   [ loop_check(P, Y, HCore) ]
  ACTION [ [ HCore := push(P, Y, HCore) ] ; [] ] 
  BRANCH [ [ not(mrk@1) ; not_emptylist(EX X) ] ]
  BACKTRACK [
      uev := uev_ext(mrk@all, uev@all, P, Y, HCore);
      mrk := mrk_ext(mrk@all, uev@all, P, Y, HCore)
  ]
  CACHE := true
  END

  RULE Loop
        EX X ; AX Y  
  ==========================
           Stop

  COND [ not_emptylist(EX X) ]
  BACKTRACK [
      uev := uev_loop(X, Y, HCore);
      mrk := mrk_loop(X, Y, HCore)
  ]
  CACHE := true
  END

END

let exit = function
    |true -> "Closed"
    |false -> "Open"
 
PP := List.map nnf_term
NEG := List.map neg_term
EXIT := exit (mrk@1)
  
let saturation = tactic ( (Id ! False ! And ! Or ! Axu ! Exu ! Exb ! Axb ) )
let modal = tactic ( (saturation ! D ! Exx ! Loop ) )
STRATEGY := tactic ( (modal)* )

MAIN
