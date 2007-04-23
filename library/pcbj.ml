
CONNECTIVES [ "~";"&";"v";"->";"<->" ]
GRAMMAR
formula :=
     Atom | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | ~ formula
    ;;

expr := int list : formula ;;
END

HISTORIES Idx : int := 0 END
VARIABLES bj  : int list := [] END

(* open Pclib *)
open Twblib
(* open Pcopt *)

TABLEAU

  RULE Id
  { i : a } ; { j : ~ a }
  =======================
    Close

  BACKTRACK [ bj := addlabel(I,J) ]
  END
  
  RULE False _ : Falsum === Close END
  RULE And {i : A & B} === i : A; i : B END
  (*
  RULE Or 
      { _ : A v B } 
  =====================
    Idx : a | Idx : b

  ACTION    [[ Idx := inc(Idx) ]; [ Idx := inc(Idx) ]]
  BRANCH    [ backjumping(Idx,bj@1) ]
  BACKTRACK [ bj := mergelabel(bj@all,status@last) ]
  END
  *)
END

STRATEGY := tactic ( (False|Id|And|Or)* )

PP := List.map nnf
NEG := List.map neg

MAIN
