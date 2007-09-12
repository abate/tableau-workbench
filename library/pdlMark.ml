
CONNECTIVES
[ "~";"&";"v";"<";">";"U";"*";",";"->";"<->";"[";"]";";";"?"]
GRAMMAR
program := 
      * program
    | ? formula
    | program U program
    | program ; program
    | ATOM
;;

formula :=
     ATOM | Verum | Falsum
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

(* the warning : Warning U: this match case is unused. 
 * is innocuous and can be ignored *)

open Twblib
open PdlMarkRewrite
open PdlMarkFunctions

HISTORIES
  HCore  : ListFormulaSet.olist := new ListFormulaSet.olist
END

VARIABLES
  uev : FormulaIntSet.set := new FormulaIntSet.set;
  mrk : bool := false
END

let nnf = List.map nnf_term

TABLEAU
  RULE Id { P } ; { ~ P } == Stop
  BACKTRACK [
      uev := uevundef ();
      mrk := true
  ]
  END

  RULE False { Falsum } == Stop
  BACKTRACK [
      uev := uevundef ();
      mrk := true
  ]
  END

  RULE And { A & B } === A ; B END
  RULE UnionBox { [ A U B ] P } === [ A ] P ;  [ B ] P END
  RULE SeqBox { [ A ; B ] P } === [ A ] [ B ] P END
  RULE StarBox { [ * A ] P } === P ; [ A ] [ * A ] P END

  RULE TestDia { < ? F > P } === F ; P 
  BACKTRACK [ uev := set_uev_TestDia(uev@1) ]
  END

  RULE SeqDia { < A ; B > P } === < A > < B > P 
  BACKTRACK [ uev := set_uev_SeqDia(uev@1) ]
  END

  RULE Or
  { P v Q }
  =========
   P ||| Q

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj(mrk@all, uev@all);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE TestBox
    { [ ? F ] P } === nnf ( ~ F ) ||| P

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj(mrk@all, uev@all);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE UnionDia
    { < A U B > P } === < A > P ||| < B > P

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj(mrk@all, set_uev_UnionDia (< A U B > P, uev@all));
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE StarDia
    { < * A > P } === P ||| < A > < * A > P

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj(mrk@all, set_uev_StarDia(< * A > P , uev@all));
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE K 
  { < a > P }  ; [ a ] Y ; < B > E ; [ C ] F ; Z 
   =============================================
       P ; Y ||| < B > E ; [ C ] F

  COND   [ loop_check(P, Y, HCore) ]
  ACTION [ [ HCore := push(P, Y, HCore) ] ; [] ]
  BRANCH [ [ test_ext(mrk@1, uev@1, P, Y, HCore) ; not_emptylist(< B > E) ] ]
  BACKTRACK [
      uev := uev_ext(mrk@all, uev@all, < a > P, Y, HCore);
      mrk := mrk_ext(mrk@all, uev@all, < a > P, Y, HCore)
  ]
  CACHE := true
  END

  RULE Loop
       < A > X ; [ B ] Y
    =====================
             Stop

  BACKTRACK [
      uev := uev_loop(<A>X, [B]Y, HCore);
      mrk := false
  ]
  CACHE := true
  END

END

STRATEGY := 
    let sat = tactic ( (False ! Id ! And ! Or ! 
                        StarDia ! StarBox ! UnionDia !
                        UnionBox ! SeqBox ! SeqDia ! 
                        TestDia ! TestBox) )
    in tactic ( (sat ! K ! Loop)* )

let exit = function
    |true -> "Closed"
    |false -> "Open"

PP := nnf
NEG := List.map neg_term
EXIT := exit (mrk@1)

MAIN
