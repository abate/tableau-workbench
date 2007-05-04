
(* This is a prover for KLM logic P as defined in the work of
   L Gordano, V Gliozzi, N Olivetti, G Pozzato
   "Analytic tableaux for KLM Preferential and Cummulative Logic"
   Proceedings of LPAR 2005 LNAI 3835:666-681, Springer, 2005.
*)


CONNECTIVES [
    "~" ; "&" ; "v" ; "->" ; "<->"
  ; "Dia" ; "Box"
  ; "=>"  (* Conditional Implication *)
]

GRAMMAR 
atm := Atom | Verum | Falsum
;;

propfml := propfml & propfml
         | propfml v propfml
         | propfml -> propfml
         | propfml <-> propfml
         | ~ propfml
         | atm 
;;

formula := formula & formula
         | formula v formula
         | formula -> formula
         | formula <-> formula
         | propfml => propfml
         | ~ formula
         | Box formula
         | Dia formula
         | propfml

;;

expr := formula ;;
END

HISTORIES
  CIMPS : FormulaSet.set := new FormulaSet.set
END

open Twblib
open Klmlib

TABLEAU

  RULE CImpp { A => B }       == nnf( ~ A ) | Dia A  | nnf( B )  
       ACTION [ CIMPS  := add(A => B, CIMPS) ]
  END

  RULE False { Falsum }       == Close  END
  RULE ID    { A } ; { ~ A }  == Close  END     (* formulae not atoms! *)
  RULE And     X & Y          == X ; Y  END
  RULE Or    { A v B }        == A | B  END


(* The following two rules are non-invertible                 *)
(* So they need some sort of special trick to make then work  *)
(* under the current TWB                                      *)

(* 
   It is imperative to never jump on the same Dia A twice to
   maintain the well-foundedness of the underlying transitive
   relation. We achieve this by storing Box ~ Dia A in the 
   denominator. From now on, every Dia jump will bring out the 
   ~ Dia A. So if Dia A ever turns up again (ID) will close the
   branch before jumping on Dia A again.
*)

  RULE CImpm { ~ ( A => B ) } ; ~ ( X => Y ) ; Z
             ----------------------------------------------------
             nnf(A) ; Box ~ Dia A ; nnf(~ B) ; ~ (X => Y) ; CIMPS
  END

  RULE Dia   { Dia A } ; ~ (X => Y) ; Box W ; Z
             ------------------------------------------------------
             nnf(A) ; Box ~ Dia  A ; ~ (X => Y) ; W ; Box W ; CIMPS 
  END
END

PP := List.map nnf
NEG := List.map neg

let saturate = tactic (False | Id | And | Or | CImpp)
STRATEGY tactic ( ( (saturate)* ; (CImpm | Dia) )* )
