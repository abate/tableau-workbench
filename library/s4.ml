
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Dia, "Dia_", Simple;
  Box, "Box_", Simple;
  Boxi, "[_]_", Simple;
  Diai, "<_>_", Simple
END

HISTORIES
  DIAMONDS : Set.set;
  BOXES : Set.set
END

open Twblib
open Klib

let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

TABLEAU

  RULE S4 
  { Dia A } ; Dia Y ; Z
  =====================
  A ; BOXES || Dia Y 
  
  COND notin(Dia A, DIAMONDS)
  
  ACTION [
      [ DIAMONDS := add(Dia A,DIAMONDS);
        DIAMONDS := add(Dia Y,DIAMONDS) ]; [DIAMONDS := add(Dia A,DIAMONDS) ] ] 
  
  BRANCH [ not_emptylist(Dia Y) ] 
  END (cache)

  RULE S4IMP
  { Dia A } ; Z
  ----------------------
  A ; BOXES 
  
  COND notin(Dia A, DIAMONDS)
  ACTION [ DIAMONDS := add(Dia A,DIAMONDS) ]
  END

  RULE TNEW
  { Box A }
  =========
     A 

  COND notin(A, BOXES)
  
  ACTION [
      BOXES    := add(A,BOXES);
      DIAMONDS := emptyset (DIAMONDS) ]
  END

  RULE TOLD
  { Box A }
  =========
     A 

  COND isin(A, BOXES)
  END
  
  RULE Id
  { A } ; { ~ A }
  ===============
    Close
  END
  
  RULE And
  { A & B }
  =========
    A ; B
  END
  
  RULE Or
  { A v B }
 ==========
    A | B
  END

  RULE Imp 
  { A -> B }
 ============
    ~ A | B
  END

  RULE DImp 
  { A <-> B }
 ==================
  A -> B | B -> A
  END

END

PP := nnf
NEG := neg

let saturation = tactic ( (And|Or|Imp|Dimp|Tnew|Told|Id)* )

STRATEGY ( saturation | S4imp )*
