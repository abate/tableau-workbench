
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

TABLEAU

  RULE S4 
  { Dia a } ; Dia y ; z
  =====================
  a ; BOXES || Dia y 
  
  COND notin(Dia a, DIAMONDS)
  
  ACTION [
      [ DIAMONDS := add(Dia a,DIAMONDS);
        DIAMONDS := add(Dia y,DIAMONDS) ]; [DIAMONDS := add(Dia a,DIAMONDS) ] ] 
  
  BRANCH [ not_emptylist(Dia y) ] 
  END (cache)

  RULE S4IMP
  { Dia a } ; z
  ----------------------
  a ; BOXES 
  
  COND notin(Dia a, DIAMONDS)
  ACTION [ DIAMONDS := add(Dia a,DIAMONDS) ]
  END

  RULE TNEW
  { Box a }
  =========
     a 

  COND notin(a, BOXES)
  
  ACTION [
      BOXES    := add(a,BOXES);
      DIAMONDS := emptyset (DIAMONDS) ]
  END

  RULE TOLD
  { Box a }
  =========
     a 

  COND isin(a, BOXES)
  END
  
  RULE Id
  { a } ; { ~ a }
  ===============
    Close
  END
  
  RULE And
   a & b 
  =========
    a ; b
  END
  
  RULE Or
  { a v b }
 ==========
    a | b
  END

  RULE Imp 
  { a -> b }
 ============
    ~ a | b
  END

  RULE DImp 
  { a <-> b }
 ==================
  a -> b | b -> a
  END

END

PP := nnf_term
NEG := neg_term

let saturation = tactic ( (And|Or|Imp|Dimp|Tnew|Told|Id)* )

STRATEGY ( saturation | S4imp )*
