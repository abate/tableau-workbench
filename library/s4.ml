
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_",   Zero;
  Dia, "Dia_", Zero;
  Box, "Box_", Zero
END

HISTORIES
  (DIAMONDS : Set of Formula := new Set.set);
  (BOXES : Set of Formula := new Set.set)
END

open Twblib
open Klib

TABLEAU

  RULE S4
  { Dia a } ; z
  ----------------------
  a ; BOXES 
  
  COND notin(Dia a, DIAMONDS)
  ACTION [ DIAMONDS := add(Dia a,DIAMONDS) ]
  END (cache)

  RULE S4H
  { Dia a } ; Dia y ; z
  ===============================
     a ; BOXES || Dia y

  COND notin(Dia a, DIAMONDS)

  ACTION [
      [ DIAMONDS := add(Dia a,DIAMONDS);
        DIAMONDS := add(Dia y,DIAMONDS)];

      [ DIAMONDS := add(Dia a,DIAMONDS) ]
  ]

  BRANCH [ not_emptylist(Dia y) ]
  END (cache)

  RULE T
  { Box a }
  =========
     a 

  COND notin(a, BOXES)
  
  ACTION [
      BOXES    := add(a,BOXES);
      DIAMONDS := emptyset (DIAMONDS) ]
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

END

PP := nnf
NEG := neg

let saturation = tactic ( (Id|And|T|Or)* )

STRATEGY ( saturation | S4 )*
