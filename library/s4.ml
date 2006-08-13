
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Dia, "Dia_", Simple;
  Box, "Box_", Simple
END

HISTORIES
  DIAMONDS : Set.set;
  BOXES : Set.set
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
  END

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

PP := nnf_term
NEG := neg_term

let saturation = tactic ( (Id|And|T|Or)* )

STRATEGY ( saturation | S4 )*
