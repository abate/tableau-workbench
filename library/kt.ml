
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Not, "~_",   Zero;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Box, "Box_", Zero;
  Dia, "Dia_", Zero;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  (BOXES : Set of Formula := new Set.set)
END

open Twblib
open Klib

TABLEAU

  RULE K
  { Dia a } ; z
  ----------------------
    a ; BOXES

  ACTION [ BOXES := clear(BOXES) ]
  END (CACHE)

  RULE T
  { Box a }
  =========
     a

  COND notin(a, BOXES)

  ACTION [ BOXES := add(a,BOXES) ]
  END
 
  RULE Id
  { a } ; { ~ a }
  ===============
    Close
  END

  RULE False
    Falsum
  =========
    Close
  END

  RULE And
  { a & b } 
  ==========
   a ; b
  END
  
  RULE Or
  { a v b }
 =================================
     a | b
  END

END

PP := Kopt.nnf
NEG := neg

let saturate = tactic ( (False|Id|And|T|Or)* )

STRATEGY := ( ( saturate ; K )* )

