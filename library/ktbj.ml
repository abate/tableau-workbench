
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
(BOXES : Set of Formula := new Set.set);
(bj : ListInt := new Set.set default [])
END

let nnf_term l = Basictype.map Kopt.nnf l ;; 

open Twblib
open Klib
open Pcopt

TABLEAU

  RULE K
  { Dia a } ; z
  ----------------------
    a ; BOXES

  ACTION [ BOXES := clear(BOXES) ]
  END

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

  BACKTRACK [ bj := addlabel(a, ~ a) ]
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
     fixlabel(a) | fixlabel(b) ; nnf_term(~ a)

  BRANCH [ backjumping(a,bj@1) ]
  BACKTRACK [ bj := mergelabel(a, bj@all) ]

  END

END

PP := Kopt.nnf
NEG := neg

let saturate = tactic ( (False|Id|And|T|Or)* )

STRATEGY := ( ( saturate | K )* )

