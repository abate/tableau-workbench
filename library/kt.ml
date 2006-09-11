
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

SIMPLIFICATION := Kopt.simpl
let nnf_term l = Kopt.nnf (Basictype.unbox(List.hd l)) ;;

open Twblib
open Klib

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
  END

  RULE False
    Falsum
  =========
    Close
  END

  RULE And
  { a & b } ; x
  ==========
      a[b] ; b[a] ; x[a][b]
  END
  
  RULE Or
  { a v b } ; x
 =================================
     a ; x[a] | b[nnf_term (~ a)] ; x[b][nnf_term (~ a)]
  END

END

PP := Kopt.nnf
NEG := neg

let saturate = tactic ( (False|Id|And|T|Or)* )

STRATEGY := ( ( saturate | K )* )

