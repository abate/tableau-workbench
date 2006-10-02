
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_",   Zero;
  Box, "Box_", Zero;
  Dia, "Dia_", Zero;
  Falsum, Const;
  Verum, Const
END

open Twblib
open Klib

TABLEAU

  RULE K1
  { Dia a } ; Box x ; Dia y ; z
  ===========================
      a ; x || Dia y ; Box x

  BRANCH [ not_emptylist(Dia y) ]
  END (cache)

  RULE K
  { Dia a } ; Box x ; z
  ----------------------
    a ; x
  END (cache)
 
  RULE Id
  { a } ; { ~ a }
  ===============
    Close
  END
  
  RULE False
     Falsum
  ===============
    Close
  END

  RULE And
  { a & b }
  ==========
    a ; b
  END
  
  RULE Or
  { a v b }
 ==========
    a | b
  END

END

PP := Kopt.nnf
NEG := neg

let t = tactic ( (Id|False|And|Or)* )

STRATEGY ( t | K )* 

