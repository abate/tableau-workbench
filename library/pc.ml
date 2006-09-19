
CONNECTIVES
DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_", Zero;
  Falsum, Const;
  Verum, Const
END

open Pclib

TABLEAU

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

PP := nnf
NEG := neg

(* STRATEGY (Id;And;Or)*  *)
STRATEGY (Id|And|Or)*

