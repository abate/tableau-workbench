
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
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

