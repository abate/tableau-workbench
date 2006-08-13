
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Falsum, Const
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
   a & b 
 ==========
    a ; b
  END
  
  RULE Or
  { a v b }
 ==========
     a | b 
  END

  RULE Imp 
  { a -> b }
 ===========
    ~ a | b
  END

  RULE Mp 
  { a } ; { a -> b }
 ===========
    b
  END

  RULE DImp 
  a <-> b
  ===============
  a -> b ; b -> a
  END

END

PP := nnf_term
NEG := neg_term

(* STRATEGY (Id;And;Or)*  *)
STRATEGY (Id|And|Or)*

