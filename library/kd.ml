
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Box, "Box_", Simple;
  Dia, "<>_", Simple;
  Falsum, Const;
  Verum, Const
END

open Twblib
open Klib

TABLEAU

  RULE KD
  ( <> a ) ; Box x ; z
  --------------------
        a ; x 
  END
 
  RULE Id
  { a } ; { ~ a }
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

let saturation = tactic ( (And;Or;Imp;Dimp;Id)* )

STRATEGY ( saturation ; Kd )*
