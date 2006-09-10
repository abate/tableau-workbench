
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Zero;
  Falsum, Const;
  Verum, Const
END

open Pclib

let __simplification l = Basictype.map simpl l ;;

TABLEAU

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
 ============================
  a ; b ; x[a/Verum][b/Verum]
  END
  
  RULE Or
  { a v b } ; x
 ===============================
 a ; x[a/Verum] | b ; x[b/Verum] 
  END

END

PP := nnf
NEG := neg

STRATEGY (Id|And|Or)*

