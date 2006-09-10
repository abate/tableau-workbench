
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Zero;
  Falsum, Const;
  Verum, Const
END

let __simplification l = Basictype.map Pclib.simpl l ;;

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
  a & b 
 ============================
  a; b
  END
  
  RULE Or
  { a v b } ; x
 ===============================
 a ; x[a/Verum] | b ; x[b/Verum] 
  END

END

PP := Pcopt.nnf
NEG := Pclib.neg

STRATEGY (Id|False|And|Or)*

