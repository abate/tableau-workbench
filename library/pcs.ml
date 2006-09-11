
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Zero;
  Falsum, Const;
  Verum, Const
END

SIMPLIFICATION := Pcopt.simpl
let nnf_term l = Pcopt.nnf (Basictype.unbox(List.hd l)) ;;


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
  {a & b} ; x
 ============================
     a[b]; b[a] ; x[a][b]
  END
  
  RULE Or
  { a v b } ; x
 ===============================
     a ; x[a] | b ; x[b][nnf_term ( ~ a)]
  END

END

PP := Pcopt.nnf
NEG := Pclib.neg

STRATEGY := ( (Id|False|And|Or)* )


