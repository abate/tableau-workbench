
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Zero;
  Falsum, Const;
  Verum, Const
END

HISTORIES
(bj : ListInt := new Set.set default [])
END

let nnf_term l = Basictype.map Pcopt.nnf l ;;
open Twblib
open Pcopt

TABLEAU

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
  {a & b}
 =========
   a; b
  END
  
  RULE Or
  { a v b } 
 ========================================
     fixlabel(a) | fixlabel(b) ; nnf_term(~ a)

   BRANCH [ backjumping(a,bj@1) ]
   BACKTRACK [ bj := mergelabel(a, bj@all) ]
  END

END

PP := Pcopt.nnf
NEG := Pclib.neg

STRATEGY := ( (Id|False|And|Or)* )


