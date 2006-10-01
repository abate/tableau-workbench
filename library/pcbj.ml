
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_",   Zero;
  Falsum, Const;
  Verum, Const
END

HISTORIES
(Idx : Int := new Set.set default 0);
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
 ===========================
  fixlabel(Idx,a) | fixlabel(Idx,b) 

  ACTION    [[ Idx := inc(Idx) ]; [ Idx := inc(Idx) ]]
  BRANCH    [ backjumping(Idx,bj@1) ]
  BACKTRACK [ bj := mergelabel(bj@all,status@last) ]
  END

END

PP := Pcopt.nnf
NEG := Pclib.neg

STRATEGY := ( (Id|False|And|Or)* )


