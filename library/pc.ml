
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
  { A } ; { ~ A }
  ===============
    Close
  END
  
  RULE False
     Falsum
  ===============
    Close
  END

  RULE And
   A & B 
 ==========
    A ; B
  END
  
  RULE Or
  { A v B }
 ==========
   A | B 
  END

  RULE Imp 
  { A -> B }
 ===========
    ~ A | B
  END

  RULE DImp 
  A <-> B
  ===============
  A -> B ; B -> A
  END

END

let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

PP := nnf
NEG := neg

(* STRATEGY (Id;And;Or)*  *)
STRATEGY (Id|And|Or)*

