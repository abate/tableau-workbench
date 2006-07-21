
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Box, "Box_", Simple;
  Dia, "Dia_", Simple;
  Falsum, Const;
  Verum, Const
END

open Klib

let not_empty = function [] -> false | _ -> true

TABLEAU

  RULE K1
  { Dia A } ; Box X ; Dia Y ; Z
  ===========================
      A ; X || Dia Y ; Box X

  BRANCH [ not_empty(Dia Y) ]
  END

  RULE K
  { Dia A } ; Box X ; Z
  ----------------------
    A ; X
  END
 
  RULE Id
  { A } ; { ~ A }
  ===============
    Close
  END
  
  RULE And
  { A & B }
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
 ============
    ~ A | B
  END

  RULE DImp 
  { A <-> B }
 ==================
  A -> B | B -> A
  END

END

let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

PP := nnf
NEG := neg

let t = tactic ( (Id|And|Or)* )

STRATEGY ( t | K )* 

