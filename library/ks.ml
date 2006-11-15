
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Not, "~_",   Zero;
  Imp, "_->_", One;
  Box, "Box_", Zero;
  Dia, "Dia_", Zero;
  Falsum, Const;
  Verum, Const
END

SIMPLIFICATION := Kopt.simpl
let nnf_term l = ([],Kopt.nnf (Basictype.unbox(List.hd l))) ;;
let nnf = Kopt.nnf ;;

open Twblib
open Klib

TABLEAU

  RULE K
  { Dia a } ; Box x ; z
  ----------------------
    a ; x[a]

  END (cache)

  RULE Id
  { a } ; { ~ a }
  ===============
    Close
  END (cache)

  RULE False
    Falsum
  =========
    Close
  END

  RULE And
  { a & b } ; x
  =========
    a[b] ; b[a] ; x[a][b]
  END
  
  RULE Or
  { a v b } ; x
 =================================
     a ; x[a] | b[nnf_term(~ a)] ; x[b][nnf_term(~ a)]
  END

END

PP := Kopt.nnf
NEG := neg

let saturate = tactic ( (False|Id|And|Or)* )

STRATEGY := ( ( saturate ; K )* )

