
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Not, "~_",   Zero;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Box, "Box_", Zero;
  Dia, "Dia_", Zero;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  (BOXES : Set of Formula := new Set.set)
END

let simp (l,t,s) =
    let t' = Basictype.unbox(List.hd t) in
    let s' = Basictype.unbox s in
    Basictype.map (fun f -> Kopt.simpl s' f t') l
;;

open Twblib
open Klib

TABLEAU

  RULE K
  { Dia a } ; z
  ----------------------
    a ; BOXES

  ACTION [ BOXES := clear(BOXES) ]
  END

  RULE T
  { Box a }
  =========
     a

  COND notin(a, BOXES)

  ACTION [ BOXES := add(a,BOXES) ]
  END
 
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
  { a & b }
  ==========
    a ; b
  END
  
  RULE Or
  { a v b } ; x
 =================================
     a; simp(x,a,Verum) | b ; simp(x,b,Verum)
  END

END

PP := Kopt.nnf
NEG := neg

let saturate = tactic ( (False|Id|And|T|Or)* )

STRATEGY ( saturate | K )* 

