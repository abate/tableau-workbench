
CONNECTIVES
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_-->_", One;
  DImp, "_<-->_", One;
  Not, "~_",   Simple;
  Box, "Box_", Simple;
  Dia, "Dia_", Simple
END

let not_empty = function [] -> false | _ -> true

TABLEAU

  RULE K1
  { Dia A } ; Box X ; Dia Y ; Z
  -----------------------------
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
  { A --> B }
 ============
    ~ A | B
  END

  RULE DImp 
  { A <--> B }
 ==================
  A --> B | B --> A
  END

END

let strategy = new Strategy.strategy "start";;
let _ = 
    strategy#add "start" (R(new and_rule))  "start" "a" ;
    strategy#add "a"     (R(new or_rule))   "a" "i1" ;
    strategy#add "i1"    (R(new imp_rule))  "i1" "i2" ;
    strategy#add "i2"    (R(new dimp_rule)) "i2" "b" ;
    strategy#add "b"     (R(new id_rule))   "b" "s1";
    strategy#add "s1"    S                  "start" "d" ;
    strategy#add "d"     (R(new k1_rule))    "d" "s2";
    strategy#add "s2"    S                  "start" "end" ;
    strategy#add "end"   E                  "end" "end"
;;

STRATEGY (A)
