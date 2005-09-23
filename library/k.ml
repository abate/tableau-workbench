
CONNECTIVES
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_-->_", One;
  DImp, "_<-->_", One;
  Not, "~_",   Simple;
  Box, "Box_", Simple;
  Dia, "Dia_", Simple
END

let print () s = ()
(*    print_endline ("Rule: "^s);
    print_newline () *)
;;

TABLEAU
  RULE K1
  { Dia A } ; Box X ; Dia Y ; Z
  -----------------------------
      A ; X || Dia Y ; Box X

  ACTION [ [print () "K down right"]; [print () "K down left"] ]
  END

  RULE K
  { Dia A } ; Box X ; Z
  =====================
    A ; X

    ACTION [ print () "K down" ]
  END
 
  RULE Id
  { A } ; { ~ A }
  ---------------
    Close

    ACTION [ print () "ID down" ]
  END
  
  RULE And
  { A & B }
 ------------
    A ; B
    
    ACTION [ print () "And down" ]
  END
  
  RULE Or
  { A v B }
 ------------
    A | B

    ACTION [ [ print () "Or down right" ]; [print () "Or down left"] ]
  END

  RULE Imp 
  { A --> B }
 ------------
    ~ A | B

    ACTION [ [ print () "Imp down right" ]; [print () "Imp down left"] ]
  END

  RULE DImp 
  { A <--> B }
 -------------------
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
    strategy#add "d"     (R(new k_rule))    "d" "s2";
    strategy#add "s2"    S                  "start" "end" ;
    strategy#add "end"   E                  "end" "end"
;;

STRATEGY (A)
