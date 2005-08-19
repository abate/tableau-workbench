
CONNECTIVES
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple
END

TABLEAU
 
  RULE Id
  { A } ; { ~ A }
  ---------------
    Close
  END
  
  RULE And
  { A & B }
 ------------
    A ; B
  END
  
  RULE Or
  { A v B }
 ------------
    A | B
  END

  RULE Imp 
  { A -> B }
 ------------
    ~ A | B
  END

  RULE DImp 
  { A <-> B }
 -------------------
    A -> B | B -> A
  END

END

(* STRATEGY ((Id; And; Or; Not)* ; K)* *)

Strategy.add "start" (R(new and_rule)) "start" "a" ;
Strategy.add "a" (R(new or_rule)) "a" "i1" ;
Strategy.add "i1" (R(new imp_rule)) "i1" "i2" ;
Strategy.add "i2" (R(new dimp_rule)) "i2" "b" ;
Strategy.add "b" (R(new id_rule)) "b" "s2";
Strategy.add "s2" S "start" "end" ;
Strategy.add "end" E "end" "end" ; 

STRATEGY (A)
