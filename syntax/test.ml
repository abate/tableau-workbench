
CONNECTIVES
  And, "_&_",  One;
  Or,  "_v_",  One;
  Not, "~_",   Simple;
  Box, "Box_", Simple;
  Dia, "Dia_", Simple
END

(*
HISTORY
  DIAMONDS : Set;
  BOXES : Set;
END
*)

(*
let notin f h = not(h#mem f)
let add f h = h#add f
let empty s = s#is_empty
*)
TABLEAU
(*
  RULE K1
      { Dia A } ; Box X; Dia Y ; Z
  --------------------------------------------
      A ; X || Dia Y ; Box X

  BRANCH empty(Dia Y)
  END

  RULE T 
     { Box A } ; Z
  ----------------------
     A ; Box A; Z
      
  COND not_starred(Box A)
  ACTION [ star(Box A) ]
  END

  RULE S4 
  { Dia A } ; Box X; Dia Y ; Z
  -----------------------------
     A ; X || Dia Y ; Box X
      
  COND notin(Dia A, DIAMONDS)
  
  ACTION [
      [ BOXES = add(Box X,BOXES); 
        DIAMONDS = add(Dia A,DIAMONDS);
        DIAMONDS = add(Dia Y,DIAMONDS)];
      [ DIAMONDS = add(Dia A,DIAMONDS);
        DIAMONDS = add(Dia Y,DIAMONDS) ]
  ] 
  
  BRANCH [ empty(Dia Y) ] 
  END
  *)
  RULE K
  { Dia A } ; Box X; Z
  =====================
    A ; X
  END
 
  RULE Id
  { A } ; { ~ A }
  ---------------
    Close
  END
  
  RULE AntiId
  { .a } ; .z 
  ------------
    Open
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

END

(* STRATEGY ((Id; And; Or; Not)* ; K)* *)

Strategy.add "start" (R(new and_rule)) "start" "a" ;
Strategy.add "a" (R(new or_rule)) "a" "b" ;
Strategy.add "b" (R(new id_rule)) "b" "b1";
Strategy.add "b1" (R(new antiid_rule)) "b1" "s1";
Strategy.add "s1" S "a" "d" ;
Strategy.add "d" (R(new k_rule)) "d" "s2";
Strategy.add "s2" S "start" "end" ;
Strategy.add "end" E "end" "end" ; 

