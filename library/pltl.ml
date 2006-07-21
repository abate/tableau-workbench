
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Until, "_Un_", One;
  Before, "_Bf_", One;
  Not, "~_",   Simple;
  Next, "X_", Simple;
  Generally, "G_", Simple;
  Sometimes, "F_", Simple;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  Ev : Set.set ;
  Br : Listoftupleset.listobj;
  uev : Set.set;
  status : String;
  n : Int default 0
END

open Twblib
open PltlRewrite
open PltlFunctions

let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

TABLEAU

  RULE Id
  { A } ; { ~ A } ; Z
  ===============
     Stop

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END
  
  RULE False
  Falsum ; Z
  ===============
     Stop

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END

  RULE Loop
  { X A } ; X B ; Z
  =================
       Stop

  BACKTRACK [
      uev := setuev(X A, X B, Z, Ev, Br);
      n   := setn (X A, X B, Z, Br)
  ]

  END

  RULE Next
  { X A } ; X B ; Z
  =================
      A ; B
      
  COND [ loop_check(X A, X B, Z, Br) ]
  ACTION [
      Ev := emptyset(Ev);
      Br := push(X A, X B, Z, Ev, Br)
  ]

  END

  RULE Before
    {A Bf C}
  ==========================
   nnf (~ C) ; A v X (A Bf C)

  END

  RULE Until
           { C Un D } 
  =============================
      D ||| C ; X ( C Un D ) 

  ACTION    [ [ Ev := add(D, Ev) ] ; [] ]
  BACKTRACK [ 
      uev := beta(uev(1), uev(2), n(1), n(2), Br);
      n := min (n(1), n(2))
  ]
  BRANCH    [ [ not_emptyset(uev(1)) ] ] 
    
  END
 
  RULE Or
  { A v B }
  =========
   A ||| B

  BACKTRACK [ 
      uev := beta(uev(1), uev(2), n(1), n(2), Br);
      n := min (n(1) , n(2))
  ]

  BRANCH [ [ not_emptyset(uev(1)) ] ]  
  END

  RULE And
  { A & B }
  =========
    A ; B
  END

  RULE GE
     { G A }
  =============
   A ; X (G A)
  END
  
END

let exit (uev) = 
    match uev#elements with
    |[] -> "Open"
    |[(termfalse)] -> "Closed"
    |_ -> "Closed"
;;

PP := nnf
NEG := neg
EXIT := exit (uev(1))

let saturation = tactic ( (And ; Or ; Until ; Ge ; Before ; Id ; False)* )

STRATEGY ( ((saturation ; Next)* ; Loop)* )

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END
    
