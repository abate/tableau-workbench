
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
  { a } ; { ~ a } ; z
  ===============
     Stop

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END
  
  RULE False
  Falsum ; z
  ===============
     Stop

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END

  RULE Loop
  { X a } ; X b ; z
  =================
       Stop

  BACKTRACK [
      uev := setuev(X a, X b, z, Ev, Br);
      n   := setn (X a, X b, z, Br)
  ]

  END

  RULE Next
  { X a } ; X b ; z
  =================
      a ; b
      
  COND [ loop_check(X a, X b, z, Br) ]
  ACTION [
      Ev := emptyset(Ev);
      Br := push(X a, X b, z, Ev, Br)
  ]

  END

  RULE Before
    {a Bf c}
  ==========================
   nnf (~ c) ; a v X (a Bf c)

  END

  RULE Until
           { c Un d } 
  =============================
      d ||| c ; X ( c Un d ) 

  ACTION    [ [ Ev := add(d, Ev) ] ; [] ]
  BACKTRACK [ 
      uev := beta(uev(1), uev(2), n(1), n(2), Br);
      n := min (n(1), n(2))
  ]
  BRANCH    [ [ not_emptyset(uev(1)) ] ] 
    
  END
 
  RULE Or
  { a v b }
  =========
   a ||| b

  BACKTRACK [ 
      uev := beta(uev(1), uev(2), n(1), n(2), Br);
      n := min (n(1) , n(2))
  ]

  BRANCH [ [ not_emptyset(uev(1)) ] ]  
  END

  RULE And
    a & b 
  =========
    a ; b
  END

  RULE GE
     { G a }
  =============
   a ; X (G a)
  END
  
END

let exit (uev) = 
    match uev#elements with
    |[] -> "Open"
    |[(termfalse)] -> "Closed"
    |_ -> "Closed"
;;

PP := nnf_term
NEG := neg_term
EXIT := exit (uev(1))

let saturation = tactic ( (And ; Or ; Until ; Ge ; Before ; Id ; False)* )

STRATEGY ( ((saturation ; Next)* ; Loop)* )

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END
    
