
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Until, "_Un_", One;
  Before, "_Bf_", One;
  Next, "X_", Zero;
  Generally, "G_", Zero;
  Sometimes, "F_", Zero;
  Not, "~_",   Zero;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  (Ev : Set of Formula := new Set.set) ;
  (Br : List of (Set of Formula * Set of Formula) := new Listoftupleset.listobj);
  (uev : Set of Formula := new Set.set);
  (status : String := new Set.set);
  (n : Int := new Set.set default 0)
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

  END (CACHE)

  RULE Before
    {a Bf c}
  ==========================
   nnf (~ c) ; a v X (a Bf c)

  END

  RULE Until
           { c Un d } 
  =============================
      d ||| c ; X ( c Un d ) 

  ACTION    [ Ev := add(d, Ev) ] 
  BRANCH    [ not_emptyset(uev@1) ] 
  BACKTRACK [ 
      uev := beta(uev@1, uev@2, n@1, n@2, Br);
      n := min (n@1, n@2)
  ]
    
  END
 
  RULE Or
  { a v b }
  =========
   a ||| b

  BRANCH [ not_emptyset(uev@1) ]  
  BACKTRACK [ 
      uev := beta(uev@1, uev@2, n@1, n@2, Br);
      n := min (n@1 , n@2)
  ]

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

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END
 
PP := nnf_term
NEG := neg_term
EXIT := exit (uev@1)

let sat = tactic ( (Id | False | And | Before | Ge | Or | Until) )

STRATEGY := (((sat)* ; (Next | Loop))* )
