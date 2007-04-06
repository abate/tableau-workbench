
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Zero;
  Dia1, "Dia1_", Zero;
  Box1, "Box1_", Zero;
  Dia2, "Dia2_", Zero;
  Box2, "Box2_", Zero;
  CDia, "dC_", Zero;
  CBox, "C_", Zero;
  EDia, "dE_", Zero;
  EBox, "E_", Zero;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  (Fev : Set of Formula := new Set.set) ;
  (Br  : List of ( Set of Formula * Set of Formula ) := new Listoftupleset.listobj) ;
  (uev : Set of ( Formula * Int ) := new Setoftermint.set) ;
  (fev : Set of ( Formula * Int ) := new Setoftermint.set) ;
  (status : String := new Set.set)
END

open Twblib
open LckRewrite
open LckFunctions

let notemptylist (d1,d2) = not(List.length (d1@d2) = 0)

TABLEAU

  RULE Id
  { a } ; { ~ a } == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END
  
  RULE False
  Falsum ; z == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END

  RULE CDia
      { dC p }
  ===================
   dE p ||| dE dC p

  ACTION [ [ Fev := add(dC P,Fev) ] ; [] ]
  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ]
  END

  RULE EDia
      {  dE p }
  ===================
   Dia1 p ||| Dia2 p

  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END

  RULE Diaone
  { Dia1 p } ; Box1 x ; Dia1 q1 ; Dia2 q2 ; z
  =============================
      p ; x ||| Box1 x ; Dia1 q1 ; Dia2 q2 ; z
      
  COND [ loop_check(p, x, Br) ]
  ACTION [ [
      Fev := emptyset(Fev);
      Br  := push(p, x, Fev, Br)
  ] ; [] ]
  BRANCH [ [ not_false(uev@1) ; notemptylist(Dia1 q1, Dia2 q2) ] ]
  BACKTRACK [ uev := setuev_pi(uev@1, uev@2, Br) ]
  END (cache)

  RULE Diatwo
  { Dia2 p } ; Box2 x ; Dia1 q1 ; Dia2 q2 ; z
  ==================================
      p ; x ||| Box2 x ; Dia1 q1 ; Dia2 q2 ; z
      
  COND [ loop_check(p, x, Br) ]
  ACTION [ [
      Fev := emptyset(Fev);
      Br  := push(p,x, Fev, Br)
  ] ; [] ]
  BRANCH [ [ not_false(uev@1) ; notemptylist(Dia1 q1, Dia2 q2) ] ]
  BACKTRACK [ uev := setuev_pi(uev@1, uev@2, Br) ]
  END (cache)
  
  RULE Loop Dia1 x1 ; Dia2 x2 ; Box1 y1 ; Box2 y2 == Stop
  BACKTRACK [ uev := setuev_loop(x1, y1, x2, y2, Fev, Br) ]
  END

  RULE Or
  { a v b }
  =========
   a ||| b

  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END

  RULE And a & b == a ; b END
  RULE EBox E p == Box1 p ; Box2 p END
  RULE CBox C p == E p ; E C p END
  
END

let exit (uev) =
    match uev#elements with
    |[] -> "Open"
    |(termfalse,_)::[] -> "Closed"
    |_ -> "Closed"
;;

PP := nnf_term
NEG := neg_term
EXIT := exit (uev@1)

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END

let saturation = tactic ( (Id| And| Or| Edia| Cbox| Ebox| Cdia| False) )

let modal = tactic ( (saturation)* ; (Diaone | Diatwo | Loop) )

STRATEGY ( (modal)* )
