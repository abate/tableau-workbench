
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  ExX, "ExX_", One;
  AxX, "AxX_", One;
  ExG, "ExG_", One;
  ExF, "ExF_", One;
  AxG, "AxG_", One;
  AxF, "AxF_", One;
  Not, "~_",   Zero;
  Star, "*_",   Zero;
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

open UbFunctions
open UbRewrite

TABLEAU

  RULE Id
  { a } ; { ~ a } == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END
  
  RULE False
  Falsum == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END

  RULE Axf
      { AxF p }
  ===================
   p ||| AxX AxF p 

  ACTION [ [ Fev := add(AxF p, Fev) ]; [] ]
  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ]
  END

  RULE Exf
      { ExF p }
  ===================
   p ||| ExX ExF p 

  ACTION [ [ Fev := add(ExF p, Fev) ] ; [] ]
  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END 

  RULE Exx
  { ExX p } ; ExX s ; AxX y ; z
  =============================
      p ; y ||| ExX s ; AxX y
      
  COND [ loop_check(p, y, Br) ]
  ACTION [ [
      Br  := push(p, y, Fev, Br); 
      Fev := emptyset(Fev)
  ] ; [] ] 
  BRANCH [ [ not_false(uev@1) ; not_empty_list(ExX s) ] ]
  BACKTRACK [ uev := setuev_pi(uev@1, uev@2, Br) ]
  END (CACHE)

  RULE Ref
  ExX x ; {AxX p} == ExX Verum ; AxX p
  COND [ is_empty_list(ExX x) ]
  END

  RULE Loop
  ExX x ; AxX y == Stop
  COND [ not_empty_list(ExX x) ]
  BACKTRACK [ uev := setuev_loop(x, y, Fev, Br) ]
  END

  RULE Or
  { a v b }
  =========
   a ||| b

  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END

  RULE And a & b == a ; b END
  RULE Axg AxG p == p ; AxX AxG p END
  RULE Exg ExG p == p ; ExX ExG p END

END

let exit (uev) =
    match uev#elements with
    |(termfalse,_)::[] -> "Closed"
    |[] -> "Open"
    |_ -> "Closed"
;;

PP := nnf_term
NEG := neg_term
EXIT := exit (uev@1)

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END

let saturation = tactic ( (Id | False | And | Axg | Exg | Or | Axf | Exf )* )

let modal = tactic ( ( saturation | Ref | Exx )* )

STRATEGY ( (modal | Loop)* )
