
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Box, "Box_", Simple;
  Dia, "<>_", Simple;
  Falsum, Const;
  Verum, Const
END

let not_empty = function [] -> false | _ -> true

let rec nnf_term f = 
    match f with
    |term ( a & b ) ->
        let x = nnf_term a
        and y = nnf_term b
        in term ( x & y )

    |term ( ~ ( a & b ) ) ->
        let x = nnf_term term ( ~ a )
        and y = nnf_term term ( ~ b )
        in term ( x v y )

    |term ( a v b ) ->
            let x = nnf_term a
            and y = nnf_term b
            in term ( x v y )

    |term ( ~ ( a v b ) ) ->
            let x = nnf_term term ( ~ a )
            and y = nnf_term term ( ~ b )
            in term ( x & y )

    |term ( a <-> b ) ->
            let x = nnf_term term ( a -> b )
            and y = nnf_term term ( b -> a )
            in term ( x & y )

    |term ( ~ ( a <-> b ) ) ->
            let x = nnf_term term ( ~ (a -> b) )
            and y = nnf_term term ( ~ (b -> a) )
            in term ( x v y )

    |term ( a -> b ) ->
            nnf_term term ( (~ a) v b )

    |term ( ~ (a -> b) ) ->
            nnf_term term ( a & (~ b) )

    |term ( ~ ~ a ) -> nnf_term a

    |term ( ~ .a ) as f -> f
    |term ( .a ) as f -> f

    |term ( <> a ) -> 
            let x = nnf_term a
            in term ( <> x )
            
    |term ( ~ ( <> a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( Box x )
            
    |term ( Box a ) -> 
            let x = nnf_term a
            in term ( Box x )
            
    |term ( ~ ( Box a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( <> x )

    |term ( ~ Falsum ) -> term ( Verum )
    |term ( ~ Verum ) -> term ( Falsum )

    |term ( Constant ) -> f
    |term ( ~ Constant ) -> f

    | _ -> failwith ("nnf_term"^(!Basictype.string_of_formula f))
;;

let neg_term = function term ( a ) -> term ( ~ a ) ;;
let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;
let always () = true ;;
TABLEAU

  RULE K1
  { <> A } ; Box X ; <> Y ; Z
  ===========================
      A ; X || <> Y ; Box X

  BRANCH [ not_empty(<> Y) ]
  END

  RULE K
  { <> A } ; Box X ; Z
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
  { A -> B }
 ============
    ~ A | B
  END

  RULE DImp 
  { A <-> B }
 ==================
  A -> B | B -> A
  END

END

PP := nnf
NEG := neg

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
    strategy#add "end"   E__                "end" "end"
;;

STRATEGY (A)
