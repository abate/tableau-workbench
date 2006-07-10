
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Box, "Box_", Simple;
  Dia, "Dia_", Simple;
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

    |term ( Dia a ) -> 
            let x = nnf_term a
            in term ( Dia x )
            
    |term ( ~ ( Dia a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( Box x )
            
    |term ( Box a ) -> 
            let x = nnf_term a
            in term ( Box x )
            
    |term ( ~ ( Box a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( Dia x )

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
  { Dia A } ; Box X ; Dia Y ; Z
  ===========================
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

let t = tactic ( (Id;And;Or)* )

STRATEGY ( t ; K )*

