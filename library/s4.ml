
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Dia, "Dia_", Simple;
  Box, "Box_", Simple;
  Boxi, "[_]_", Simple;
  Diai, "<_>_", Simple
END

HISTORIES
  DIAMONDS : Set.set;
  BOXES : Set.set
END

let add (l,h) = h#addlist l
let notin (l,h) = not(h#mem (List.hd l))
let isin (l,h) = h#mem (List.hd l)
let emptyset h = h#empty
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

    | term ( Dia a ) -> 
            let x = nnf_term a
            in term ( Dia x )
            
    | term ( ~ ( Dia a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( Box x )
            
    | term ( Box a ) -> 
            let x = nnf_term a
            in term ( Box x )
            
    | term ( ~ ( Box a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( Dia x )
            
    | _ -> failwith "nnf_term"
;;

let not_marked f = not(Basictype.is_marked_formula f) ;;
let is_marked_list l = List.for_all not_marked l ;;
let mark f = Basictype.mark_formula f ;;
let mark_list l = Basictype.map mark l ;;

let neg_term = function term ( a ) -> term ( ~ a ) ;;
let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

TABLEAU

  RULE S4 
  { Dia A } ; Dia Y ; Z
  =====================
  A ; BOXES || Dia Y 
  
  COND notin(Dia A, DIAMONDS)
  
  ACTION [
      [ DIAMONDS := add(Dia A,DIAMONDS);
        DIAMONDS := add(Dia Y,DIAMONDS) ]; [DIAMONDS := add(Dia A,DIAMONDS) ] ] 
  
  BRANCH [ not_empty(Dia Y) ] 
  END

  RULE S4IMP
  { Dia A } ; Z
  ----------------------
  A ; BOXES 
  
  COND notin(Dia A, DIAMONDS)
  ACTION [ DIAMONDS := add(Dia A,DIAMONDS) ]
  END

  RULE TNEW
  { Box A }
  =========
     A 

  COND notin(A, BOXES)
  
  ACTION [
      BOXES    := add(A,BOXES);
      DIAMONDS := emptyset (DIAMONDS) ]
  END

  RULE TOLD
  { Box A }
  =========
     A 

  COND isin(A, BOXES)
  END
  
  RULE Id
  { A } ; { ~ A }
  ===============
    Close
  END
  
  RULE And
  { A & B }
  =========
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

let saturation = tactic ( (And;Or;Imp;Dimp;Tnew;Told;Id)* )

STRATEGY ( saturation ; S4imp )*
