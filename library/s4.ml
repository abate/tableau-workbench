

open Basictype

let not_marked f = not(Basictype.is_marked_formula f) ;;
let is_marked_list l = List.for_all not_marked l ;;

let mark f = Basictype.mark_formula f
let mark_list l = Basictype.map mark l ;;

let neg_term = function
    `Formula a -> `Formula ( Not (nc, a))
    | _ -> failwith "neg_term"
;;
let neg = Basictype.map neg_term ;;

let rec nnf_term = function
    `Formula ( And (_, a1, a2) ) -> 
        let x = nnf_term ( `Formula a1 ) 
        and y = nnf_term ( `Formula a2 )
        in `Formula ( And ( nc , Basictype.unbox x, Basictype.unbox y ) )
        
    | `Formula Not (_, And (_, a1, a2) ) ->
        let x = nnf_term ( `Formula ( Not (nc ,a1)) )
        and y = nnf_term ( `Formula ( Not (nc ,a2)) )
        in `Formula ( Or ( nc , Basictype.unbox x, Basictype.unbox y ) )

    | `Formula ( Or (_, a1, a2) ) -> 
        let x = nnf_term ( `Formula a1 ) 
        and y = nnf_term ( `Formula a2 )
        in `Formula ( Or ( nc , Basictype.unbox x, Basictype.unbox y ) )
    | `Formula Not (_, Or (_, a1, a2) ) ->
        let x = nnf_term ( `Formula ( Not (nc ,a1)) )
        and y = nnf_term ( `Formula ( Not (nc ,a2)) )
        in `Formula ( And ( nc , Basictype.unbox x, Basictype.unbox y ) )
        
    | `Formula Diai (i, _, a1 ) ->
            let x = nnf_term ( `Formula a1 )
            in `Formula ( Diai (i, nc, Basictype.unbox x ) )
    | `Formula Not (_, Diai (i, _, a1 )) ->
            let x = nnf_term ( `Formula ( Not(nc, a1)) )
            in `Formula ( Boxi (i, nc, Basictype.unbox x ) )

    | `Formula Boxi (i,_, a1 ) ->
            let x = nnf_term ( `Formula a1 )
            in `Formula ( Boxi (i, nc, Basictype.unbox x ) )
    | `Formula Not (_, Boxi (i, _, a1 )) ->
            let x = nnf_term ( `Formula ( Not(nc, a1)) )
            in `Formula ( Diai (i, nc, Basictype.unbox x ) )

    | `Formula Not (_, Not (_, a1) ) ->
        let x = nnf_term ( `Formula a1 )
        in `Formula (Basictype.unbox x)
    | `Formula ( Not (_, a1) ) ->
        let x = nnf_term ( `Formula a1 )
        in `Formula ( Not ( nc, Basictype.unbox x ) )

    | `Formula Atom(_, _) as f -> f
 
    | _ -> failwith "nnf_term"
;;

let nnf l = List.map (fun t -> nnf_term t) l ;;



CONNECTIVES
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_-->_", One;
  DImp, "_<-->_", One;
  Not, "~_",   Simple;
  Dia, "<>_", Simple;
 (*  Box, "[]_", Simple; doesn't work *)
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

TABLEAU
  RULE S4 
  { <1> A } ; <1> Y ; Z
  -----------------------
  A ; BOXES || <1> Y 
  
  COND notin(<1> A, DIAMONDS)
  
  ACTION [
      [ DIAMONDS := add(<1> A,DIAMONDS);
        DIAMONDS := add(<1> Y,DIAMONDS) ];
        
      [ DIAMONDS := add(<1> A,DIAMONDS) ]
  ] 
  
  BRANCH [ empty(<1> Y) ] 
  END

  RULE TNEW
  { [1] A }
  ---------
     A 

     COND notin([1] A, BOXES)
     
     ACTION [
         BOXES    := add([1] A,BOXES);
         DIAMONDS := emptyset (DIAMONDS) ]
  END

  RULE TOLD
  { [1] A }
  ---------
     A 

     COND isin([1] A, BOXES)
  END

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
  { A --> B }
 ------------
    ~ A | B
  END

  RULE DImp 
  { A <--> B }
 -------------------
  A --> B | B --> A
  END

END

let strategy = new Strategy.strategy "start";;
let _ = 
    strategy#add "start" (R(new and_rule))  "start" "a" ;
    strategy#add "a"     (R(new or_rule))   "a" "i1" ;
    strategy#add "i1"    (R(new imp_rule))  "i1" "i2" ;
    strategy#add "i2"    (R(new dimp_rule)) "i2" "i3" ;
    strategy#add "i3"    (R(new tnew_rule)) "i3" "i4" ;
    strategy#add "i4"    (R(new told_rule)) "i4" "b" ;
    strategy#add "b"     (R(new id_rule))   "b" "s1";
    strategy#add "s1"    S                  "start" "d" ;
    strategy#add "d"     (R(new s4_rule))   "d" "s2";
    strategy#add "s2"    S                  "start" "end" ;
    strategy#add "end"   E                  "end" "end"
;;

PP := nnf
NEG := neg

STRATEGY (A)
