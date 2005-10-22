
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
let not_empty = function [] -> false | _ -> true

let not_marked f = not(Basictype.is_marked_formula f) ;;
let is_marked_list l = List.for_all not_marked l ;;

let mark f = Basictype.mark_formula f
let mark_list l = Basictype.map mark l ;;

let neg_term = function
    | term ( a ) -> term ( ~ a )
    | _ -> failwith "neg_term"
;;

let rec nnf_term = function
    term ( a & b ) -> 
        let x = nnf_term a  
        and y = nnf_term b
        in term ( x & y )
        
    | term ( ~ ( a & b ) ) -> 
        let x = nnf_term ( term ( ~ a ) ) 
        and y = nnf_term ( term ( ~ b ) )
        in term ( x v y )

    | term ( a v b ) ->
            let x = nnf_term a
            and y = nnf_term b
            in term ( x v y )
            
    | term ( ~ ( a v b ) ) ->
            let x = nnf_term a
            and y = nnf_term b
            in term ( x & y )

    | term ( <i> a ) -> 
            let x = nnf_term a
            in term ( <i> x )
            
    | term ( ~ ( <i> a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( [i] x )
            
    | term ( [i] a ) -> 
            let x = nnf_term a
            in term ( [i] x )
            
    | term ( ~ ( [i] a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( <i> x )
            
    | term ( ~ ~ a ) -> a

    | term ( ~ a ) -> 
            let x = nnf_term a
            in term ( ~ x )

    | atm ( a ) as f -> f
 
    | _ -> failwith "nnf_term"
;;

(*
let neg = Basictype.map neg_term ;;

let nnf l = List.map (fun t -> nnf_term t) l ;;
*)


TABLEAU

  RULE S4 
  { <1> A } ; <1> Y ; Z
  ======================
  A ; BOXES || <1> Y 
  
  COND notin(<1> A, DIAMONDS)
  
  ACTION [
      [ DIAMONDS := add(<1> A,DIAMONDS);
        DIAMONDS := add(<1> Y,DIAMONDS) ]; [DIAMONDS := add(<1> A,DIAMONDS) ] ] 
  
  BRANCH [ not_empty(<1> Y) ] 
  END

  RULE TNEW
  { [1] A }
  =========
     A 

  COND notin([1] A, BOXES)
  
  ACTION [
      BOXES    := add([1] A,BOXES);
      DIAMONDS := emptyset (DIAMONDS) ]
  END

  RULE TOLD
  { [1] A }
  =========
     A 

  COND isin([1] A, BOXES)
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
  { A --> B }
 ============
    ~ A | B
  END

  RULE DImp 
  { A <--> B }
 ==================
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
    strategy#add "s2"    S                  "start" "meta" ;
    strategy#add "meta" (R(new defaultaxiom_rule)) "end" "end" ;
    strategy#add "end"   E                  "end" "end"
;;

(*
PP := nnf
NEG := neg
 *)

STRATEGY (A)
