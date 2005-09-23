
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
let notin (l,h) = h#mem (List.hd l)
let not_marked a = 
    match a with 
    <> A -> true
    | _ -> false
;;
let not_marked_list l = List.for_all not_marked l ;;
let mark a =
    match a with
    <> B -> @ <> B @
    | _ -> failwith "ddd"
;;
let mark_list l = Basictype.map mark l ;;
let print () s = print_endline s ;;

TABLEAU
  RULE K1
  { <1> A } ; [1] X; <1> Y ; Z
  -----------------------------
  A ; X || <1> Y ; [1] X

  BRANCH empty ( <1> Y )
  END

  RULE S4 
  { <1> A } ; [1] X; [1] Y ; Z
  -----------------------------
  A ; X || <1> Y ; [1] X
      
  COND notin(<1> A, DIAMONDS)
  
  ACTION [
      [ BOXES := add(<1> X,BOXES); 
        DIAMONDS := add(<1> A,DIAMONDS);
        DIAMONDS := add(<1> Y,DIAMONDS);
        print () "s4 down right" 
      ];
      [ DIAMONDS := add(<1> A,DIAMONDS);
        DIAMONDS := add(<1> Y,DIAMONDS);
        print () "s4 down left" 
      ]
  ] 
  
  BRANCH [ empty(<1> Y) ] 
  END

(*
  RULE K forall(i)
  { <i>A } ; [i]X ; Z
  =====================
    A ; X
  END
*)

  RULE T 
     not_marked ({ [1] A }) 
  ----------------------
     A ; mark_list([1] A)
  END

  RULE K
  { <1> A } ; [1] X ; Z
  =====================
    A ; X

    ACTION [ print () "K down" ]
  END
 
  RULE Id
  { A } ; { ~ A }
  ---------------
    Close

    ACTION [ print () "ID down" ]
  END
  
  RULE AntiId
  { .a } ; .z 
  ------------
    Open
  END

  RULE And
  { A & B }
 ------------
    A ; B
    
    ACTION [ print () "And down" ]
  END
  
  RULE Or
  { A v B }
 ------------
    A | B

    ACTION [ [ print () "Or down right" ]; [print () "Or down left"] ]
  END

  RULE Imp 
  { A --> B }
 ------------
    ~ A | B

    ACTION [ [ print () "Imp down right" ]; [print () "Imp down left"] ]
  END

  RULE DImp 
  { A <--> B }
 -------------------
  A --> B | B --> A
  END

END

(* STRATEGY ((Id; And; Or; Not)* ; K)* *)

let strategy = new Strategy.strategy "start";;
let _ = 
    strategy#add "start" (R(new and_rule))  "start" "a" ;
    strategy#add "a"     (R(new or_rule))   "a" "i1" ;
    strategy#add "i1"    (R(new imp_rule))  "i1" "i2" ;
    strategy#add "i2"    (R(new dimp_rule)) "i2" "b" ;
    strategy#add "b"     (R(new id_rule))   "b" "s1";
    strategy#add "s1"    S                  "a" "d" ;
    strategy#add "d"     (R(new k_rule))    "d" "s2";
    strategy#add "s2"    S                  "start" "end" ;
    strategy#add "end"   E                  "end" "end"
;;

STRATEGY (A)
