
open Basictype

let not_marked = function
    `Formula ( Box (core,_) ) -> not(Basictype.is_marked core)
    | _ -> failwith "not_marked"
;;

let is_marked_list l = List.for_all not_marked l ;;

let mark = function
    `Formula Box (core,x) ->
        `Formula ( Box ( Basictype.mark core, x ) )
    | _ -> failwith "mark"
;;

let mark_list l = Basictype.map mark l ;;

let neg_term = function
    `Formula a -> `Formula ( Not (nc, a))
    | _ -> failwith "neg_term"
;;
let neg = List.map neg_term ;;

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
        
    | `Formula Dia (_, a1 ) ->
            let x = nnf_term ( `Formula a1 )
            in `Formula ( Dia (nc, Basictype.unbox x ) )
    | `Formula Not (_, Dia (_, a1 )) ->
            let x = nnf_term ( `Formula ( Not(nc, a1)) )
            in `Formula ( Box (nc, Basictype.unbox x ) )

    | `Formula Box (_, a1 ) ->
            let x = nnf_term ( `Formula a1 )
            in `Formula ( Box (nc, Basictype.unbox x ) )
    | `Formula Not (_, Box (_, a1 )) ->
            let x = nnf_term ( `Formula ( Not(nc, a1)) )
            in `Formula ( Dia (nc, Basictype.unbox x ) )

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
  Dia, "Dia_", Simple;
  Box, "Box_", Simple
END

TABLEAU

  RULE T 
     not_marked ({ Box A }) 
  ---------------------------
     A ; mark_list (Box A)
  END

  RULE K
  { Dia A } ; Box X ; Z
  =====================
    A ; X
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
    strategy#add "i2"    (R(new imp_rule))  "i2" "i3" ;
    strategy#add "i3"    (R(new t_rule))    "i3" "b" ;
    strategy#add "b"     (R(new id_rule))   "b" "s1";
    strategy#add "s1"    S                  "start" "d" ;
    strategy#add "d"     (R(new k_rule))    "d" "s2";
    strategy#add "s2"    S                  "start" "end" ;
    strategy#add "end"   E                  "end" "end"
;;

PP := nnf
NEG := neg

STRATEGY (A)
