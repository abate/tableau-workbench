
CONNECTIVES
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Falsum, Const
END


let rec nnf_term f =
    print_endline (Basictype.string_of_formula f);
    match f with
    | term ( a & b ) -> 
        let x = nnf_term a  
        and y = nnf_term b
        in term ( x & y )
        
    | term ( ~ ( a & b ) ) -> 
        let x = nnf_term term ( ~ a ) 
        and y = nnf_term term ( ~ b )
        in term ( x v y )

    | term ( a v b ) ->
            let x = nnf_term a
            and y = nnf_term b
            in term ( x v y )
            
    | term ( ~ ( a v b ) ) ->
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

    | term ( ~ ~ a ) -> nnf_term a

    | term ( ~ .a ) as f -> f
    | term ( .a ) as f -> f
 
    | f -> failwith ("nnf_term"^(Basictype.string_of_formula f))
;;


TABLEAU

  RULE Id
  { A } ; { ~ A }
  ===============
    Close
  END
  
  RULE False
     Falsum
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
 ===========
    ~ A | B
  END

  RULE DImp 
  { A <-> B }
 ===============
    A -> B | B -> A
  END

END

let neg_term = function term ( a ) -> term ( ~ a ) ;;

let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

PP := nnf
NEG := neg


(* STRATEGY ((Id; And; Or; Not)* ; K)* *)

let strategy = new Strategy.strategy "start";;
let _ =
    strategy#add "start" (R(new and_rule)) "start" "a" ;
    strategy#add "a" (R(new or_rule)) "a" "i1" ;
    strategy#add "i1" (R(new imp_rule)) "i1" "b" ;
(*    strategy#add "i2" (R(new dimp_rule)) "i2" "b" ; *)
    strategy#add "b" (R(new id_rule)) "end" "c";
    strategy#add "c" (R(new false_rule)) "end" "s2";
    strategy#add "s2" S "start" "end" ;
    strategy#add "end" E "end" "end" ;
;;

STRATEGY (A)
