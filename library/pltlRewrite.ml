
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Until, "_Un_", One;
  Before, "_Bf_", One;
  Not, "~_",   Simple;
  Next, "X_", Simple;
  Generally, "G_", Simple;
  Sometimes, "F_", Simple;
  Falsum, Const;
  Verum, Const
END

let rec nnf_term f = 
(*    print_endline (Basictype.string_of_formula f); *)
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

    |term ( ~ A ) as f -> f
    |term ( A ) as f -> f

    |term ( X a ) -> 
            let x = nnf_term a
            in term ( X x )
            
    |term ( ~ ( X a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( X x )
            
    |term ( ~ G a ) ->
            nnf_term term ( F ~ a )
    |term ( G a ) -> 
            let x = nnf_term term ( a )
            in term ( G x )

    |term ( ~ F a ) ->
            nnf_term term ( G ~ a )
    |term ( F a ) ->
            nnf_term term ( Verum Un a )

    |term ( ~ (a Bf b) ) ->
            nnf_term term ( (~ a) Un b )
    |term ( a Bf b ) ->
            let x = nnf_term term ( a )
            and y = nnf_term term ( b )
            in term ( x Bf y )

    |term ( ~ (a Un b) ) ->
            nnf_term term ( (~ a) Bf b )
    |term ( a Un b ) ->
            let x = nnf_term term ( a )
            and y = nnf_term term ( b )
            in term ( x Un y )

    |term ( ~ Falsum ) -> term ( Verum )
    |term ( ~ Verum ) -> term ( Falsum )

    |term ( Constant ) -> f
    |term ( ~ Constant ) -> f
    
    | _ -> failwith ("nnf_term"^(!Basictype.string_of_formula f))
;;

let neg_term = function term ( a ) -> term ( ~ a ) ;;
