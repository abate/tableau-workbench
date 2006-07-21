
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

let neg_term = function term ( a ) -> term ( ~ a ) ;;

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
