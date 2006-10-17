CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  ExX, "ExX_", One;
  AxX, "AxX_", One;
  ExG, "ExG_", One;
  ExF, "ExF_", One;
  AxG, "AxG_", One;
  AxF, "AxF_", One;
  Not, "~_",   Zero;
  Falsum, Const;
  Verum, Const
END

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

    |term ( ~ Atom ) as f -> f
    |term ( Atom ) as f -> f

    |term ( AxX a ) -> 
            let x = nnf_term a
            in term ( AxX x )
            
    |term ( ~ ( AxX a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( ExX x )

    |term ( ExX a ) -> 
            let x = nnf_term a
            in term ( ExX x )
            
    |term ( ~ ( ExX a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( AxX x )
            
    |term ( ~ AxG a ) ->
            nnf_term term ( ExF ~ a )
            
    |term ( ~ ExG a ) ->
            nnf_term term ( AxF ~ a )
 
    |term ( AxG a ) -> 
            let x = nnf_term term ( a )
            in term ( AxG x )

    |term ( ExG a ) -> 
            let x = nnf_term term ( a )
            in term ( ExG x )

    |term ( ~ ExF a ) -> 
            let x = nnf_term term ( ~ a )
            in term ( AxG x )

    |term ( ~ AxF a ) -> 
            let x = nnf_term term ( ~ a )
            in term ( ExG x )

    |term ( ExF a ) -> 
            let x = nnf_term term ( a )
            in term ( ExF x )

    |term ( AxF a ) -> 
            let x = nnf_term term ( a )
            in term ( AxF x )

    |term ( ~ Falsum ) -> term ( Verum )
    |term ( ~ Verum ) -> term ( Falsum )

    |term ( Constant ) -> f
    |term ( ~ Constant ) -> f
    
    | _ -> failwith ("nnf_term "^(!Basictype.string_of_formula f))
;;

let neg_term = function term ( a ) -> term ( ~ a ) ;;
(*let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;
*)
