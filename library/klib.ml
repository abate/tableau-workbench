
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Zero;
  Box, "Box_", Zero;
  Dia, "Dia_", Zero;
  Falsum, Const;
  Verum, Const
END

let neg = function term ( a ) -> term ( ~ a ) ;;

let rec nnf f = 
    match f with
    |term ( a & b ) -> term ( [nnf a] & [nnf b] )
    |term ( ~ ( a & b ) ) ->
            term ( [nnf term ( ~ a )] v [nnf term ( ~ b )] )

    |term ( a v b ) ->
            term ( [nnf a] v [nnf b] )
    |term ( ~ ( a v b ) ) ->
            term ( [nnf term ( ~ a )] & [nnf term ( ~ b )] )

    |term ( a <-> b ) ->
            term ( [nnf term ( a -> b )] & [nnf term ( b -> a )] )
    |term ( ~ ( a <-> b ) ) ->
            term ( [nnf term ( ~ (a -> b) )] v [nnf term ( ~ (b -> a) )] )

    |term ( a -> b ) -> nnf term ( (~ a) v b )
    |term ( ~ (a -> b) ) -> nnf term ( a & (~ b) )

    |term ( ~ ~ a ) -> nnf a

    |term ( ~ Atom ) as f -> f
    |term ( Atom ) as f -> f

    |term ( Dia a ) -> term ( Dia [nnf a] )
            
    |term ( ~ ( Dia a ) ) -> term ( Box [nnf ( term ( ~ a ) )] )
            
    |term ( Box a ) -> term ( Box [nnf a] )
            
    |term ( ~ ( Box a ) ) -> term ( Dia [nnf ( term ( ~ a ) )] )

    |term ( ~ Falsum ) -> term ( Verum )
    |term ( ~ Verum ) -> term ( Falsum )

    |term ( Constant ) -> f
    |term ( ~ Constant ) -> f

    |f -> failwith (Printf.sprintf "%s\n" (Twblib.sof(f)))
;;

let rec cnf t =
    let rec distrib = function
        |t1, term ( t2 & t3 ) -> term ([distrib(t1,t2)] & [distrib(t1,t3)])
        |term (t1 & t2), t3 -> term ([distrib(t1,t3)] & [distrib(t2,t3)])
        |t1,t2 -> term (t1 v t2)
    in
    let rec conjnf t =
        match t with
        |term (t1 & t2) -> term ([conjnf(t1)] & [conjnf(t2)])
        |term (t1 v t2) -> distrib (conjnf(t1),conjnf(t2))
        |term (Box t1) -> term ( Box [cnf t1] )
        |term (Dia t1) -> term ( Dia [cnf t1] )
        |_ -> t
in conjnf t
;;

