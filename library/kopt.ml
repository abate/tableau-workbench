
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

let nnf f =
    let rec aux = function
        |term ( a & b ) as f -> Pcopt.order aux f
        |term ( ~ ( a & b ) ) -> aux term ( ~ a  v ~ b )
        |term ( a v b ) as f -> Pcopt.order aux f
        |term ( ~ ( a v b ) ) -> aux term ( ~ a & ~ b )
        |term ( a <-> b ) ->
                aux term ( ( a -> b ) & ( b -> a ) )
        |term ( ~ ( a <-> b ) ) ->
                aux term ( ( ~ (a -> b) ) v ( ~ (b -> a) ) )
        |term ( a -> b ) -> aux term ( (~ a) v b )
        |term ( ~ (a -> b) ) -> aux term ( a & (~ b) )
        |term ( ~ ~ a ) -> aux a
        |term ( ~ Atom ) as f -> (0,f)
        |term ( Atom ) as f   -> (0,f)
        |term ( Constant ) as f -> (0,f)
        |term (~ Constant) as f -> (0,f)

        |term ( Dia a ) -> let (d,t) = aux a in (d,term ( Dia t ))
        |term ( ~ ( Dia a ) ) -> aux term ( Box ~ a )
        |term ( Box a ) -> let (d,t) = aux a in (d,term ( Box t ))
        |term ( ~ ( Box a ) ) -> aux term ( Dia ~ a )

        |f -> failwith (Printf.sprintf "aux:%s" (Twblib.sof(f)))
    in let (_,f') = aux f in f'
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

let naive_simpl = Pcopt.simpl 

let rec simpl s f t =
    match f,t with
    |_,_ when f = t -> s
    |_, term (~ b) when s = term (Verum) ->
            simpl term (Falsum) f b
    |_, term (~ b) when s = term (Falsum) ->
            simpl term (Verum) f b
    |term (~ a),_     ->
            (match naive_simpl (simpl s a t) with
            |term (Verum)  -> term (Falsum)
            |term (Falsum) -> term (Verum)
            |_  -> f
            )
    |term (a & b),_ ->
            let x = simpl s a t
            and y = simpl s b t
            in
            naive_simpl (term (x & y))
    |term (a v b),_ ->
            let x = simpl s a t
            and y = simpl s b t
            in
            naive_simpl (term (x v y))
    |term (Dia a), term (Dia a') when s = term (Falsum) ->
            let x = simpl s a a'
            in
            naive_simpl (term (Dia x))
    |term (Dia a), term (Box a') when s = term (Verum) ->
            let x = simpl s a a'
            in
            naive_simpl (term (Dia x))
    |term (Box a), term (Box a') when s = term (Verum) ->
            let x = simpl s a a'
            in
            naive_simpl (term (Box x))
    |term (Box a), term (Dia a') when s = term (Falsum) ->
            let x = simpl s a a'
            in
            naive_simpl (term (Box x))
    |_,_ -> f
;;

