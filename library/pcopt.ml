
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_", Zero;
  Falsum, Const;
  Verum, Const
END

let rec order aux = function
    |term ( a & b ) -> 
        let (d1,t1) = aux a in
        let (d2,t2) = aux b in
        let d = d1 * d2 in
        begin match compare d1 d2 with
        |1 -> d, term ( t2 & t1 )
        |0 ->
                if compare a b < 0 
                then d, term ( t1 & t2 ) 
                else d, term ( t2 & t1 )
        |_ -> d, term ( t1 & t2 )
        end
    |term ( a v b ) -> 
        let (d1,t1) = aux a in
        let (d2,t2) = aux b in
        let d = d1 + d2 in
        begin match compare d1 d2 with
        |1 -> d, term ( t2 v t1 )
        |0 ->
                if compare a b < 0
                then d, term ( t1 v t2 )
                else d, term ( t2 v t1 )
        |_ -> d, term ( t1 v t2 )
        end
    |_ -> failwith "order"

;;

let nnf f =
    let rec aux = function
        |term ( a & b ) as f -> order aux f
        |term ( ~ ( a & b ) ) -> aux term ( ~ a  v ~ b )
        |term ( a v b ) as f -> order aux f
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
        |f -> failwith (Printf.sprintf "aux:%s" (Twblib.sof(f)))
    in let (_,f') = aux f in f'
;;

let rec simpl f =
(*    Printf.printf "simpl:%s\n" (Twblib.sof(f)); *)
    match f with
    |term (~ Falsum)    -> term (Verum)
    |term (~ Verum)     -> term (Falsum)
    |term (a & Falsum)  -> term (Falsum)
    |term (Falsum & a)  -> term (Falsum)
    |term (a v Verum)   -> term (Verum)
    |term (Verum v a)   -> term (Verum)

    |term (a & Verum)   -> simpl a
    |term (Verum & a)   -> simpl a
    |term (a v Falsum)  -> simpl a
    |term (Falsum v a)  -> simpl a

    |term (a & b) ->
            (match simpl a with
            |term (Falsum) -> term (Falsum)
            |_ as sx ->
                    (match simpl b with
                    |term (Falsum) -> term (Falsum)
                    |_ as sy ->
                            if sx = sy then sx
                            else term (sx & sy) )
            )
    |term (a v b) ->
            (match simpl a with
            |term (Verum) -> term (Verum)
            |_ as sx ->
                    (match simpl b with
                    |term (Verum) -> term (Verum)
                    |_ as sy ->
                            if sx = sy then sx
                            else term (a v b) )
            )
    |_ as f -> f
;;
