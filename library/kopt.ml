
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_",   Zero;
  Box, "Box_", Zero;
  Dia, "Dia_", Zero;
  Falsum, Const;
  Verum, Const
END

let neg = function term ( a ) -> term ( ~ a ) ;;

let rec boolean t = 
    let aux = function
        |term (a & b) when a = b -> a
        |term (a v b) when a = b -> a
        |term (Verum & b)  |term (b & Verum)  -> b
        |term (Falsum & b) |term (b & Falsum) -> term (Falsum)
        |term (Verum v b)  |term (b v Verum)  -> term (Verum)
        |term (Falsum v b) |term (b v Falsum) -> b
        |term (Dia Falsum) -> term (Falsum)
        |term (Box Falsum) -> term (Falsum)
        |term (~ Verum)  -> term (Falsum)
        |term (~ Falsum) -> term (Verum)
        |a -> a
    in match t with
    |term (a & b) -> aux term ( [boolean (aux a)] & [boolean (aux b)] )
    |term (a v b) -> aux term ( [boolean (aux a)] v [boolean (aux b)] )
    |term (Dia a) -> aux term ( Dia [boolean (aux a)] )
    |term (Box a) -> aux term ( Box [boolean (aux a)] )
    |term (~ a)   -> aux term ( ~ [boolean (aux a)] )
    |a -> aux a
;;

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
    in let (_,f') = aux f in boolean f'
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

let rec simpl phi a =
(*    Printf.printf "Simplification ! %s[%s]\n" (Twblib.sof(a)) (Twblib.sof(phi)); *)
    let rec aux phi a = match a with
        |term (~ b) when b = a -> term(Falsum) 
        |term (~ b)   -> term ( ~ [aux phi b] )
        |term (b & c) -> term ( [aux phi b] & [aux phi c] )
        |term (b v c) -> term ( [aux phi b] v [aux phi c] )
        |term (Box b) ->
                begin match phi with
                |term (Box phi') -> term ( Box [aux phi' b] )
                |_ -> a
                end
        |term (Dia b) ->
                begin match phi with
                |term (Box phi') -> term ( Dia [aux phi' b] )
                |_ -> a
                end
        |_ when phi = a -> term(Verum)
        |_ when phi = (nnf (term ( ~ a ))) -> term(Falsum)
        |_ -> a
    in
    let r = boolean (aux phi a) in
(*    Printf.printf "Result: %s\n\n" (Twblib.sof(r)) ;  *)
    r
;;

