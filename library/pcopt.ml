
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_", Zero;
  Falsum, Const;
  Verum, Const
END

(* workd if f is in nnf *)
let rec weigth = function
    |term ( a & b ) -> (weigth a) * (weigth b) 
    |term ( a v b ) -> 1 + (weigth a) + (weigth b) 
    |_ -> 0
;;

let cmp a b = compare (weigth a) (weigth b) ;;

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
        let d = 1 + d1 + d2 in
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

let rec simpl phi a =
    if phi = a then term(Verum)
    else if phi = (nnf (term ( ~ a ))) then term(Falsum)
    else match a with
    |term (~ b)   -> term ( ~ [simpl phi b] )
    |term (b & c) -> term ( [simpl phi b] & [simpl phi c] )
    |term (b v c) -> term ( [simpl phi b] v [simpl phi c] )
    |_ -> a
;;

