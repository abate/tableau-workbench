
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_", Zero;
  Falsum, Const;
  Verum, Const
END

let neg = function term ( a ) -> term ( ~ a ) ;;

let rec nnf = function
    |term ( a & b ) -> term ( [nnf a] & [nnf b] )
    |term ( ~ ( a & b ) ) -> 
            term ( [ nnf term ( ~ a )] v [nnf term ( ~ b )] )

    |term ( a v b ) -> term ([nnf a] v [nnf b])
    |term ( ~ ( a v b ) ) ->
            term ( [ nnf term ( ~ a )] & [nnf term ( ~ b )] )

    |term ( a <-> b ) ->
            term ( [nnf term ( a -> b )] & [nnf term ( b -> a )] )
    |term ( ~ ( a <-> b ) ) ->
            term ( [nnf term ( ~ (a -> b) )] v [nnf term ( ~ (b -> a) )] )
            
    |term ( a -> b ) -> nnf term ( (~ a) v b )
    |term ( ~ (a -> b) ) -> nnf term ( a & (~ b) )
    |term ( ~ ~ a ) -> nnf a

    |term ( ~ Atom ) as f -> f
    |term ( Atom ) as f -> f
 
    |term (Verum) -> term (Verum)
    |term (Falsum) -> term (Falsum)
    |term (~ Verum) -> term (Falsum)
    |term (~ Falsum) -> term (Verum)

    |f -> failwith (Printf.sprintf "nnf:%s" (Twblib.sof(f)))
;;

let cnf t =
    let rec distr = function
        |term ( x v ( y & z ) ) ->
                term ([distr( term ( x v y) )] & [distr( term ( x v z) )])
        |x -> x
    in
    let rec distl = function
        |term ( ( y & z ) v x ) -> term ( [distl term (y v x)] & [distl term ( z v x ) ])
        |x -> x
    in
    let dist x = distr(distl x) 
    in
    let rec conjnf = function
        |term (t1 & t2) -> term ([conjnf(t1)] & [conjnf(t2)])
        |term (t1 v t2) -> dist (term ( [conjnf(t1)] v [conjnf(t2)]))
        |x -> x
in conjnf t
;;

let cnfl t =
    let i = ref 0 in
    let rec uniq = function
        |[] -> []
        |h::t -> h:: uniq (List.filter (fun x -> not(x = h)) t)
    in
    let rec lits = function
        |term ( A v B ) as t -> [t]
        |term ( A & B ) as t -> [t]
        |term ( ~ A v B ) as t -> [t]
        |term ( ~ A & B ) as t -> [t]
        |term ( A v ~ B ) as t -> [t]
        |term ( A & ~ B ) as t -> [t]

        |term ( a v b ) -> ( lits a ) @ (lits b )
        |term ( a & b ) -> ( lits a ) @ (lits b )
        |_ -> []
    in
    let rec aux t acc = function
        |hd::tl ->
                let j = incr i ; !i in
                let a = ( term (p(j) <-> hd ) ) in
                let b = term( t{p(j)/hd} ) in
                let acc' = term ( a & acc ) in
                aux b acc' tl
        |[] -> term (t & acc)
    in
    let t1 = cnf ( nnf t ) in
    aux t1 term ( Verum ) (uniq ( lits t1 ))
;;

(* formula list -> formula list *)
let listfy t =
    let rec split = function
        |term (a & b) -> split ( term (a) ) @ split ( term (b) )
        |_ as f -> [`Formula f]
    in
    match t with
    |[`Formula t] -> Basictype.open_bt_list (split (cnf t))
    |_ -> failwith "listfy"
;;

let rec simpl f = 
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
