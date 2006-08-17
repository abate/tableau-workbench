
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Falsum, Const;
  Verum, Const
END

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

    |term ( ~ A ) as f -> f
    |term ( A ) as f -> f
 
    |term (Verum) -> term (Verum)
    |term (Falsum) -> term (Falsum)
    |term (~ Verum) -> term (Falsum)
    |term (~ Falsum) -> term (Verum)

    | f -> failwith (Printf.sprintf "%s\n" (Twblib.sof(f)))
;;

let cnf t =
    let rec distrib = function
        |t1, term ( t2 & t3 ) ->
                let a = distrib(t1,t2)
                and b = distrib(t1,t3)
                in term ( a & b )
        |term (t1 & t2), t3 ->
                let a = distrib(t1,t3)
                and b = distrib(t2,t3)
                in term (a & b)
        |t1,t2 -> term (t1 v t2)
    in
    let rec conjnf t =
        match t with
        | term (t1 & t2) ->
                let a = conjnf(t1)
                and b = conjnf(t2)
                in term (a & b)
        | term (t1 v t2) -> distrib (conjnf(t1),conjnf(t2))
        | _ -> t
in conjnf (nnf t)
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

let neg_term = function term ( a ) -> term ( ~ a ) ;;
let nnf_term = nnf

