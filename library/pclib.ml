
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Falsum, Const
END

let rec nnf_term f =
    match f with
    | term ( a & b ) -> 
        let x = nnf_term a  
        and y = nnf_term b
        in term ( x & y )
        
    | term ( ~ ( a & b ) ) -> 
        let x = nnf_term term ( ~ a ) 
        and y = nnf_term term ( ~ b )
        in term ( x v y )

    | term ( a v b ) ->
            let x = nnf_term a
            and y = nnf_term b
            in term ( x v y )
            
    | term ( ~ ( a v b ) ) ->
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

    | term ( ~ ~ a ) -> nnf_term a

    | term ( ~ A ) as f -> f
    | term ( A ) as f -> f
 
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
in conjnf (nnf_term t)
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

