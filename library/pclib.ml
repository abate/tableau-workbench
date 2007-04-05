
source Pc

let neg = function formula ( a ) -> formula ( ~ a )

let rec nnf = function
    |formula ( a & b ) -> formula ( {nnf a} & {nnf b} )
    |formula ( ~ ( a & b ) ) -> 
            formula ( {nnf formula ( ~ a )} v {nnf formula ( ~ b )} )

    |formula ( a v b ) -> formula ({nnf a} v {nnf b})
    |formula ( ~ ( a v b ) ) ->
            formula ( {nnf formula ( ~ a )} & {nnf formula ( ~ b )} )

    |formula ( a <-> b ) ->
            formula ( {nnf formula ( a -> b )} & {nnf formula ( b -> a )} )
    |formula ( ~ ( a <-> b ) ) ->
            formula ( {nnf formula ( ~ (a -> b) )} v {nnf formula ( ~ (b -> a) )} )
            
    |formula ( a -> b ) -> nnf formula ( (~ a) v b )
    |formula ( ~ (a -> b) ) -> nnf formula ( a & (~ b) )
    |formula ( ~ ~ a ) -> nnf a

    |formula (Verum) -> formula (Verum)
    |formula (Falsum) -> formula (Falsum)
    |formula (~ Verum) -> formula (Falsum)
    |formula (~ Falsum) -> formula (Verum)

    |formula ( ~ A ) as f -> f
    |formula ( A ) as f -> f

let cnf t =
    let rec distr = function
        |formula ( x v ( y & z ) ) ->
                formula ({distr( formula ( x v y) )} & {distr( formula ( x v z) )})
        |x -> x
    in
    let rec distl = function
        |formula ( ( y & z ) v x ) -> formula ( {distl formula (y v x)} & {distl formula ( z v x ) })
        |x -> x
    in
    let dist x = distr(distl x) 
    in
    let rec conjnf = function
        |formula (t1 & t2) -> formula ({conjnf(t1)} & {conjnf(t2)})
        |formula (t1 v t2) -> dist (formula ( {conjnf(t1)} v {conjnf(t2)}))
        |x -> x
in conjnf t

(*
let cnfl t =
    let i = ref 0 in
    let rec lits = function
        |formula ( A v B ) as t -> [t]
        |formula ( A & B ) as t -> [t]
        |formula ( ~ A v B ) as t -> [t]
        |formula ( ~ A & B ) as t -> [t]
        |formula ( A v ~ B ) as t -> [t]
        |formula ( A & ~ B ) as t -> [t]

        |formula ( a v b ) -> ( lits a ) @ (lits b )
        |formula ( a & b ) -> ( lits a ) @ (lits b )
        |_ -> []
    in
    let rec aux t acc = function
        |hd::tl ->
                let j = incr i ; !i in
                let a = ( formula (p(j) <-> hd ) ) in
                let b = formula ( t{p(j)/hd} ) in
                let acc' = formula ( a & acc ) in
                aux b acc' tl
        |[] -> formula (t & acc)
    in
    let t1 = cnf ( nnf t ) in
    aux t1 formula ( Verum ) (ExtList.list_uniq ( lits t1 ))

(* formula list -> formula list *)

let listfy t =
    let rec split = function
        |formula (a & b) -> split ( formula (a) ) @ split ( formula (b) )
        |_ as f -> [`Formula f]
    in
    match t with
    |[`Formula t] -> Basictype.open_bt_list (split (cnf t))
    |_ -> failwith "listfy"
*)
