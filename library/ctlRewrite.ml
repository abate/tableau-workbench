
source Ctl

let rec nnf_term f = 
    match f with
    |formula ( a & b ) ->
        let x = nnf_term a
        and y = nnf_term b
        in formula ( x & y )

    |formula ( ~ ( a & b ) ) ->
        let x = nnf_term formula ( ~ a )
        and y = nnf_term formula ( ~ b )
        in formula ( x v y )

    |formula ( a v b ) ->
            let x = nnf_term a
            and y = nnf_term b
            in formula ( x v y )

    |formula ( ~ ( a v b ) ) ->
            let x = nnf_term formula ( ~ a )
            and y = nnf_term formula ( ~ b )
            in formula ( x & y )

    |formula ( a <-> b ) ->
            let x = nnf_term formula ( a -> b )
            and y = nnf_term formula ( b -> a )
            in formula ( x & y )

    |formula ( ~ ( a <-> b ) ) ->
            let x = nnf_term formula ( ~ (a -> b) )
            and y = nnf_term formula ( ~ (b -> a) )
            in formula ( x v y )

    |formula ( a -> b ) ->
            nnf_term formula ( (~ a) v b )

    |formula ( ~ (a -> b) ) ->
            nnf_term formula ( a & (~ b) )

    |formula ( ~ ~ a ) -> nnf_term a

    |formula ( ~ P ) as f -> f
    |formula ( P ) as f -> f

            
    |formula ( ~ ( AX a ) ) -> 
            let x = nnf_term ( formula ( ~ a ) )
            in formula ( EX x )
            
    |formula ( ~ ( EX a ) ) -> 
            let x = nnf_term ( formula ( ~ a ) )
            in formula ( AX x )
            
    |formula ( ~ AG a ) ->
            let x = nnf_term ( formula ( ~ a ) )
            in nnf_term formula ( EF x )
            
    |formula ( ~ EG a ) ->
            let x = nnf_term ( formula ( ~ a ) )
            in nnf_term formula ( AF x )
 
    |formula ( AG a ) -> 
            let x = nnf_term ( formula ( ~ a ) )
            in formula ( A Falsum B x )

    |formula ( EG a ) ->
            let x = nnf_term ( formula ( ~ a ) )
            in formula ( E Falsum B x )

    |formula ( ~ EF a ) -> 
            let x = nnf_term formula ( ~ a )
            in nnf_term formula ( AG x )

    |formula ( ~ AF a ) -> 
            let x = nnf_term formula ( ~ a )
            in nnf_term formula ( EG x )

    |formula ( ~ ( E a U b ) ) ->
            let x = nnf_term formula ( ~ a )
            in formula ( E x B {nnf_term b} )

    |formula ( ~ ( A a U b ) ) ->
            let x = nnf_term formula ( ~ a )
            in formula ( A x B {nnf_term b} )

    |formula ( ~ ( E a B b ) ) ->
            let x = nnf_term formula ( ~ a )
            in formula ( E x U {nnf_term b} )

    |formula ( ~ ( A a B b ) ) ->
            let x = nnf_term formula ( ~ a )
            in formula ( A x U {nnf_term b} )

    |formula ( EF a ) -> formula ( E Verum U {nnf_term a} )
    |formula ( AF a ) -> formula ( A Verum U {nnf_term a} )

    |formula ( AX a ) -> formula ( AX {nnf_term a} )
    |formula ( EX a ) -> formula ( EX {nnf_term a} )

    |formula ( E a U b ) -> formula ( E {nnf_term a} U {nnf_term b} )
    |formula ( A a U b ) -> formula ( A {nnf_term a} U {nnf_term b} )
    |formula ( E a B b ) -> formula ( E {nnf_term a} B {nnf_term b} )
    |formula ( A a B b ) -> formula ( A {nnf_term a} B {nnf_term b} )

    |formula ( ~ Falsum ) -> formula ( Verum )
    |formula ( ~ Verum ) -> formula ( Falsum )
    |formula ( Falsum ) -> formula ( Falsum )
    |formula ( Verum ) -> formula ( Verum )
    
let neg_term = function formula ( a ) -> formula ( ~ a ) 
