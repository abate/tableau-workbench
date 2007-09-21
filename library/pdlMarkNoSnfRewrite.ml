source PdlMarkNoSnf

let neg_term = function formula ( a ) -> formula ( ~ a )

let rec nnf_term = function
  | formula ( a & b ) -> formula ( {nnf_term a} & {nnf_term b} )
  | formula ( ~ ( a & b ) ) ->
      formula ( {nnf_term formula ( ~ a )} v {nnf_term formula ( ~ b )} )
  | formula ( a v b ) -> formula ({nnf_term a} v {nnf_term b})
  | formula ( ~ ( a v b ) ) ->
      formula ( {nnf_term formula ( ~ a )} & {nnf_term formula ( ~ b )} )
  | formula ( a <-> b ) ->
      formula ( {nnf_term formula ( a -> b )} & {nnf_term formula ( b -> a )} )
  | formula ( ~ ( a <-> b ) ) ->
      formula ( {nnf_term formula ( ~ (a -> b) )} v {nnf_term formula ( ~ (b -> a) )} )
  | formula ( a -> b ) -> nnf_term formula ( (~ a) v b )
  | formula ( ~ (a -> b) ) -> nnf_term formula ( a & (~ b) )
  | formula ( ~ ~ a ) -> nnf_term a
  | formula ( < p > a ) -> formula ( < p > {nnf_term a} )
  | formula ( ~ ( < p > a ) ) -> formula ( [ p ] {nnf_term ( formula ( ~ a ) )} )
  | formula ( [ p ] a ) -> formula ( [ p ] {nnf_term a} )
  | formula ( ~ ( [ p ] a ) ) -> formula ( < p > {nnf_term ( formula ( ~ a ) )} )
  | formula (Verum) as f -> f
  | formula (Falsum) as f -> f
  | formula (~ Verum) -> formula (Falsum)
  | formula (~ Falsum) -> formula (Verum)
  | formula ( ~ A ) as f -> f
  | formula ( A ) as f -> f
