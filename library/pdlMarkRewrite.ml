source PdlMark

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

let rec eps_free = function
  | program ( * a ) -> false
  | program ( ? f ) -> false
  | program ( a U b ) -> (eps_free a) && (eps_free b)
  | program ( a ; b ) -> (eps_free a) || (eps_free b)
  | _ -> true

let rec snf_term = function
  | formula ( a & b ) -> formula ( {snf_term a} & {snf_term b} )
  | formula ( a v b ) -> formula ({snf_term a} v {snf_term b})
  | formula ( < p > a ) -> formula ( < {snf_prog p} > {snf_term a} )
  | formula ( [ p ] a ) -> formula ( [ {snf_prog p} ] {snf_term a} )
  | formula ( a ) as f -> f
and snf_prog = function
  | program ( * a ) ->
      begin 
        match ef_prog a with
        | None -> program ( ? Verum )
        | Some a1 -> program ( * a1 )
      end
  | program ( ? f ) -> program ( ? {snf_term f} )
  | program ( a U b ) -> program ( {snf_prog a} U {snf_prog b} )
  | program ( a ; b ) -> program ( {snf_prog a} ; {snf_prog b} )
  | _ as p -> p
and ef_prog = function
  | program ( * a ) ->
      begin
        match ef_prog a with
        | None -> None
        | Some a1 -> Some (program ( a1 ; ( * a1 ) ))
      end
  | program ( ? f ) -> None
  | program ( a U b ) ->
      begin
        match (ef_prog a, ef_prog b) with
        | (None, ob1) -> ob1
        | (oa1, None) -> oa1
        | (Some a1, Some b1) -> Some (program ( a1 U b1 ))
      end
  | program ( a ; b ) ->
      let sa = snf_prog a in
      let sb = snf_prog b in
      if eps_free a || eps_free b then Some (program ( sa ; sb ))
      else
        begin
          match (ef_prog a, ef_prog b) with
          | (None, None) -> None
          | (None, Some b1) -> Some (program ( sa ; b1 ))
          | (Some a1, None) -> Some (program ( a1 ; sb ))
          | (Some a1, Some b1) -> Some (program ( ( a1 ; sb ) U ( sa ; b1 ) ))
        end
  | _ as p -> Some p

let nnf_snf_term f =
  let nnf = nnf_term f in
  let snf = snf_term nnf in
  print_endline (formula_printer snf);
  snf
