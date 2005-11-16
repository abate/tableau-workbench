
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Until, "_Un_", One;
  Before, "_Bf_", One;
  Not, "~_",   Simple;
  Next, "X_", Simple;
  Generally, "G_", Simple;
  Sometimes, "F_", Simple;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  Ev : Set.set ;
  Br : Listofsets.listobj ;
  uev : Setoftermint.set; 
  status : String
END

(* debug flag *)
let debug = ref false ;;

let add (l,h) = h#addlist l
let notin (l,h) = not(h#mem (List.hd l))
let isin (l,h) = h#mem (List.hd l)
let not_empty l = not(l#is_empty)

let emptyset h = h#empty
let push (xa,xb,z,br) = 
    let set = (new Set.set)#addlist (xa@xb@z)
    in br#add set
;;

let termfalse = `Formula ( term ( Falsum ) ) ;; 
let setclose br = (new Setoftermint.set)#add (termfalse, br#length) ;;

let beta (uev1, uev2, br) =
    let m = (br#length - 1) in
    let _ =
        if !debug then
        Printf.printf "BETA\nm:%d\nuev1: %s\nuev2 : %s\nBr: %s\n"
        m uev1#to_string uev2#to_string br#to_string
        else ()
    in

    if uev1#is_empty || uev2#is_empty then (new Setoftermint.set)
    
    else if List.exists (function 
        |(`Formula ( term ( Falsum ) ),_) -> true
        |_ -> false) uev1#elements
    then uev2
    
    else if List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        | _ -> false) uev2#elements
    then uev1
    
    else if List.for_all ( fun (_,n) -> n > m ) (uev1#union uev2)#elements
    then (new Setoftermint.set)#add (termfalse,m+1)
    
    else if List.for_all ( fun (_,n) -> n <= m ) uev1#elements &&
    List.for_all ( fun (_,n) -> n > m ) uev2#elements 
    then uev1
    
    else if List.for_all ( fun (_,n) -> n <= m ) uev2#elements &&
    List.for_all ( fun (_,n) -> n > m ) uev1#elements
    then uev2
    
    else
        (new Setoftermint.set)#addlist(
            ExtLib.List.filter_map (fun (x,nx) ->
                try
                    let (z,nz) =
                        List.find (fun (y,_) -> y = x)
                        uev1#elements
                    in Some(x,min nx nz)
                with Not_found -> None
            ) uev2#elements
        )
        (* uev1#intersect uev2 *)
;;

exception Stop of int ;;
let index br s =
    let i = ref 0 in
    try begin
        List.iter (fun e ->
            if s#equal e then raise ( Stop !i) else incr i
        ) br#elements;
        failwith "index: list empty"
        end
    with Stop(n) -> n
;;

let loop_check (xa,xb,z,br) =
    let set = (new Set.set)#addlist (xa@xb@z) in
    not(List.exists (fun s -> set#equal s) br#elements)
;;

let setuev (xa,xb,z,ev,br) =
    let set = (new Set.set)#addlist (xa@xb@z) in
    let i = index br set in
    let loopset = ev#elements in 
    let uev =
        (new Setoftermint.set)#addlist (
            List.map (fun e -> (e,i))
            (List.filter (function
                |`Formula term (X (c Un d)) ->
                        not(List.mem (`Formula d) loopset)
                |_ -> false
            ) (xa@xb))
        )
    in
    if !debug then
    Printf.printf "SetUev: %d\n%s\n" i (uev#to_string)
    else () ;
    uev
;;

let pi (uev, br, ev) =
    let m = br#length in
    let loopset = ev#elements in
    uev#filter (function
        |(`Formula term (X (c Un d)), n) when (n > m) ->
              not(List.mem (`Formula d) loopset)
        |_ -> true
    )
;;

let rec nnf_term f = 
(*    print_endline (Basictype.string_of_formula f); *)
    match f with
    |term ( a & b ) ->
        let x = nnf_term a
        and y = nnf_term b
        in term ( x & y )

    |term ( ~ ( a & b ) ) ->
        let x = nnf_term term ( ~ a )
        and y = nnf_term term ( ~ b )
        in term ( x v y )

    |term ( a v b ) ->
            let x = nnf_term a
            and y = nnf_term b
            in term ( x v y )

    |term ( ~ ( a v b ) ) ->
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

    |term ( ~ ~ a ) -> nnf_term a

    |term ( ~ .a ) as f -> f
    |term ( .a ) as f -> f

    |term ( X a ) -> 
            let x = nnf_term a
            in term ( X x )
            
    |term ( ~ ( X a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( X x )
            
    |term ( ~ G a ) ->
            nnf_term term ( F ~ a )
    |term ( G a ) -> 
            let x = nnf_term term ( a )
            in term ( G x )

    |term ( ~ F a ) ->
            nnf_term term ( G ~ a )
    |term ( F a ) ->
            nnf_term term ( Verum Un a )

    |term ( ~ (a Bf b) ) ->
            nnf_term term ( (~ a) Un b )
    |term ( a Bf b ) ->
            let x = nnf_term term ( a )
            and y = nnf_term term ( b )
            in term ( x Bf y )

    |term ( ~ (a Un b) ) ->
            nnf_term term ( (~ a) Bf b )
    |term ( a Un b ) ->
            let x = nnf_term term ( a )
            and y = nnf_term term ( b )
            in term ( x Un y )

    |term ( ~ Falsum ) -> term ( Verum )
    |term ( ~ Verum ) -> term ( Falsum )

    |term ( Constant ) -> f
    |term ( ~ Constant ) -> f
    
    | _ -> failwith ("nnf_term"^(!Basictype.string_of_formula f))
;;

let neg_term = function term ( a ) -> term ( ~ a ) ;;
let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

TABLEAU

  RULE Id
  { A } ; { ~ A } ; Z
  ===============
     Stop

  BACKTRACK [ uev := setclose (Br) ]

  END
  
  RULE False
  Falsum ; Z
  ===============
     Stop

  BACKTRACK [ uev := setclose (Br) ]

  END

  RULE Loop
  { X A } ; X B ; Z
  =================
       Stop

  BACKTRACK [ uev := setuev(X A, X B, Z, Ev, Br) ]

  END

  RULE Next
  { X A } ; X B ; Z
  =================
      A ; B
      
  COND [ loop_check(X A, X B, Z, Br) ]
  ACTION [
      Ev := emptyset(Ev);
      Br := push(X A, X B, Z, Br)
  ]
  BACKTRACK [ uev := pi(uev(1), Br, Ev) ]

  END

  RULE Before
    {A Bf C}
  ==========================
   nnf (~ C) ; A v X (A Bf C)

  END

  RULE Until
           { C Un D } 
  =============================
      D ||| C ; X ( C Un D ) 

  ACTION    [ [ Ev := add(D, Ev) ] ; [] ]
  BACKTRACK [ uev := beta(uev(1), uev(2), Br) ]
  BRANCH    [ [ not_empty(uev(1)) ] ] 
    
  END
 
  RULE Or
  { A v B }
  =========
   A ||| B

  BACKTRACK [ uev := beta(uev(1), uev(2), Br) ]
  BRANCH [ [ not_empty(uev(1)) ] ] 
  END

  RULE And
  { A & B }
  =========
    A ; B
  END

  RULE GE
     { G A }
  =============
   A ; X (G A)
  END
  
END

let strategy = new Strategy.strategy "start";;
let _ = 
    strategy#add "start" (R(new and_rule))  "start" "a" ;
    strategy#add "a"     (R(new or_rule))   "a" "i2" ;
    strategy#add "i2"    (R(new until_rule)) "i2" "i3" ;
    strategy#add "i3"    (R(new ge_rule)) "i3" "i4" ;
    strategy#add "i4"    (R(new before_rule)) "i4" "b" ;
    strategy#add "b"     (R(new id_rule))   "b" "c";
    strategy#add "c"     (R(new false_rule))   "c" "s1";
    strategy#add "s1"    S                  "start" "d" ;
    strategy#add "d"     (R(new next_rule)) "d" "s2";
    strategy#add "s2"    S                  "start" "meta" ;
    strategy#add "meta"  (R(new loop_rule)) "end" "end" ;
    strategy#add "end"   E__                "end" "end"
;;

let exit (uev) =
    match uev#elements with
    |(termfalse,_)::[] -> "Closed"
    |[] -> "Open"
    |_ -> "Closed"
;;

PP := nnf
NEG := neg
EXIT := exit (uev(1))

STRATEGY (A)

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END

