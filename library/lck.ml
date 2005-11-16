
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  Diai, "<_>_", Simple;
  Boxi, "[_]_", Simple;
  CDia, "dC_", Simple;
  CBox, "C_", Simple;
  EDia, "dE_", Simple;
  EBox, "E_", Simple;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  Ev : Set.set ;
  Br : Listofsets.listobj ;
  uev : Setoftermint.set ; 
  status : String
END

(* debug flag *)
let debug = ref false ;;

let add (l,h) = h#addlist l
let notin (l,h) = not(h#mem (List.hd l))
let isin (l,h) = h#mem (List.hd l)
let not_empty l = not(l#is_empty)
let is_empty l = l#is_empty
let is_empty_list l = ( List.length l = 0 )
let not_empty_list l = not ( List.length l = 0 )

let not_false l =
    not(List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        |_ -> false
    ) l#elements)
;;

let emptyset h = h#empty
let push (dia,box,br) = 
    let set = (new Set.set)#addlist (dia@box)
    in br#add set
;;

let termfalse = `Formula ( term ( Falsum ) ) ;; 
let setclose br = (new Setoftermint.set)#add (termfalse, br#length) ;;

let beta (uev1, uev2, br) =
    let m = (br#length - 1) in
    let _ =
        if !debug then
        Printf.printf "BETA\nm:%d\nuev1: %s\nuev2: %s\nBr: %s\n\n"
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
        let a = 
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
        in if !debug then (Printf.printf "INTER: %s\n\n" a#to_string ; a) else a
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
    with Stop(n) ->
            if !debug then
                begin
                    Printf.printf "index: %d\nBr: %s\n" n br#to_string;
                    n
                end
            else n
;;

(* true if there is not an element in the list equal to (dia@box) *)
let loop_check (dia,box,br) =
    let set = (new Set.set)#addlist (dia@box) in
    not(List.exists (fun s -> set#equal s) br#elements)
;;

let setuev (dia1,box1,dia2,box2,ev,br) =
    let checkuev node ev br =
        let set = (new Set.set)#addlist node in
        if List.exists ( fun s -> set#equal s ) br#elements then
            let i = index br set in
            let loopset = ev#elements in
            Some(
                (new Setoftermint.set)#addlist (
                    List.filter_map (function
                        |`Formula term (<j> (dC d)) 
                        when not(List.mem (`Formula d) loopset) ->
                            Some(`Formula term (dC d),i)
                        |_ -> None
                    ) (node)
            )
            )
        else begin
            print_endline "SetUEV but not in Br !!!";
            print_endline set#to_string;
            failwith "This should never happen"
        end
    in
    let uevlist1 =
        List.filter_map(fun dia ->
            checkuev (dia::box1) ev br
        ) dia1
    in
    let uevlist2 =
        List.filter_map(fun dia ->
            checkuev (dia::box2) ev br
        ) dia2
    in
    let uev =
        List.fold_left (fun e s -> s#union e)
        (new Setoftermint.set) (uevlist1@uevlist2)
    in
    if !debug then 
        if uev#is_empty then Printf.printf "SetUev: OPEN\n\n" 
        else Printf.printf "SetUev: %s\n\n" (uev#to_string)
    else () ;
    uev
;;

let pi (uev1, uev2, br, ev) =
    let m = br#length in
    let loopset = ev#elements in
    let uevlist = [uev1;uev2] in
    let uev = List.fold_left (fun s e -> s#union e) 
        (new Setoftermint.set) uevlist
    in
    let _ =
        if !debug then
        Printf.printf "PI\nm:%d\nloopset: %s\nuev : %s\n"
        m ev#to_string uev#to_string
        else ()
    in 
    let a =
        uev#filter (function
            |(`Formula term (dC d), n) when (n > m) ->
                  not(List.mem (`Formula d) loopset)
            |_ -> true
        )
    in if !debug then (Printf.printf "filter: %s\n\n" a#to_string ; a) else a
;;

let rec nnf_term f = 
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

    |term ( [i] a ) -> 
            let x = nnf_term a
            in term ( [i] x )
            
    |term ( ~ ( [i] a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( <i> x )

    |term ( <i> a ) -> 
            let x = nnf_term a
            in term ( <i> x )
            
    |term ( ~ ( <i> a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( [i] x )

    |term ( ~ C a ) ->
            nnf_term term ( dC ~ a )
            
    |term ( C a ) -> 
            let x = nnf_term term ( a )
            in term ( C x )

    |term ( ~ dC a ) ->
            nnf_term term ( C ~ a )
 
    |term ( dC a ) -> 
            let x = nnf_term term ( a )
            in term ( dC x )

    |term ( ~ dE a ) -> 
            let x = nnf_term term ( ~ a )
            in term ( E x )

    |term ( dE a ) -> 
            let x = nnf_term term ( a )
            in term ( dE x )

    |term ( ~ E a ) -> 
            let x = nnf_term term ( ~ a )
            in term ( dE x )

    |term ( E a ) -> 
            let x = nnf_term term ( a )
            in term ( E x )

    |term ( ~ Falsum ) -> term ( Verum )
    |term ( ~ Verum ) -> term ( Falsum )

    |term ( Constant ) -> f
    |term ( ~ Constant ) -> f
    
    | _ -> failwith ("nnf_term"^(!Basictype.string_of_formula f))
;;

let neg_term = function term ( a ) -> term ( ~ a ) ;;
let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term

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

  RULE CDia
      { dC P }
  ===================
   dE P ||| dE dC P

  ACTION [ [ Ev := add(P,Ev) ] ; [] ]
  BACKTRACK [ uev := beta(uev(1), uev(2), Br) ]
  BRANCH [ [ not_empty(uev(1)) ] ] 
  END

  RULE EDia
      {  dE P }
  ===================
   <1> P ||| <2> P

  BACKTRACK [ uev := beta(uev(1), uev(2), Br) ] 
  BRANCH [ [ not_empty(uev(1)) ] ] 
  END

  RULE CBox
     not_empty_list(C P)
  ===================
    E P ; E C P
  END

  RULE EBox
     not_empty_list(E P)
  ===================
    [1] P ; [2] P
  END

  RULE Dia1
  { <1> P } ; [1] X ; Z
  =============================
      P ; X ||| [1] X ; Z
      
  COND [ loop_check(<1> P, [1] X, Br) ]
  ACTION [ [
      Ev := emptyset(Ev);
      Br := push(<1> P, [1] X, Br)
  ] ; [] ]
  BACKTRACK [ uev := pi(uev(1), uev(2), Br, Ev) ]
  BRANCH [ [ not_false(uev(1)) ] ]
  END

  RULE Dia2 
  { <2> P } ; [2] X ; Z
  ==================================
      P ; X ||| [2] X ; Z
      
  COND [ loop_check(<2> P, [2] X, Br) ]
  ACTION [ [
      Ev := emptyset(Ev);
      Br := push(<2> P,[2] X, Br)
  ] ; [] ]
  BACKTRACK [ uev := pi(uev(1), uev(2), Br, Ev) ]
  BRANCH [ [ not_false(uev(1)) ] ]
  END
  
  RULE Loop
  <1> X1 ; <2> X2 ; [1] Y1 ; [2] Y2 ; Z
  ==========================================
                   Stop

  BACKTRACK [ uev := setuev(<1> X1,[1] Y1,<2> X2,[2] Y2, Ev, Br) ]
  END

  RULE Or
  { A v B }
  =========
   A ||| B

  BACKTRACK [ uev := beta(uev(1), uev(2), Br) ] 
  BRANCH [ [ not_empty(uev(1)) ] ] 
  END

  RULE And
  not_empty_list(A & B)
  =========
    A ; B
  END
  
END

let strategy = new Strategy.strategy "start";;
let _ = 
    strategy#add "start" (R(new and_rule))   "start" "a" ;
    strategy#add "a"     (R(new false_rule))    "a" "i2" ;
    strategy#add "i2"    (R(new id_rule))   "i2" "i3" ;
    strategy#add "i3"    (R(new edia_rule))   "i3" "i4" ;
    strategy#add "i4"    (R(new cbox_rule))   "i4" "i5" ;
    strategy#add "i5"    (R(new ebox_rule))   "i5" "c" ;
    strategy#add "c"     (R(new or_rule)) "c" "s1";
    strategy#add "s1"    S                   "start" "b" ;
    strategy#add "b"     (R(new cdia_rule))  "start" "s3";
    strategy#add "s3"    S                   "start" "d1" ;
    strategy#add "d1"    (R(new dia1_rule))   "s2" "d2";
    strategy#add "d2"    (R(new dia2_rule))   "s2" "s2";
    strategy#add "s2"    S                   "start" "meta" ;
    strategy#add "meta"  (R(new loop_rule))  "end" "end" ;
    strategy#add "end"   E__                  "end" "end"
;;

STRATEGY (A)

let exit (uev) =
    match uev#elements with
    |[] -> "Open"
    |(termfalse,_)::[] -> "Closed"
    |_ -> "Closed"
;;

PP := nnf
NEG := neg
EXIT := exit (uev(1))

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END

