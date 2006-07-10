
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Not, "~_",   Simple;
  ExX, "ExX_", Simple;
  AxX, "AxX_", Simple;
  ExG, "ExG_", Simple;
  ExF, "ExF_", Simple;
  AxG, "AxG_", Simple;
  AxF, "AxF_", Simple;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  Fev : Set.set ;
  Br : Listofsets.listobj ;
  uev : Setoftermint.set ; 
  iev : Set.set ; 
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

let setuev_beta (uev1, uev2, br) =
    let l = (br#length -1) in
    let _ =
        if !debug then
        Printf.printf "BETA\nm:%d\nuev1: %s\nuev2: %s\nBr: %s\n"
        l uev1#to_string uev2#to_string br#to_string
        else ()
    in 
    if (List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        | _ -> false) uev2#elements) 
    then uev1

    else if (List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        | _ -> false) uev1#elements) 
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
        in if !debug then (Printf.printf "INTER %s\n" a#to_string ; a) else a
;;

let setiev_beta(uev1,uev2,iev1,iev2,ev) =
    let _ =
        if !debug then
        Printf.printf "iev1: %s\niev2: %s\n"
        iev1#to_string iev2#to_string
        else ()
    in 
    if (List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        | _ -> false) uev2#elements) ||
        uev1#is_empty
    then iev1#addlist ev

    else if (List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        | _ -> false) uev1#elements) ||
        uev2#is_empty
    then iev2#addlist ev

    else (iev1#union iev2)#addlist ev
;;

exception Stop of int ;;
let index br s =
    let i = ref 0 in
    try begin
        List.iter (fun e ->
            if s#is_equal e then raise ( Stop !i) else incr i
        ) br#elements;
        failwith "index: list empty"
        end
    with Stop(n) -> n
;;

(* true if there is not an element in the list equal to (dia@box) *)
let loop_check (dia,box,br) =
    let set = (new Set.set)#addlist (dia@box) in
    not(List.exists (fun s -> set#is_equal s) br#elements)
;;

let setuev_loop (diax,box,ev,br) =
    let checkuev node ev br =
        let set = (new Set.set)#addlist node in
        if List.exists ( fun s -> set#is_equal s ) br#elements then
            let i = index br set in
            let fev = ev#elements in
            Some(
                (new Setoftermint.set)#addlist (
                    List.filter_map (function
                        |`Formula term (ExX ExF d)
                        when not(List.mem (`Formula term (ExF d)) fev) ->
                            Some(`Formula term (ExF d),i)
                        |`Formula term (AxX AxF d)
                        when not(List.mem (`Formula term (AxF d)) fev) ->
                            Some(`Formula term (AxF d),i)
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
    let uevlist =
        match diax,box with
        |[],[] -> [new Setoftermint.set]
        |[],box ->
                (match checkuev box ev br with
                |Some(l) -> [l]
                |None -> [new Setoftermint.set])
        |dia,_ ->
                List.filter_map(fun dia ->
                    checkuev (dia::box) ev br
                ) diax
    in
    let uev =
        List.fold_left (fun e s -> s#union e)
        (new Setoftermint.set) uevlist
    in
    if !debug then Printf.printf "SetUev: %s\n" (uev#to_string)
    else () ;
    uev
;;

let setuev_pi (uev1, uev2, iev1, iev2, br, ev) =
    let l = (br#length -1) in
    let fev = ev#elements in
    (* all iterated eventualities that don't have a witness in the next
     * zone, but that were supposed to be fulfilled *)
    let uev1' = uev1#filter (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        |(d, _) -> (List.mem (d) (iev1#union iev2)#elements)
    )
    in
    (* all iterated eventualities that have a witness in the next zone *)
    let iev1' = iev1#filter (fun d ->
        not(List.exists (function |(d',_) -> d = d') (uev1#elements))
    )
    in
    (* all iterated eventualities that were supposed to be fulfilled in
     * the next zone, and don't have a false witness *)
    let uev = (uev1'#union uev2)#filter (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        |(`Formula d, _) ->
                not(List.mem (`Formula d) (iev1'#union iev2)#elements)
        |_ -> false
    )
    in
    let _ =
        if !debug then
        Printf.printf "PI\nm:%d\nfev: %s\nuev: %s\n"
        l ev#to_string uev#to_string
        else ()
    in 
    if List.exists ( fun (_,n) -> n > l ) (uev1'#union uev2)#elements
    then (new Setoftermint.set)#add (termfalse,l+1)
    else if List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        |_ -> false) (uev1'#union uev2)#elements
    then (new Setoftermint.set)#add (termfalse,l+1)
    else if List.for_all ( fun (_,n) -> n <= l ) (uev1'#union uev2)#elements
    then
    uev#filter (fun (d, _) -> not(List.mem d fev))
    else failwith ("pi: impossible")
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

    |term ( AxX a ) -> 
            let x = nnf_term a
            in term ( AxX x )
            
    |term ( ~ ( AxX a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( ExX x )

    |term ( ExX a ) -> 
            let x = nnf_term a
            in term ( ExX x )
            
    |term ( ~ ( ExX a ) ) -> 
            let x = nnf_term ( term ( ~ a ) )
            in term ( AxX x )
            
    |term ( ~ AxG a ) ->
            nnf_term term ( ExF ~ a )
            
    |term ( ~ ExG a ) ->
            nnf_term term ( AxF ~ a )
 
    |term ( AxG a ) -> 
            let x = nnf_term term ( a )
            in term ( AxG x )

    |term ( ExG a ) -> 
            let x = nnf_term term ( a )
            in term ( ExG x )

    |term ( ~ ExF a ) -> 
            let x = nnf_term term ( ~ a )
            in term ( AxG x )

    |term ( ~ AxF a ) -> 
            let x = nnf_term term ( ~ a )
            in term ( ExG x )

    |term ( ExF a ) -> 
            let x = nnf_term term ( a )
            in term ( ExF x )

    |term ( AxF a ) -> 
            let x = nnf_term term ( a )
            in term ( AxF x )

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
  BACKTRACK [
      uev := setclose (Br);
      iev := emptyset(Fev)
    ]
  END
  
  RULE False
  Falsum ; Z
  ===============
     Stop

  BACKTRACK [
      uev := setclose (Br);
      iev := emptyset(Fev)
  ]
  END

  RULE Axf
      { AxF P }
  ===================
   P ||| AxX AxF P

  ACTION [ [ Fev := add(AxF P,Fev) ] ; [] ]
  BACKTRACK [
      uev := setuev_beta(uev(1), uev(2), Br);
      iev := setiev_beta(uev(1), uev(2), iev(1), iev(2), AxF P)
  ]
  BRANCH [ [ not_empty(uev(1)) ] ] 
  END

  RULE Exf
      { ExF P }
  ===================
   P ||| ExX ExF P

  ACTION [ [ Fev := add(ExF P,Fev) ] ; [] ]
  BACKTRACK [
      uev := setuev_beta(uev(1), uev(2), Br);
      iev := setiev_beta(uev(1), uev(2), iev(1), iev(2), ExF P)
  ] 
  BRANCH [ [ not_empty(uev(1)) ] ] 
  END 

  RULE Axg
     not_empty_list(AxG P)
  ===================
    P ; AxX AxG P
  END

  RULE Exg
     not_empty_list(ExG P)
  ===================
    P ; ExX ExG P
  END

  RULE Exx
  { ExX P } ; ExX S ; AxX Y ; Z
  =============================
  P ; Y ||| ExX S ; AxX Y
      
  COND [ loop_check(ExX P, AxX Y, Br) ]
  ACTION [ [
      Fev := emptyset(Fev);
      Br := push(ExX P, AxX Y, Br)
  ] ; [] ]
  BACKTRACK [
      uev := setuev_pi(uev(1), uev(2), iev(1), iev(2), Br, Fev);
      iev := emptyset(Fev)
  ]
  BRANCH [ [ not_false(uev(1)) ; not_empty_list(ExX S) ] ]
  END (cache)

  RULE Ref
  is_empty_list(ExX P) ; X
  ====================
      ExX Verum ; X
  END

  RULE Loop
       ExX X ; AxX Y ; Z
  =============================
            Stop

  BACKTRACK [ 
      uev := setuev_loop(ExX X, AxX Y, Fev, Br);
      iev := emptyset(Fev)
  ]
  END

  RULE Or
  { A v B }
  =========
   A ||| B

  BACKTRACK [
      uev := setuev_beta(uev(1), uev(2), Br);
      iev := setiev_beta(uev(1), uev(2), iev(1), iev(2), [])
  ] 
  BRANCH [ [ not_empty(uev(1)) ] ] 
  END

  RULE And
  not_empty_list(A & B)
  =========
    A ; B
  END
  
END

let exit (uev) =
    match uev#elements with
    |(termfalse,_)::[] -> "Closed"
    |[] -> "Open"
    |_ -> "Closed"
;;

PP := nnf
NEG := neg
EXIT := exit (uev(1))

OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END

let saturation = tactic ( (Id; And; Or; Axf; Axg; Exf; Exg; False)* )

let modal = tactic ( ( saturation ; Ref; Exx )* )

STRATEGY ( (modal ; Loop)* )
