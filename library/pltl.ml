
CONNECTIVES
  And, "_&_",  One;
  Or,  "_v_",  One;
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
  Br : Listoftupleset.listobj ;
  uev : Set.set; 
  status : String;
  n : Int default 0
END

let add (l,h) = h#addlist l
let notin (l,h) = not(h#mem (List.hd l))
let isin (l,h) = h#mem (List.hd l)
let not_empty l = not(l#is_empty)

let emptyset h = h#empty
let push (xa,xb,z,ev,br) = 
    let set = (new Set.set)#addlist (xa@xb@z)
    in br#add (set, ev)
;;

let termfalse = `Formula ( const ( Falsum )) ;; 
let setclose () = (new Set.set)#add termfalse ;;
let setclosen br = br#length ;;

let beta (uev1, uev2, n1, n2, br) =
    print_endline "Beta";
    print_string "uev 1:";
    print_endline uev1#to_string;
    print_string "uev 2:";
    print_endline uev2#to_string;
    print_string "n1: "; print_int n1;
    print_newline ();
    print_string "n2: "; print_int n2;
    print_endline "--------------";
    let m = (br#length - 1) in
    if uev1#is_empty || uev2#is_empty then (new Set.set)
    else if n1 > m && n2 > m then (new Set.set)#add termfalse
    else if n1 <= m && n2 > m then uev1
    else if (List.hd uev2#elements) = termfalse then uev1
    else if n1 > m && n2 <= m then uev2
    else if (List.hd uev1#elements) = termfalse then uev2
    else uev1#intersect uev2
;;

let rec index n s l =
    if List.length l > 0 then
        if s#equal (List.nth l n) then n
        else
            if n < ((List.length l) - 1) then index (n+1) s l
            else failwith "index: core not found"
    else failwith "index: list empty"
;;

let loop_check (xa,xb,z,br) =
    let (br1, br2) = List.split br#elements in
    let set = (new Set.set)#addlist (xa@xb@z) in
    not(List.exists (fun s -> set#equal s) br1)
;;

let setuev (xa,xb,z,ev,br) =
    let (br1, br2) = List.split br#elements in
    let set = (new Set.set)#addlist (xa@xb@z) in
    let i = index 0 set br1 in
    let rec buildset counter bl acc =
        if counter < ((List.length bl) - 1) then
            let bl_i = (List.nth bl counter) in
            buildset (counter+1) bl (acc@(bl_i#elements))
        else acc
    in
    let loopset = ((ev#elements) @ (buildset (i+1) br2 [])) in 
    let uev = 
        set#filter (function
            |`Formula term ( X ( c Un d ) ) -> 
                    not(List.mem (`Formula d) loopset)
            |_ -> false
        )
    in 
    print_string "SetUev: "; print_endline (uev#to_string);
    uev
;;

let setn (xa,xb,z,br) =
    let (br1, br2) = List.split br#elements in
    let set = (new Set.set)#addlist (xa@xb@z)
    in index 0 set br1
;;
   
let min (a,b) = min a b ;;

let rec nnf_term f = 
(*    print_endline (Basictype.string_of_formula f); *)
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

    | term ( ~ .a ) as f -> f
    | term ( .a ) as f -> f

    | term ( X a ) -> 
            let x = nnf_term a
            in term ( X x )
            
    | term ( ~ ( X a ) ) -> 
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

    | _ -> failwith "nnf_term"
;;

let neg_term = function term ( a ) -> term ( ~ a ) ;;
let neg = Basictype.map neg_term ;;
let nnf = Basictype.map nnf_term ;;

TABLEAU

  RULE Id
  { A } ; { ~ A } ; Z
  ===============
     Axiom

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END
  
  RULE False
  Falsum ; Z
  ===============
     Axiom

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END

  RULE Loop
  { X A } ; X B ; Z
  =================
       Axiom

  BACKTRACK [
      uev := setuev(X A, X B, Z, Ev, Br);
      n   := setn (X A, X B, Z, Br)
  ]

  END

  RULE Next
  { X A } ; X B ; Z
  ===========
      A ; B
      
  COND [ loop_check(X A, X B, Z, Br) ]
  ACTION [
      Ev := emptyset(Ev);
      Br := push(X A, X B, Z, Ev, Br)
  ]
      
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
  BACKTRACK [ 
      uev := beta(uev(1), uev(2), n(1), n(2), Br);
      n := min (n(1), n(2))
  ]
(*  BRANCH    [ [ not_empty(uev(1)) ] ] *)
    
  END
 
  RULE Or
  { A v B }
  =========
   A ||| B

  BACKTRACK [ 
      uev := beta(uev(1), uev(2), n(1), n(2), Br);
      n := min (n(1) , n(2))
  ]

(*  BRANCH [ [ not_empty(uev(1)) ] ] *)
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
    strategy#add "end"   E                  "end" "end"
;;

let exit (uev) = 
    if uev#is_empty then "Open"
    else if (List.hd uev#elements) = termfalse
        then "Closed"
        else "Open"
;;

PP := nnf
NEG := neg
EXIT := exit (uev(1))

STRATEGY (A)
