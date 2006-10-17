CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  ExX, "ExX_", One;
  AxX, "AxX_", One;
  ExG, "ExG_", One;
  ExF, "ExF_", One;
  AxG, "AxG_", One;
  AxF, "AxF_", One;
  Not, "~_",   Zero;
  Star, "*_",   Zero;
  Falsum, Const;
  Verum, Const
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
let emptyset h = h#empty
let unstar l = Basictype.map (function Star x -> x |x -> x) l
    
let not_false l =
    not(List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        |_ -> false
    ) l#elements)
;;

let push (dia,box,fev,br) = 
    let nodeset = (new Set.set)#addlist (dia@box) 
    in br#add (nodeset,fev)
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
            ExtList.filter_map (fun (x,nx) ->
                try
                    let (z,nz) = 
                        List.find (fun (y,_) -> y = x) uev1#elements
                    in
                    begin match x with
                    |`LabeledFormula ([],term (ExF d)) -> Some(x,min nx nz)
                    |`LabeledFormula ([],term (AxF d)) -> Some(x,max nx nz)
                    |_ -> failwith "dddddd"
                    end
                with Not_found -> None
            ) uev2#elements
        )
        in if !debug then (Printf.printf "INTER %s\n" a#to_string ; a) else a
;;

let rec index n s l =
    if List.length l > 0 then
        if s#is_equal (List.nth l n) then n
        else
            if n < ((List.length l) - 1) then index (n+1) s l
            else failwith "index: core not found"
    else failwith "index: list empty"
;;

(* true if there is not an element in the list equal to (dia@box) *)
let loop_check (dia,box,br) =
    let set = (new Set.set)#addlist (dia@box) in
    not(List.exists (fun (s,_) -> set#is_equal s) br#elements)
;;

exception Stop_exn of int ;;
let procastinator idx ev (br1,br2) = 
    let bra1 = Array.of_list br1 in
    let bra2 = Array.of_list br2 in
    let len = Array.length bra1 in
    try
        Array.iter (fun set ->
            if (set#mem ev) then ()
            else raise ( Stop_exn 0)
        ) (Array.sub bra1 idx ( len - idx )) ;
        (* the fev are displaced by one and were happy if it is not in the fev *)
        Array.iter (fun fev ->
            if not(fev#mem ev) then ()
            else raise ( Stop_exn 0)
        ) (Array.sub bra2 (idx + 1) ( len - (idx + 1) )) ;
        true
    with Stop_exn _ -> false
;;

let setuev_loop (diax,box,fev,brl) =
    let (br1, br2) = List.split brl#elements in
    let checkuev node fev br =
        let set = (new Set.set)#addlist node in
        if List.exists ( fun s -> set#is_equal s ) br then
            let i = index 0 set br in
            Some(
                (new Setoftermint.set)#addlist (
                    ExtList.filter_map (function
                        |`LabeledFormula ([],term (ExF d)) as ev when
                        procastinator i ev (br1,br2) && (* it's a procastinator *)
                        not(fev#mem ev) -> (* and is not in the fev of the last world *)
                            Some(`LabeledFormula ([],term (ExF d)),i)
                        |`LabeledFormula ([],term (AxF d)) as ev when
                        procastinator i ev (br1,br2) &&
                        not(fev#mem ev) -> 
                            Some(`LabeledFormula ([], term (AxF d)),i)
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
                ExtList.filter_map(fun dia ->
                    checkuev (dia::box) fev br1
                ) diax
    in
    let uev =
        List.fold_left (fun e s -> s#union e)
        (new Setoftermint.set) uevlist
    in
    if !debug then Printf.printf "SetUevLoop: %s\n" (uev#to_string)
    else () ;
    uev
;;

let setuev_pi (uev1, uev2, br) = 
    let l = (br#length -1) in
    let uev = (uev1#union uev2) in
    let _ =
        if !debug then
        Printf.printf "PI\nm:%d\nuev: %s\n" l uev#to_string
        else ()
    in
    if List.exists ( fun (_,n) -> n > l ) uev#elements
    then (new Setoftermint.set)#add (termfalse,l+1)
    else if List.exists (function
        |(`Formula ( term ( Falsum ) ),_) -> true
        |_ -> false
        ) uev#elements
    then (new Setoftermint.set)#add (termfalse,l+1)
    else if List.for_all ( fun (_,n) -> n <= l ) uev#elements
    then uev
    else failwith ("pi: impossible")
;;
