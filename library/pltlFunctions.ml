
CONNECTIVES
  And, "_&_",  Two;
  Or,  "_v_",  Two;
  Imp, "_->_", One;
  DImp, "_<->_", One;
  Until, "_Un_", One;
  Before, "_Bf_", One;
  Not, "~_", Zero;
  Next, "X_", Zero;
  Generally, "G_", Zero;
  Sometimes, "F_", Zero;
  Falsum, Const;
  Verum, Const
END

open Twblib

let push (xa,xb,z,ev,br) = 
    let set = (new Set.set)#addlist (xa@xb@z)
    in br#add (set, ev)
;;

let termfalse = `Formula ( term ( Falsum )) ;; 
let setclose () = (new Set.set)#add termfalse ;;
let setclosen br = br#length ;;

let beta (uev1, uev2, n1, n2, br) =
    let m = (br#length - 1) in
    let _ =
        if !debug then
        Printf.printf "BETA\nm:%d\nuev1: %s\nuev2 : %s\nBr: %s\n"
        m uev1#to_string uev2#to_string br#to_string
        else ()
    in
    if uev1#is_empty || uev2#is_empty then (new Set.set)
    else if (List.hd uev2#elements) = termfalse then uev1
    else if (List.hd uev1#elements) = termfalse then uev2
    else if n1 > m && n2 > m then (new Set.set)#add termfalse
    else if n1 <= m && n2 > m then uev1
    else if n1 > m && n2 <= m then uev2
    else uev1#intersect uev2
;;

(* we effectively use a list, not a queue, so we need to reverse
 * the list to look up the index *)
let rec index n s l =
    if List.length l > 0 then
        if s#is_equal (List.nth l n) then n
        else
            if n < ((List.length l) - 1) then index (n+1) s l
            else failwith "index: core not found"
    else failwith "index: list empty"
;;


let loop_check (xa,xb,z,br) =
    let (br1, br2) = List.split br#elements in
    let set = (new Set.set)#addlist (xa@xb@z) in
    not(List.exists (fun s -> set#is_equal s) br1)
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
    if !debug then
    Printf.printf "SetUev: %d\n%s\n" i (uev#to_string)
    else () ;
    uev
;;

let setn (xa,xb,z,br) =
    let (br1, br2) = List.split br#elements in
    let set = (new Set.set)#addlist (xa@xb@z)
    in index 0 set br1
;;
