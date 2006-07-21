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
    let m = br#length in
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
    List.exists (fun s -> set#equal s) br1
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
            |`Formula term ( c Un d ) -> not(List.mem (`Formula d) loopset)
            |_ -> false
        )
    in uev
;;

let setn (xa,xb,z,br) =
    let (br1, br2) = List.split br#elements in
    let set = (new Set.set)#addlist (xa@xb@z)
    in index 0 set br1
;;
   
let min (a,b) = min a b ;;

