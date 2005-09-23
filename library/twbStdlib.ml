

let add (l,h) = h#addlist l
let notin (l,h) = h#mem (List.hd l)

let not_marked a =
    match a with
    <> A -> true
    | _ -> false
;;

let not_marked_list l = List.for_all not_marked l

let mark a =
    match a with
    <> B -> @ <> B @
    | _ -> failwith "ddd"
;;

let mark_list l = Basictype.map mark l ;;

