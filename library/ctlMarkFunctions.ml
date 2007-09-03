
source CtlMark

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer
        let copy s = s
    end
)

module FormulaIntSet = TwbSet.Make(
    struct
        type t = formula * int
        let to_string (f,i) = Printf.sprintf "(%i,%s)" i (formula_printer f)
        let copy s = s
    end
)

module ListFormulaSet = TwbList.Make(
    struct
        type t = FormulaSet.set
        let to_string s = s#to_string
        let copy s = s#copy
    end
)
;;

let rec filter_map f = function
    | [] -> []
    | hd :: tl ->
            begin match f hd with
            |None -> filter_map f tl
            |Some(a) -> a :: filter_map f tl
            end
;;

let push (dia,box,hcore) = 
    let nodeset = (new FormulaSet.set)#addlist (dia@box) 
    in hcore#add nodeset
;;

let index (node,hcore) = 
    let set = (new FormulaSet.set)#addlist node in
    let rec aux n s l =
        if s#is_equal (List.nth l n) then Some(n)
        else if n < ((List.length l) - 1) then aux (n+1) s l
        else None
    in
    if List.length hcore > 0 then aux 0 set hcore
    else None
;;

let loop (node,hcore) =
    match index (node,hcore) with
    |None -> false
    |Some(_) -> true
;;

(* true if there is not an element in the list equal to (dia@box) *)
let loop_check (dia,box,hcore) = not(loop(dia@box,hcore#elements))

let uev_disj (mrks,uevs,p) =
    let undef = new FormulaIntSet.set in
    (* Am I the witness *)
    let excl (uev,p) = 
        let p = List.hd p in
        if List.exists (fun (f,_) -> f = p) uev#elements then undef
        else uev
    in
    let min (uev1,uev2) = 
        if uev1#length = 0 || uev2#length = 0 then undef
        else
            (new FormulaIntSet.set)#addlist(
                filter_map (fun (x,nx) ->
                    try
                        let (z,nz) =
                            List.find (fun (y,_) -> y = x) uev1#elements
                        in
                        begin match x with
                        |formula (A a U d) -> Some(x,min nx nz)
                        |formula (E a U d) -> Some(x,max nx nz)
                        |_ -> failwith "dddddd"
                        end
                    with Not_found -> None
                ) uev2#elements
            )
    in
    match (mrks,uevs) with
    |[mrk1],_ when mrk1 = false -> undef
    |[mrk1;mrk2],[uev1;uev2] when mrk1 && mrk2 -> undef
    |[mrk1;mrk2],[uev1;uev2] when not(mrk1) && mrk2 -> excl(uev1,p)
    |[mrk1;mrk2],[_;uev2] when mrk1 && not(mrk2) -> uev2
    |[mrk1;mrk2],[uev1;uev2] -> min(excl(uev1,p),uev2)
    |_ -> failwith "uev_disj"
;;

let mrk_disj (mrks,_,_) =
    match mrks with
    |[mrk1] -> mrk1 (* must be false because of the branch condition *)
    |[mrk1;mrk2] -> mrk1 && mrk2
    |_ -> failwith "mrk_disj"
;;

let uev_ext (mrks,uevs,dia,box,hcore) =
    let undef = new FormulaIntSet.set in
    let l = List.length hcore#elements in
    let p = List.hd dia in
    (* add a uev if I'm THE branch, the eventuality don't loop below
     * and if the uev = AU then I take the maximum, if there is more
     * then one *)
    let max (uev1,uev2) =
        (new FormulaIntSet.set)#addlist(
            filter_map (fun (x,i) -> match x with
                |formula (E a U d) when x = p && l > i -> 
                        Some(x,i)
                |formula (A a U d) when List.mem x box && l > i -> 
                        begin try
                            let (z,j) =
                                List.find (fun (y,_) -> y = x) uev2#elements
                            in
                            Some(x,max i j)
                        with Not_found -> Some(x,i) end
                |formula (E a U d) -> None
                |formula (A a U d) -> None 
                |_ -> failwith "uev_ext max"
            ) uev1#elements
        )
    in
    match (mrks,uevs) with
    |[mrk1],[uev1] -> max(uev1,undef)
    |[mrk1;mrk2],[uev1;uev2] -> max(uev1,uev2)
    |_ -> failwith "uev_ext"
;;

let mrk_ext (mrks,uevs,dia,box,hcore) = 
    match mrks with
    |[mrk1] -> mrk1
    |[mrk1;mrk2] -> mrk1 || mrk2
    |_ -> failwith "mrk_ext"
;;

let uev_loop (diax,box,hcore) = 
    let checkuev (dia,box,hcore) = 
        match index(dia::box,hcore) with
        |None -> None
        |Some(i) ->
                Some(
                    (new FormulaIntSet.set)#addlist (
                        filter_map (function
                            |formula (E a U d) as x when x = dia -> 
                                    Some(formula (E a U d),i)
                            |formula (A a U d) as x when List.mem x box -> 
                                    Some(formula (A a U d),i)
                            |_ -> None
                        ) (dia::box)
                    )
                )
    in
    let l = hcore#elements in
    let uevlist = filter_map(fun dia -> checkuev (dia,box,l)) diax in
    List.fold_left (fun e s -> s#union e) (new FormulaIntSet.set) uevlist
;;

(* Since all formulae here are blocked, mrk is true iff there is one
 * looping bad eventuality *)
let mrk_loop (diax,box,hcore) = not((uev_loop (diax,box,hcore))#is_empty) ;;
