source PdlMark

module FormulaSet = TwbSet.Make(
  struct
    type t = formula
    let to_string = formula_printer
    let copy s = s
  end
 )

module FormulaIntSet = TwbSet.Make(
  struct
    type t = ( formula * formula * int )
    let to_string (f1,f2,i) =
        Printf.sprintf "(%i,%s,%s)" i (formula_printer f1) (formula_printer f2)
    let copy s = s
  end
 )

module ListFormulaSet = TwbList.Make(
  struct
    type t = ( formula * FormulaSet.set )
    let to_string (f,s) = Printf.sprintf "(%s,%s)" (formula_printer f) s#to_string
    let copy (f,s) = (f, s#copy)
  end
 )

(* ------------ Support Functions --------------- *)
let is_emptylist  = function 
  | [] -> true  
  | _ -> false

let not_emptylist = function
  | [] -> false 
  | _ -> true


let rec filter_map f = function
    | [] -> []
    | hd :: tl ->
            begin match f hd with
            |None -> filter_map f tl
            |Some(a) -> a :: filter_map f tl
            end

let uevundef () = new FormulaIntSet.set

let doNextChild_disj (mrk, uev) = mrk || (not uev#is_empty)

let concat (uev1,uev2) = [uev1;uev2]

let uevfilter f uev =
    new FormulaIntSet.set#addlist (filter_map f uev#elements)

(* -------------- Linear Rules --------------- *)

let set_uev_SeqDia (uev,f,z) =
    let f = List.hd f in
    uevfilter (function
        |(formula ( <a ; b > p ) as x1 , x2, i) 
        when x1 = f -> Some(formula ( < a > < b > p ) , x2, i)
        |(x1,x2,i) when List.mem x1 z -> Some(x1,x2,i)
        |_ -> None
    ) uev
;;

let set_uev_TestDia (uev,f,z) =
    let f = List.hd f in
    uevfilter (function
        |(formula ( < ? a > p ) as x1, x2, i) 
        when x1 = f -> Some (formula ( p ) , x2, i)
        |(x1,x2,i) when List.mem x1 z -> Some(x1,x2,i)
        | x -> None
    ) uev
;;

let set_uev_All(uev,z) =
    uevfilter (function
        |(x1,x2,i) when List.mem x1 z -> Some(x1,x2,i)
        |_ -> None
    ) uev

(* ------- Universal Rules --------- *)

let set_uev_UnionDia (uevs,f,z) =
    let f = List.hd f in
    let f1 = 
        uevfilter (function
            |(formula ( < a U b > p ) as x1, x2 , i) 
            when x1 = f -> Some(formula ( <a>p ) , x2 , i)
            |(x1,x2,i) when List.mem x1 z -> Some(x1,x2,i)
            |_ -> None
        )
    in
    let f2 = 
        uevfilter (function
            |(formula ( < a U b > p ) as x1, x2, i) 
            when x1 = f -> Some(formula ( <b>p ) , x2, i)
            |(x1,x2,i) when List.mem x1 z -> Some(x1,x2,i)
            |_ -> None
        )
    in
    match uevs with
    |[uev1] -> [f1 uev1]
    |[uev1;uev2] -> [f1 uev1 ; f2 uev2]
    |_ -> failwith "set_uev_UnionDia"
;;

let set_uev_StarDia (uevs,f,z) =
    let f = List.hd f in
    let f1 = 
        uevfilter (function
            |( x1 , x2, _) when x1 = f && x2 = f -> None
            |(formula ( <a>p ) as x1 , x2, i )
            when x1 = f && not (x2 = f) -> Some (formula ( p ) , x2, i)
            |(x1,x2,i) when List.mem x1 z -> Some(x1,x2,i)
            |_ -> None
        ) 
    in
    let f2 = 
        uevfilter (function
            |(formula ( < * a > p ) as x1 , x2, i) 
            when x1 = f -> Some(formula ( < a > < * a > p ) , x2, i)
            |(x1,x2,i) when List.mem x1 z -> Some(x1,x2,i)
            |_ -> None
        ) 
    in
    match uevs with
    |[uev1] -> [f1 uev1]
    |[uev1;uev2] -> [f1 uev1 ; f2 uev2]
    |_ -> failwith "set_uev_StarDia"
;;

let uev_disj (mrks, uevs) =
    let takemin uev1 uev2 =
        let l1 = uev1#elements in
        let l2 = uev2#elements in
        new FormulaIntSet.set#addlist (filter_map (
            fun (x, d, i) ->
                try
                    let (_, _, j) = List.find (fun (y, _, _) -> y = x) l2
                    in Some (x, d, min i j)
                with Not_found -> None
            )
        l1)
    in
    match mrks, uevs with
    | [mrk1], [uev1] -> uev1
    | [mrk1; mrk2], _ when mrk1 && mrk2 -> uevundef ()
    | [mrk1; mrk2], [_; uev2] when mrk1 && not mrk2 -> uev2
    | [mrk1; mrk2], [uev1; _] when not mrk1 && mrk2 -> uev1
    | _, [uev1; uev2] -> takemin uev1 uev2
    | _ -> failwith "uev_disj"
;;

let mrk_disj mrks =
  match mrks with
  | [mrk1] -> mrk1 (* must be false because of the branch condition *)
  | [mrk1; mrk2] -> mrk1 && mrk2
  | _ -> failwith "mrk_disj"
;;

(* ------- Existential Rules -------------------- *)

let index (dia,node) hcore =
    let hcore = hcore#elements in
    let len = List.length hcore in
    let dia = List.hd dia in
    let nodeset = (new FormulaSet.set)#addlist (node) in
    let rec search n =
        let s = (List.nth hcore n) in
        if dia= fst(s) && nodeset#is_equal (snd(s)) then Some(n)
        else if n < (len - 1) then search (n+1)
        else None
    in
    if len > 0 then search 0 else None
;;

(* true if there is not an element in the list equal to (dia@box) *)
let loop_check (dia, box, hcore) =
    match index (dia,dia@box) hcore with
    | None -> true
    | Some _ -> false
;;

let push (dia, box, hcore) =
    let nodeset = (new FormulaSet.set)#addlist (dia@box)
    in hcore#add (List.hd dia, nodeset)
;;

let isMarked (mrk,uev,dia,box,hcore) =
    if mrk then true
    else
        let len = hcore#length in
        let f = List.hd dia in
        List.exists (function (x, _, i) -> 
            (x = f) && (i >= len) (* && x1 in pre(x2) *) 
        ) uev#elements
;;

let test_ext (mrk, uev, dia, box, hcore) =
    not (isMarked (mrk, uev, dia, box, hcore))
;;

let mrk_ext (mrks, uevs, dia, box, hcore) =
    match mrks,uevs with
    |[mrk1],[uev1] -> isMarked (mrk1, uev1, dia, box, hcore)
    |[_;mrk2],_ -> mrk2
    |_ -> failwith "mrk_ext"
;;

let uev_ext (mrks, uevs, dia, box, hcore) =
    let (a,p) =
        match List.hd dia with
        |formula ( <a1>p1 ) -> (a1,p1)
        |_ -> failwith "uev_ext"
    in
    let filter uev = 
        uevfilter (function
            |(formula ( < ax1 > px1 ), (* formula ( < * ax2 > px2 ) as *) x2, i )
            when ax1 = a && px1 = p (* && x1 in pre(x2) *) &&
            mrk_ext (mrks, uevs, dia, box, hcore) -> Some(formula (px1), x2, i)
            |_ -> None
        ) uev
    in
    match uevs with
    |[uev1] -> filter uev1
    |[uev1;uev2] -> filter (uev1#union uev2)
    | _ -> failwith "uev_ext"
;;

let uev_loop (diax, box, hcore) =
    let fltrbox a = function
        | formula ( [ x ] p ) when x = a -> Some(p)
        | _ -> None
    in
    let getindex box = function
        | formula ( < a > < * b > p ) when a = b ->
                let boxa = filter_map (fltrbox a) box in
                begin match index ([formula (< * b > p)], formula (< * b > p) :: boxa) hcore with
                | None -> failwith "uev_loop checkuev"
                | Some i -> (formula (< * b > p), formula ( < * b > p ), i)
                end
        | _ -> failwith "uev_loop checkuev"
    in
    let dialist = List.map (getindex box) diax in
    (new FormulaIntSet.set)#addlist dialist
;;
