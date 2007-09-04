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

let index flist hcore = 
  let hcore = hcore#elements in
  let len = List.length hcore in
  let nodeset = (new FormulaSet.set)#addlist flist in
  let rec search n =
    if nodeset#is_equal (List.nth hcore n) then Some n
    else if n < (len - 1) then search (n+1)
    else None
  in
  if len > 0 then search 0 else None

let uevundef () = new FormulaIntSet.set

let doNextChild_disj (mrk, uev) = mrk || (not uev#is_empty)

let uev_disj (mrks, uevs, p) = 
  let excl uev p = 
    let p = List.hd p in
    try
      let pair = List.find (fun (f, _) -> f = p) uev#elements in
      uev#del pair
    with Not_found -> uev
  in
  let takemin uev1 uev2 =
    let l1 = uev1#elements in
    let l2 = uev2#elements in
    (new FormulaIntSet.set)#addlist
      (filter_map 
         (fun (x, i) ->
           try
             let (_, j) = List.find (fun (y,_) -> y = x) l2 in
             Some(x, min i j)
           with Not_found -> None
         ) l1
      )
  in
  match (mrks, uevs) with
  | ([mrk1], [uev1])  -> uev1
  | ([mrk1; mrk2], _) when mrk1 && mrk2 -> uevundef ()
  | ([mrk1; mrk2], [uev1; _]) when (not mrk1) && mrk2 -> excl uev1 p
  | ([mrk1; mrk2], [_; uev2]) when mrk1 && (not mrk2) -> uev2
  | (_, [uev1; uev2]) -> takemin (excl uev1 p) uev2
  | _ -> failwith "uev_disj"

let mrk_disj mrks =
  match mrks with
  | [mrk1] -> mrk1 (* must be false because of the branch condition *)
  | [mrk1; mrk2] -> mrk1 && mrk2
  | _ -> failwith "mrk_disj"




(* true if there is not an element in the list equal to (dia@box) *)
let loop_check (dia, box, hcore) = 
  match index (dia@box) hcore with
  | None -> true
  | Some _ -> false

let push (dia, box, hcore) = 
  let nodeset = (new FormulaSet.set)#addlist (dia@box) 
  in hcore#add nodeset
;;

let memo f =
    let cache = Hashtbl.create 8 in
    let contains = Hashtbl.mem cache in
    let get = Hashtbl.find cache in
    let put = Hashtbl.replace cache in
    fun arg ->
        if not (contains arg) then
            put arg (f arg);
        get arg
;;

let isMarked mrk uevl dia box hcore =
    let aux (mrk,uevl,dia,box,hcore) =
        if mrk then true
        else
            let len = hcore#length in
            let chkloop f (x, i) = (x = f) && (i >= len) in
            List.exists (fun f -> List.exists (chkloop f) uevl) (dia@box)
    in memo aux (mrk,uevl,dia,box,hcore)
;;

let test_ext (mrk, uev, dia, box, hcore) = not (isMarked mrk (uev#elements) dia box hcore)

let uev_ext (mrks, uevs, diax, box, hcore) =
  let dia = List.hd diax in
  let mrk1 = List.hd mrks in
  let l1 = (List.hd uevs)#elements in
  if isMarked mrk1 l1 diax box hcore then uevundef ()
  else if List.length uevs = 1 then
    (new FormulaIntSet.set)#addlist
      (filter_map 
         (fun (x, i) ->
           match x with
           | formula (E a U d) when x = dia -> Some (x, i)
           | formula (A a U d) when List.mem x box -> Some (x, i)
           | _ -> None
         ) l1
      )
  else
    let mrk2 = List.nth mrks 1 in
    if mrk2 then uevundef ()
    else
      let l2 = (List.nth uevs 1)#elements in
      let uev = 
        (new FormulaIntSet.set)#addlist
          (filter_map 
             (fun (x, i) ->
               match x with
               | formula (E a U d) when x = dia -> Some (x, i)
               | formula (A a U d) when List.mem x box ->
                   begin try
                     let (_, j) = List.find (fun (y, _) -> y = x) l2 in
                     Some (x, max i j)
                   with Not_found -> Some(x, i) end
               | _ -> None
             ) l1
          )
      in
      uev#addlist
        (filter_map 
           (fun (x, i) ->
             match x with
             | formula (E a U d) -> Some (x, i)
             | formula (A a U d) ->
                 if List.exists (fun (y, _) -> y = x) l1 then None
                 else Some (x, i)
             | _ -> failwith "uev_ext"
           ) l2
        )

let mrk_ext (mrks, uevs, dia, box, hcore) = 
  let mrk1 = List.hd mrks in
  let l1 = (List.hd uevs)#elements in
  if isMarked mrk1 l1 dia box hcore then true
  else if List.length mrks = 1 then false
  else List.nth mrks 1


let uev_loop (diax, box, hcore) = 
  let getindex dia =
    match index (dia::box) hcore with
    | None -> failwith "uev_loop checkuev"
    | Some i -> (dia, i)
  in
  let fltrEU (x, _) =
    match x with
    | formula (E a U d) -> true
    | _ -> false
  in
  let fltrAU = function
    | formula (A a U d) -> true
    | _ -> false
  in
  let dialist = List.map getindex diax in
  let maxlvl = List.fold_left (fun m (_, i) -> max m i) 0 dialist in
  let eulist = List.filter fltrEU dialist in
  let aulist = List.filter fltrAU box in
  let aulist = List.map (fun x -> (x, maxlvl)) aulist in
  (new FormulaIntSet.set)#addlist (eulist@aulist)
