
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_", Zero;
  Falsum, Const;
  Verum, Const
END


(* workd if f is in nnf *)
let rec weigth = function
    |term ( a & b ) -> (weigth a) * (weigth b) 
    |term ( a v b ) -> 1 + (weigth a) + (weigth b) 
    |_ -> 0
;;

let cmp a b = Pervasives.compare (weigth a) (weigth b) ;;

(* raughly MOMS : less disjunct at the front *)
let rec order aux = function
    |term ( a & b ) -> 
        let (d1,t1) = aux a in
        let (d2,t2) = aux b in
        let d = d1 * d2 in
        begin match Pervasives.compare d1 d2 with
        |i when i > 0 -> d, term ( t2 & t1 )
        |i when i < 0 -> d, term ( t1 & t2 )
        |_ ->
                begin match Pervasives.compare a b with
                |i when i > 0 -> d, term ( t2 & t1 )
                |i when i < 0 -> d, term ( t1 & t2 ) 
                |_ -> d, t1
                end
        end
    |term ( a v b ) -> 
        let (d1,t1) = aux a in
        let (d2,t2) = aux b in
        let d = 1 + d1 + d2 in
        begin match Pervasives.compare d1 d2 with
        |i when i > 0 -> d, term ( t2 v t1 )
        |i when i < 0 -> d, term ( t1 v t2 )
        |_ ->
                begin match Pervasives.compare a b with
                |i when i > 0 -> d, term ( t2 v t1 )
                |i when i < 0 -> d, term ( t1 v t2 ) 
                |_ -> d, t1
                end
        end
    |_ -> failwith "order"

;;

let nnf f =
    let rec aux = function
        |term ( a & b ) as f -> order aux f
        |term ( ~ ( a & b ) ) -> aux term ( ~ a  v ~ b )
        |term ( a v b ) as f -> order aux f
        |term ( ~ ( a v b ) ) -> aux term ( ~ a & ~ b )
        |term ( a <-> b ) ->
                aux term ( ( a -> b ) & ( b -> a ) )
        |term ( ~ ( a <-> b ) ) ->
                aux term ( ( ~ (a -> b) ) v ( ~ (b -> a) ) )
        |term ( a -> b ) -> aux term ( (~ a) v b )
        |term ( ~ (a -> b) ) -> aux term ( a & (~ b) )
        |term ( ~ ~ a ) -> aux a
        |term ( ~ Atom ) as f -> (0,f)
        |term ( Atom ) as f   -> (0,f)
        |term ( Constant ) as f -> (0,f)
        |term (~ Constant) as f -> (0,f) 
        |f -> failwith (Printf.sprintf "aux:%s" (Twblib.sof(f)))
    in let (_,f') = aux f in f'
;;

(* A[phi] *)
let rec simpl phi a =
    if phi = a then term(Verum)
    else if phi = (nnf (term ( ~ a ))) then term(Falsum)
    else match a with
    |term (~ b)   -> term ( ~ [simpl phi b] )
    |term (b & c) -> term ( [simpl phi b] & [simpl phi c] )
    |term (b v c) -> term ( [simpl phi b] v [simpl phi c] )
    |_ -> a
;;

let inc (idx) = idx + 1 ;;

let rec uniq = function
    |[] -> []
    |h::t -> h:: uniq (List.filter (fun x -> not(x = h)) t)
;;

let addlabel (tl1,tl2) =
    match List.hd tl1,List.hd tl2 with
    |`LabeledFormula(l1,t1),`LabeledFormula(l2,t2) -> uniq(l1@l2)
    |_ -> failwith "backjumping"
;;

let simpbj simpf (tl,sl) =
    open_bt_list (
        List.map( function
            |`LabeledFormula(l,t) ->
                    let (rl,rt) =
                        List.fold_left(fun (il1,a) s ->
                            match List.hd s with
                            |`LabeledFormula(il2,phi) ->
                                let a' = simpf phi a in
                                if a' = a then (il1,a)
                                else (il1@il2,a')
                            |_ -> failwith "simplbj"
                        ) (l,t) sl
                    in `LabeledFormula(uniq rl,rt)
            |_ -> failwith "simpl"
        ) tl
    )
;;

let fixlabel (idx,tl) =
    List.map( function
        |`LabeledFormula(l,t) -> `LabeledFormula(idx::l,t)
        |_ -> failwith "fixlabel"
    ) tl
;;

let backjumping (idx,intlist) = List.mem idx intlist ;;

let mergelabel (intll, status) =
    if status = "Open" then [] else uniq(List.flatten intll)
;;

