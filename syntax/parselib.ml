(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

let hist_table  : (string, string * string * MLast.expr * MLast.expr option) Hashtbl.t = Hashtbl.create 50 ;;
let const_table : (string, unit) Hashtbl.t = Hashtbl.create 50 ;;
let patt_table  : (Ast.term,string) Hashtbl.t = Hashtbl.create 50 ;;
let rule_table  : (string,string list) Hashtbl.t = Hashtbl.create 50 ;;

let (=~) s re = Str.string_match (Str.regexp re) s 0;;
let get_match i s = Str.matched_group i s
(* binary connective. ei.: A & B *)
let bi_re = "_\\([^_]+\\)_";;
(* unary connective. ie: <> B *)
let u_re =  "\\([^_]+\\)_";;

let test_sep strm =
    match Stream.peek strm with
    | Some(_,s) when s =~ "==+" -> Stream.junk strm; Ast.Invertible
    | Some(_,s) when s =~ "--+" -> Stream.junk strm; Ast.NotInvertible
    | _ -> raise Stream.Failure
;;
let test_sep = Grammar.Entry.of_parser Pcaml.gram "test_sep" test_sep ;;

let test_uid strm =
    match Stream.peek strm with
    | Some (("UIDENT", s)) when not(Hashtbl.mem const_table s) ->
            Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_uid = Grammar.Entry.of_parser Pcaml.gram "test_uid" test_uid ;;

let test_history strm =
    match Stream.peek strm with
    | Some (("UIDENT", s)) when Hashtbl.mem hist_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_history = Grammar.Entry.of_parser Pcaml.gram "test_history" test_history ;;

let test_constant strm =
    match Stream.peek strm with
    | Some (("UIDENT", s)) when Hashtbl.mem const_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_constant = Grammar.Entry.of_parser Pcaml.gram "test_constant" test_constant ;;

let test_variable strm =
    match Stream.peek strm with
    | Some (("LIDENT", s)) when Hashtbl.mem hist_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_variable = Grammar.Entry.of_parser Pcaml.gram "test_variable" test_variable ;;

let new_id =
  let counter = ref 0 in
  fun s ->
      incr counter;
      "__" ^s^ string_of_int !counter
;;

let is_var = function
    |Ast.Var(_) -> true
    |_ -> false
;;

let rec patt_to_string ?(generic=true) = function
    |Ast.Bicon(s,t1,t2) ->
            Printf.sprintf "%s_%s_%s" s
            (patt_to_string ~generic:generic t1)
            (patt_to_string ~generic:generic t2)
    |Ast.Ucon(s,t) ->
            Printf.sprintf "%s_%s" s
            (patt_to_string ~generic:generic t)
    |Ast.Var(id) when generic = false -> id
    |_ -> ""
;;

let add_patt_table _loc name expr =
    let add_rule_table name s =
        try
            let l = Hashtbl.find rule_table name in
            if List.mem s l then ()
            else Hashtbl.replace rule_table name (s::l)
        with Not_found ->
            Hashtbl.add rule_table name [s]
    in
    let s generic = 
        match expr with
        |Ast.Term (Ast.Atom(_)) -> "__atom"
        |Ast.Term (Ast.Const(_)) -> "__const"
        |Ast.Filter("__single",[Ast.Term(p)])
        |Ast.Filter("__empty",[Ast.Term(p)])
        |Ast.Term (Ast.Bicon(_,_,_) as p) 
        |Ast.Term (Ast.Ucon(_,_) as p) ->
                patt_to_string ~generic:generic p
        |_ -> ""
    in
    match expr with
    |Ast.Filter("__single",[Ast.Term(t)])
    |Ast.Filter("__empty",[Ast.Term(t)])
    |Ast.Term (t) ->
            add_rule_table name (s false);
            Hashtbl.replace patt_table t (s true); (s true)
    |_ -> (s true)
;;

let find_patt_table _loc = function
    |Ast.Filter("__single",[Ast.Term(t)])
    |Ast.Filter("__empty",[Ast.Term(t)])
    |Ast.Term (t) ->
            begin try Hashtbl.find patt_table t with Not_found -> "" end
    |_ -> ""
;;

let rec compare_term_patt p1 p2 =
    let rec depth_term_patt = function
        |Ast.Bicon(s,a,b) -> 1 + max (depth_term_patt a) (depth_term_patt b)
        |Ast.Ucon(s,a) -> 1 + (depth_term_patt a)
        |_ -> 0
    in
    let dp1 = depth_term_patt p1 in
    let dp2 = depth_term_patt p2 in
    match p1,p2 with
    |Ast.Bicon(s1,_,_), Ast.Bicon(s2,_,_) ->
            if dp1 = dp2 then compare s1 s2
            else compare dp1 dp2
    |Ast.Ucon(s1,_), Ast.Ucon(s2,_) ->
            if dp1 = dp2 then compare s1 s2
            else compare dp1 dp2
    |_,_ -> 1
;; 

let sort_pattlist l =
    let cmp (s1,t1) (s2,t2) =
        if s1 = s2 then 0
        else compare_term_patt t1 t2
    in
    let rec unique_aux = function
        |[] -> []
        |(s1,t1)::tl ->
                (s1,t1) :: unique_aux (
                    List.filter (fun (s2,_) -> not(s1 = s2)) tl
                    )
    in
    unique_aux (List.sort cmp l)
;;

let list_to_exprlist _loc l =
    List.fold_right (
        fun x l -> <:expr< [ $x$ :: $l$ ] >>
    ) l <:expr< [] >>
;;

let filter_map f l =
    List.fold_left(fun l e ->
        match f e with
        |None -> l
        |Some(e) -> e::l
    ) [] l
;;

let rec unique = function
    |[] -> []
    |h::t -> h:: unique (List.filter (fun x -> not(x = h)) t)
;;

module Option = struct
    let get = function Some x -> x | None -> failwith "Option.get"
    let optlist = function Some l -> l | None -> []
    let is_none = function Some _ -> false | None -> true
end
