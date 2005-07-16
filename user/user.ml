
open Llist
open Data

open Basictype
open Comptypes

open Datatype
open Datatype.NodeType
open Node
open Datatype.Node

open Datatype.NodePattern
open Datatype.HistPattern
open Datatype.Partition

open Tree 
open Datatype.Rule
open Datatype.Strategy
open Datatype.Visit

open UserRule
open Datatype.RuleContext

let nc = Basictype.newcore 1 [|0|]

let open_mt v = (v : mixtype list :> [> mixtype] list )
type sbl = Comptypes.mixlist Data.Substlist.t

let print_sbl sbl = 
    Substlist.iter ( fun k e ->
        print_endline k ;
        print_endline (Comptypes.string_of_mixlist e)
    ) sbl 
;;


let add (sbl : sbl) l =
  List.fold_left (
      fun s (k,v) ->
              try
                  begin
                      match Data.Substlist.find k s with
                      |`L(l) -> Data.Substlist.add k (`L(l#addlist v)) s
                      |`S(l) -> Data.Substlist.add k (`S(l#addlist v)) s
                      |#Comptypes.mixlist -> failwith "add type node allowed"
                  end
              with Not_found ->  (
                  Data.Substlist.add k (`L((new Mtlist.listobj)#addlist v)) s )
      ) sbl l

(* return true if the pattern p is not in the sbl or if
 * the pattern p is in the sbl and the formula f matches
 *)
let mem sbl p f =
    try
        match Data.Substlist.find p sbl with
        |`L(l) -> l#mem f
        |#Comptypes.mixlist -> failwith "add type node allowed"
    with Not_found -> raise Not_found
      
let match_unary sbl f a l =
    let l1 = List.fold_left (
        fun l1 el ->
            let a = f el in a::l1
        ) [] l
    in add sbl [(a,l1)]

let match_binary sbl f a b l =
    let (l1,l2) = List.fold_left (
        fun (l1,l2) el ->
            let (a,b) = f el in (a::l1,b::l2)
        ) ([],[]) l
    in add sbl [(a,l1);(b,l2)]

(* A v B *)
let or_p sbl fl =
    let and_rec = function
        |`Formula(Or(_,a,b)) -> (`Formula a,`Formula b)
        |`Formula(_) -> raise FailedMatch 
        |_ -> failwith "or_p: type mismatch"
    in match_binary sbl and_rec "A" "B" fl

(* A & B *)
let and_p sbl fl =
    let and_rec = function
        |`Formula(And(_,a,b)) -> (`Formula a,`Formula b)
        |`Formula(_) -> raise FailedMatch
        |_ -> failwith "and_p: type mismatch"
    in match_binary sbl and_rec "A" "B" fl

(* ~ p *)
let not_p sbl fl =
    let not_rec = function
        |`Formula(Not(_,a)) ->
                begin
                    let f = (`Formula a) in
                    try if mem sbl "P" f then []
                        else raise FailedMatch
                    with Not_found -> [f]
                end
        |`Formula(_) -> raise FailedMatch
        |_ -> failwith "and_p: type mismatch"
    in add sbl [("P",not_rec (List.hd fl))]

let p_p sbl fl = 
    let p_rec = function
        |`Formula(a) ->
                begin
                    let f = (`Formula a) in
                    try if mem sbl "P" f then []
                        else raise FailedMatch
                    with Not_found -> [f]
                end
        |_ -> failwith "and_p: type mismatch"
    in add sbl [("P",p_rec (List.hd fl))]

let var_p sbl fl = add sbl [("X",fl)]
let hist_p sbl s = Data.Substlist.add "H" (List.hd s) sbl

let andp = NodePattern.newpatt "2" and_p
let orp = NodePattern.newpatt "3" or_p
let varp = NodePattern.newpatt "" var_p
let pp = NodePattern.newpatt "" p_p
let notp = NodePattern.newpatt "4" not_p

let histp = HistPattern.newpatt "H" hist_p


let na1_a sbl = 
    try
        match (Data.Substlist.find "A" sbl), (Data.Substlist.find "B" sbl) with
        |`L(l1),`L(l2) ->
                let l =
                    List.map2 (fun a b ->
                        match a,b with
                        |`Formula(a),`Formula(b) -> `Formula((Or(nc,a,b)))
                        |_ -> failwith "na type node allowed"
                    ) l1#elements l2#elements
                in l 
        |_ -> failwith "na1 type node allowed"
    with Not_found -> failwith "na"

let na2_a a sbl = 
    try
        match (Data.Substlist.find a sbl) with
        |`L(l) -> l#elements
        |_ -> failwith "na2 type node allowed"
    with Not_found -> failwith "na2"

let na1 = NodePattern.newact "2" na1_a
let na2 = NodePattern.newact "" (na2_a "A")
let na3 = NodePattern.newact "" (na2_a "B")
let na4 = NodePattern.newact "" (na2_a "X")

let matchpatt : Basictype.mixtype -> string = function
  |`Formula(And(_,Or(_,_,_),_)) -> "1"
  |`Formula(And(_,_,_)) -> "2"
  |`Formula(Or(_,_,_)) -> "3"
  |`Formula(Not(_,_)) -> "4"
  |`Formula(Atom(_)) -> "5"
  |_ -> failwith "this formula is not mached by any pattern"
;;

(* return an enumeration (the rule context). If the enumeration
 * is empty or the sbl is empty, the strategy will try an other rule. *)
let match_all node (pl,sl,ll) hl =
    let (map,hist) = node#get in
    let enum = match_node map (pl,sl,ll) in
    let (sbl,newmap) = match_hist enum hist map hl in
    let newnode = node#set (newmap,hist) in
    let _ = print_endline (map#to_string) in
    let _ = print_endline "---------------" in
    let _ = print_endline (newmap#to_string) in
    let _ = print_endline "---------------" in
    let _ = print_sbl sbl in
    new context (enum,sbl,newnode)

let action_all node sbl al =
    let (map,hist) = node#get in
    let newmap = Build.build_node map sbl al in
    (*let newhist = Build.build_hist node sbl na1 in *)
    node#set (newmap,hist)

let rec make_llist sbl = function
    |[] -> Empty
    |(node,al)::t -> LList(action_all node sbl al, lazy(make_llist sbl t))

    
class and_rule =
    object
        inherit linear_rule

        method check node = 
            print_endline "check and" ;
            match_all node ([andp],[varp],[]) []
            
        method down node context = 
            print_endline "down and" ;
            let (enum,sbl,newnode) = context#get in
            let ll = make_llist sbl [(newnode,[na3;na2;na4])] in
            Tree(ll)
    end
;;

class or_rule =
    object
        inherit forall_rule

        method check node =
            print_endline "check or" ;
            match_all node ([orp],[varp],[]) []
            
        method down node context =
            print_endline "down or" ;
            let (enum,sbl,newnode) = context#get in
            let ll = make_llist sbl [(newnode,[na2;na4]);(newnode#copy,[na3;na4])]
            in Tree(ll)
    end
;;


class closed_axiom =
    object
        inherit linear_rule

        method check node = 
            print_endline "check axiom" ;
            match_all node ([pp;notp],[varp],[]) []
            
        method down node context =
            print_endline "down axiom" ;
            let (enum,sbl,newnode) = context#get in
            print_sbl sbl;
            Leaf(newnode#set_status Data.Closed)
    end
;;

let input1 = open_mt [
    (`Formula(And(nc, Atom(nc,"a"), Atom(nc,"b"))));
    (`Formula(Or(nc, Atom(nc,"a"), Atom(nc,"b"))))
            ] ;;

let input2 = open_mt [
    (`Formula(Not(nc,Atom(nc,"a"))));
    (`Formula(Atom(nc,"a")));
    (`Formula(Atom(nc,"b")));
    (`Formula(Atom(nc,"a")));
    (`Formula(Atom(nc,"c")))
            ] ;;

let andr = new and_rule ;;
let orr = new or_rule ;;
let cla = new closed_axiom;;

let m1 = (new Fmap.map matchpatt)#addlist (input2@input1) ;;
let h1 = (new Hmap.map)#add "H" (`S((new Set.set)#addlist input1)) ;;

let n = new node (m1,h1) ;;

Strategy.add "start" (R(andr)) "start" "a";;
Strategy.add "a" (R(orr)) "a" "b" ;;
Strategy.add "b" (R(cla)) "b" "end" ;;
Strategy.add "end" E "end" "end" ;;

let start = Strategy.newstate "start" ;;
Visit.visit start n;;

