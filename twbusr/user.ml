
open Llist
open Data

open Basictype
open Comptypes

open Datatype
open Datatype.Node
open Datatype.NodePattern
open Datatype.Partition

open Datatype.Tree 
open Datatype.Rule
open Datatype.Strategy
open Datatype.Visit

let c = Basictype.newcore 0 (Array.make 1 0)

let open_mt v = (v : mixtype list :> [> mixtype] list )

(* XXX: this operation is very expensive *)
(* search = O(log n)
 * concatenation = O(n m)
 * insertion = O(log n) *)
let add sbl l =
    List.fold_left (
        fun s (k,v) ->
            let oldlist =
                try Data.Substlist.find k s 
                with Not_found -> []
            in
            (* XXX this coercion is important ! *)
            Data.Substlist.add k (oldlist@(open_mt v)) s
        ) sbl l

let match_unary sbl f a l =
    let l1 = List.fold_left (
        fun l1 el -> let a = f el in a::l1
        ) [] l
    in add sbl [(a,l1)]

let match_binary sbl f a b l =
    let (l1,l2) = List.fold_left (
        fun (l1,l2) el ->
            let (a,b) = f el in (a::l1,b::l2)
        ) ([],[]) l
    in add sbl [(a,l1);(b,l2)]

(* A & B *)
let and_p sbl fl =
    let and_rec = function
        |`Formula(And(_,a,b)) -> (`Formula a,`Formula b)
        |#mixlist -> raise FailedMatch
    in match_binary sbl and_rec "A" "B" fl

(* A v B *)
let or_p sbl fl = 
    let or_rec = function
        |`Formula(Or(_,a,b)) -> (`Formula a,`Formula b)
        |#mixlist -> raise FailedMatch
    in match_binary sbl or_rec "A" "B" fl

let not_p sbl fl = 
    let not_rec = function
        |`Formula(Not(_,a)) -> (`Formula a)
        |#mixlist -> raise FailedMatch
    in match_unary sbl not_rec "A" fl

let var_p sbl fl = 
    let var_rec = function
        |`Formula(_) as a -> a
        |#mixlist -> raise FailedMatch
    in match_unary sbl var_rec "X" fl

let andp = newpatt 2 and_p
let varp = newpatt 0 var_p

let input1 = open_mt [(`Formula(And(c, Atom(c,"a"), Atom(c,"b"))))]

let nodepattern = { pname = "One"; chained = [andp] ; strict = [varp] ; loose = [] }

let action_a1 sbl = Data.Substlist.find "A" sbl
let action_a2 sbl = Data.Substlist.find "B" sbl
let action_a3 sbl = Data.Substlist.find "X" sbl
let action_a4 sbl =
    List.map (fun el ->
        match el with
        |`Formula(a) -> `Formula(Not(c,a))
        |#mixlist -> raise FailedMatch
    ) (Data.Substlist.find "B" sbl)

let a1 = newact 0 action_a1
let a2 = newact 0 action_a2
let a3 = newact 0 action_a3
let a4 = newact 4 action_a4

let nodeaction = { aname = "One"; action = [a1;a2;a3;a4] }

let matchpatt = function
  |`Formula(And(_,Or(_,_,_),_)) -> 1
  |`Formula(And(_,_,_)) -> 2
  |`Formula(Or(_,_,_)) -> 3
  |`Formula(Not(_,_)) -> 4
  |#mixlist -> failwith "this formula is not mached by any pattern"
;;

class or_rule =
    object
        inherit forall_rule
        
        (* check return an enumeration (the rule context). If the enumeration
         * is empty, then strategy will try an other rule. 
         * *)
        method check node =
            let enum = match_node node nodepattern in
            if Enum.is_empty enum then print_endline "bugger"
            else print_endline "ok !!" ; 
            new rule_context
        method down node = Leaf(node)
        method up nodelist = failwith ""
    end
;;

let a = new or_rule in
let n = new node in
let s1 = (new Fmap.fmap matchpatt)#addlist input1 in
a#check (n#set "One" (`FMap(s1)))

