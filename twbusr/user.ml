
open Llist
open Datatype
open Type
open Datatype.Node

open Datatype.Pattern

open Datatype.Tree 
open Datatype.Rule
open Datatype.Strategy
open Datatype.Visit

open Datatype.MatchType
open Datatype.MatchNode
(*
open Datatype.Builder
open Datatype.Backtrack
*)

(*
type nodepattern = ( term_t list -> bool   ) * pattern list
type nodeaction  = ( term_t list -> term_t ) * pattern list
*)
open Basictype

let c = { id = 0; star = Array.make 1 0 }

let add sbl l = List.fold_left (fun s e -> Data.Sublist.add e s) l

let and_p sbl = function
|`Formula(And(_,a,b)) -> add sbl [("A",a);("B",b)]
|_ -> raise FailedMatch

let or_p sbl = function
|`Formula(Or(_,a,b)) -> add sbl [("A",a);("B",b)]
|_ -> raise FailedMatch

let var_p sbl = function
|`Formula(a) -> add sbl [("X",a)]

(*
let andp = `Formula_p(And_p(c, Var_p(c,"A"), Var_p(c,"B")))
let orp = `Formula_p(Or_p(c, Var_p(c,"A"), Var_p(c,"B")))
let varp = `Formula_p(Var_p(c,"X"))
let patt1 = `Formula_p(And_p(c, Var_p(c,""), Var_p(c,"")))
*)

let input1 = `Formula(And(c, Atom(c,"a"), Atom(c,"b")))

let nodepattern = { name = "One"; chained = [andp] ; strict = [varp] ; loose = [] }

class or_rule =
    object
        inherit forall_rule
        
        (* check return an enumeration (the rule context). If the enumeration
         * is empty, then strategy will try an other rule. 
         * *)
        method check node =
            let enum = match_node node nodepattern in
            new rule_context
        method down substlist = failwith ""
        method up nodelist = failwith ""

    end
;;

let matchpatt = function
  |And(_,Or(_,_,_)) -> 1
  |And(_,_,_) -> 2
  |Or(_,_,_) -> 3
  |_ -> failwith "this formula is not mached by any pattern"

let a = new or_rule in
let n = new node in
let s1 = (new Fmap.fmap matchpatt)#add(0,[input1]) in
a#check (n#set "node" (`FMap(s1))) 

