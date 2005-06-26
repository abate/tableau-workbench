
open Basictype
open Listobj
open Sets
open Fmap
open Setofsets
open Setoftupleset

type mixlist = [
    |`L of mixtype listobj
    |`S of set
    |`SS of setofset
    |`SoTS of setoftupleset
    |`FMap of fmap
    |mixtype
]

type 'a patt = Var__p of string | Const__p of 'a
type 'a listobj_p = List of 'a patt * 'a listobj_p | Empty

type mixlist_p = [
    |`L_p of (Basictype.mixtype_p listobj_p) patt
    |`S_p of set patt
    |`SS_p of setofset patt
    |`SoTS_p of setoftupleset patt
    |`FMap_p of Basictype.mixtype_p
    |mixtype_p
]

let match_type_fmap set pattern =
    match set,pattern with
    |`FMap(s), (#mixtype_p as p) -> s#get p
    |#mixlist, #mixlist_p -> raise FailedMatch 
    | _ -> raise FailedMatch

(* FIXME: type matter match here is too loose.
 * the signature should be more succinct *)
let rec match_mixtype_listobj sbl set pattern = 
    match set,pattern with
(*    |s,List(Const__p(c), Empty) when ->  *)
    |s,List(Const__p(c), p) ->
            match_mixtype_listobj sbl s#tail p ; sbl
            
(*    |s,List(Var__p(v), Empty) when -> *)

(* !!! XXX: !!! here I coerce the value of s#head (that is
 * of type mixtype) to its supertype mixlist *)
    |s,List(Var__p(v), p) ->
            match_mixtype_listobj 
            (Substlist.add v (s#head :> mixlist) sbl)
            s#tail p
            
    | _ -> raise FailedMatch

(* This function is a proxy that returns a sbl from a store *)
let match_type sbl set pattern =
    match set,pattern with
    |`L(s),`L_p(Const__p(c)) -> match_mixtype_listobj sbl s c
    |`L(s),`L_p(Var__p(v)) -> Substlist.add v set sbl
    
    |`S(s),`S_p(Const__p(c)) -> raise FailedMatch
    |`S(s),`S_p(Var__p(c)) -> raise FailedMatch
    |`SS(s),`SS_p(Const__p(c)) -> raise FailedMatch
    |`SS(s),`SS_p(Var__p(c)) -> raise FailedMatch
    |`SoTS(s),`SoTS_p(Const__p(c)) -> raise FailedMatch
    |`SoTS(s),`SoTS_p(Var__p(c)) -> raise FailedMatch

    |#mixtype, #mixtype_p -> Basictype.match_type sbl set pattern
    |#mixlist, #mixlist_p -> raise FailedMatch 
    
    | _ -> raise FailedMatch
;;
