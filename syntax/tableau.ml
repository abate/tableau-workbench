(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open ExtLib

let patt_term    = Grammar.Entry.create Pcaml.gram "patt_term";;
let expr_term    = Grammar.Entry.create Pcaml.gram "expr_term";;
let rewrite_patt_term    = Grammar.Entry.create Pcaml.gram "rewrite_patt_term";;
let rewrite_expr_term    = Grammar.Entry.create Pcaml.gram "rewrite_expr_term";;


(* generates fresh ids given a string *)
let new_id = 
  let counter = ref 0 in
  fun s ->
      incr counter;
      "__" ^s^ string_of_int !counter
;;

let hist_table  = Hashtbl.create 50 ;;
let const_table = Hashtbl.create 50 ;;
let patt_table  = Hashtbl.create 50 ;;

(* given a patter, returns an pattern where all lid as
 * substituted with _ *)
let rec remove_lid p = 
    let loc = Token.dummy_loc in
    match p with
    | <:patt< Atom (_,_) >> -> <:patt< _ >>
    | <:patt< Constant($lid:_$,$str:s$) >> when Hashtbl.mem const_table s -> 
            <:patt< Constant(_,_) >>
    | <:patt< $uid:s$ ( $list:pl$ ) >> ->
        let l = List.map (remove_lid) pl in
        <:patt< $uid:s$ ( $list:l$ ) >>
    | <:patt< $lid:s$ >> -> <:patt< _ >>
    | <:patt< $int:i$ >> -> <:patt< _ >>
    | <:patt< _ >> -> <:patt< _ >>
    | _ as p ->
            failwith
            ("remove_lid : parsing error "^
            (Pcaml.string_of Pcaml.pr_patt p))
;;

(* this table is used to generate the matchpattern function
 * out of all ids generate while parsing the rules *)
let add_patt_table l p =
    let patt = remove_lid p in
    try let (s,l) = Hashtbl.find patt_table patt in s
    with Not_found ->
        let s = new_id "patternid" in
        match patt with
        | <:patt< Atom(_,_) >> -> s 
        | <:patt< Constant(_,_) >> -> s
        | <:patt< _ >> -> s
        | _ -> Hashtbl.add patt_table patt (s,l); s
;;    

let list_to_exprlist loc l =
    List.fold_right (
        fun x l -> <:expr< [ $x$ :: $l$ ] >>
    ) l <:expr< [] >>
;;

(* extend the parser with the tokens declared in the 
 * CONNECTIVES part. binary connectives *)
let add_biconn lev op co =
    EXTEND
      patt_term: LEVEL $lev$
        [[ (lx,x) = patt_term; $op$; (ly,y) = patt_term -> 
            ((lx@ly),<:patt< $uid:co$(_,$x$,$y$) >>)
        ]];
      expr_term: LEVEL $lev$
        [[ (lx,x) = expr_term; $op$; (ly,y) = expr_term ->
            let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
            ((lx@ly),<:expr< $uid:co$($nc$,$x$,$y$) >>)
        ]];
        
      rewrite_patt_term: LEVEL $lev$
        [[ x = rewrite_patt_term; $op$; y = rewrite_patt_term -> 
            <:patt< $uid:co$(_,$x$,$y$) >>
        ]];
      rewrite_expr_term: LEVEL $lev$
        [[ x = rewrite_expr_term; $op$; y = rewrite_expr_term ->
            let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
            <:expr< $uid:co$($nc$,$x$,$y$) >>
        ]];

    END;;

(* extend the parser with the tokens declared in the 
 * CONNECTIVES part. unary connectives connectives *)
let add_uconn op co =
    EXTEND
      patt_term: LEVEL "Simple"
        [[ $op$; (lx,x) = patt_term ->
            (lx,<:patt< $uid:co$(_,$x$) >> )
        ]];
      expr_term: LEVEL "Simple"
        [[ $op$; (lx,x) = expr_term ->
            let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
            (lx,<:expr< $uid:co$(nc,$x$) >> )
        ]];
        
      rewrite_patt_term: LEVEL "Simple"
        [[ $op$; x = rewrite_patt_term ->
            <:patt< $uid:co$(_,$x$) >>
        ]];
      rewrite_expr_term: LEVEL "Simple"
        [[ $op$; x = rewrite_expr_term ->
            let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
            <:expr< $uid:co$(nc,$x$) >>
        ]];
    END
;;

let add_muconn op1 op2 co =
    EXTEND
      patt_term: LEVEL "Simple"
      [[ $op1$; i = INT; $op2$; (lx,x) = patt_term ->
            (lx,<:patt< $uid:co$($int:i$,_,$x$) >> )
        ]];
      expr_term: LEVEL "Simple"
      [[ $op1$; i = INT; $op2$; (lx,x) = expr_term ->
            let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
            (lx,<:expr< $uid:co$($int:i$,nc,$x$) >> )
        ]];
        
      rewrite_patt_term: LEVEL "Simple"
      [[ $op1$; i = INT; $op2$; x = rewrite_patt_term ->
            <:patt< $uid:co$($int:i$,_,$x$) >>
        | $op1$; i = LIDENT; $op2$; x = rewrite_patt_term ->
            <:patt< $uid:co$($lid:i$,_,$x$) >>

        ]];
      rewrite_expr_term: LEVEL "Simple"
      [[ $op1$; i = INT; $op2$; x = rewrite_expr_term ->
            let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
            <:expr< $uid:co$($int:i$,nc,$x$) >>
        | $op1$; i = LIDENT; $op2$; x = rewrite_expr_term ->
            let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
            <:expr< $uid:co$($lid:i$,nc,$x$) >>

        ]];

    END
;;

let (=~) s re = Str.string_match (Str.regexp re) s 0;;
let get_match i s = Str.matched_group i s

(* binary connective. ei.: A & B *)
let bi_re = "_\\([^_]+\\)_";;

(* multi modal connective. ie: <a>B *)
let mu_re = "\\([^_]+\\)_\\([^_]+\\)_";;

(* unary connective. ie: <> B *)
let u_re =  "\\([^_]+\\)_";;

(* this is a parser to match an arbitrary number of tokens 
 * and it's used to parse invertible and not invertible rules *)
type rule_t = Inv | NotInv
let test_sep strm =
    match Stream.peek strm with
    | Some(_,s) when s =~ "==+" -> Stream.junk strm; Inv
    | Some(_,s) when s =~ "--+" -> Stream.junk strm; NotInv
    | _ -> raise Stream.Failure
;;
let test_sep = Grammar.Entry.of_parser Pcaml.gram "test_sep" test_sep ;;

let test_variable strm =
    match Stream.peek strm with
    | Some (("LIDENT", s)) when Hashtbl.mem hist_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_variable = Grammar.Entry.of_parser Pcaml.gram "test_variable" test_variable ;;

let test_constant strm =
    match Stream.peek strm with
    | Some (("UIDENT", s)) when Hashtbl.mem const_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_constant = Grammar.Entry.of_parser Pcaml.gram "test_constant" test_constant ;;

let is_variable = function
      ([s],<:expr< $lid:a$ >>) -> true
    | ([s],<:expr< $int:a$ >>) when Hashtbl.mem hist_table s -> true
    | _ -> false
;;

(* generate the code pattern match a set of formulae *)
let expand_set loc ?cond formula l =
    let newid = new_id "exp_set" in
    let is_variable = function
        | <:patt< $lid:a$ >> -> true
        | _ -> false
    in
    let pa1 =
        let l = List.map (fun a -> <:patt< $lid:("l"^(String.lowercase a))$ >>) l 
        in <:patt< ( $list:l$ ) >>
    in
    let pa2 =
        let l = List.map (fun a -> <:patt< $lid:(String.lowercase a)$ >>) l 
        in <:patt< ( $list:l$ ) >>
    in
    let ex1 =
        let l = List.map (
            function 
            |a when a =~ "atom___\\(.*\\)" ->
                    <:expr< `Formula (Atom (nc,$lid:get_match 1 a$)) >>
            |a -> <:expr< `Formula $lid:String.lowercase a$ >>
        ) l 
        in <:expr< ( $list:l$ ) >>
    in
    let ex3 = (* tuple of lists *)
        let l = List.map (fun a ->
            <:expr< [$lid:(String.lowercase a)$ :: $lid:("l"^(String.lowercase a))$ ] >>
        ) l 
        in <:expr< ( $list:l$ ) >>
    in
    let ex4 = (* tuple of empty lists *)
        let l = List.map (fun a -> <:expr< [] >>) l 
        in <:expr< ( $list:l$ ) >>
    in
    let ex5 = (* list of tuple *)
        let l = List.map (
            function
            |a when a =~ "atom___\\(.*\\)" ->
                    let b = [<:expr<$str: (get_match 1 a)$>>;
                    <:expr<$lid:("l"^(String.lowercase a))$ >>] in
                    <:expr< ( $list:b$ ) >>
            |a -> 
                    let b = [<:expr<$str:a$>>;<:expr<$lid:("l"^(String.lowercase a))$ >>] in
                    <:expr< ( $list:b$ ) >>
            ) l 
        in list_to_exprlist loc l
    in
    let ex6 = 
        if is_variable formula then
            [(<:patt<`Formula($formula$)>>,None,ex1);
             (<:patt< _>>,None,<:expr<failwith ($str:newid$^": type mismatch")>>)
            ]
        else
            [(<:patt<`Formula($formula$)>>,None,ex1);
             (<:patt<`Formula(_)>>,None,<:expr< raise FailedMatch>>);
             (<:patt< _>>,None,<:expr<failwith ($str:newid$^": type mismatch")>>)
            ]
    in
    let ex7 =
        if Option.is_none cond then <:expr< True >>
        else <:expr< $lid:Option.get cond$(fl) >>
    in
    (newid,
    <:str_item<
        value $lid:newid$ sbl fl =
            let __rec = fun [ $list:ex6$ ] in 
            if $ex7$ then
                let $pa1$ = List.fold_left (
                    fun [ $pa1$ ->
                        fun [ el -> 
                            let $pa2$ = __rec el in $ex3$ 
                        ]
                    ]
                ) $ex4$ fl
                in Sbl.add sbl $ex5$
            else raise FailedMatch
    >>)
;;

(* generate the code to pattern match a principal formula *)
let expand_single loc ?cond formula l =
    let newid = new_id "exp_single" in
    let is_variable = function
        | <:patt< $lid:a$ >> -> true
        | _ -> false
    in
    let ex1 =
        let l = List.map (
            function 
            |a when a =~ "atom___\\(.*\\)" ->
                    <:expr< `Formula (Atom (nc,$lid:get_match 1 a$)) >>
            |a -> <:expr< `Formula $lid:String.lowercase a$ >>
        ) l 
        in list_to_exprlist loc l
    in
    let ex2 =
        let l = List.map (
            function
            |a when a =~ "atom___\\(.*\\)" ->
                    <:expr< $str: (get_match 1 a)$ >>
            |a -> <:expr< $str: a$>>
        ) l
        in list_to_exprlist loc l
    in
    let ex3 =
        if Option.is_none cond then <:expr< True >>
        (* this List.hd cannot be empty because it is a principal formula *)
        else <:expr< $lid:Option.get cond$(List.hd fl) >>
    in
    let pex1 = (
        <:patt< `Formula($formula$) >>, None,
        <:expr<
            List.map2 (fun [ f ->
                fun [ s -> 
                    try if Sbl.mem sbl s f then [] else raise FailedMatch
                    with [ Not_found -> [f] ] 
                ]
            ]) $ex1$ $ex2$ >>
            )
    in
    let pex2 = (<:patt< `Formula(_) >> ,None , <:expr< raise FailedMatch >>)
    in
    let pex3 = (
        <:patt< _ >>, None,
        <:expr< failwith ($str:newid$^": type mismatch") >>
        )
    in
    (* all this to avoid a warning *)
    let l = if is_variable formula then [pex1;pex3] else [pex1;pex2;pex3]
    in
    (newid,
    <:str_item<
        value $lid:newid$ sbl fl =
            let __rec = fun [ $list:l$ ] in
            if $ex3$ then
                (* this List.hd cannot be empty because it is a principal
                 * formula *)
                Sbl.add sbl (List.combine $ex2$ (__rec (List.hd fl)))
            else raise FailedMatch
    >>)
;;

(* generate the code to pattern match a generic variable *)
let expand_set_anon loc ?cond formula a =
    let newid = new_id "exp_anon" in
    let ex1 =
        if Option.is_none cond then <:expr< True >>
        else <:expr< $lid:Option.get cond$(fl) >>
    in
    (newid,
    <:str_item< value $lid:newid$ sbl fl =
        if $ex1$ then 
            Sbl.add sbl [($str: a$,fl)]
        else raise FailedMatch
    >>)
;;

type cond_t =
    | Single
    | Const
    | NoCond
    | Cond of string
    | SingCond of string

type act_t = 
    | NoAct
    | Act of string
    
type branch_t =
    | Forall of bt
    | Exists of bt
    | User   of bt
(*    | Cond   of string *)
and bt = (string list * ( MLast.expr * act_t ) ) list list


(* this is the monster that builds formulae *)
let expand_build_formula loc (sl,formula) newid =
    let ex1 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:expr<$lid:"h"^string_of_int !i$>>
        ) (List.unique sl) in <:expr< ( $list:l$ ) >>
    in
    let ex2 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:expr<$lid:"t"^string_of_int !i$>>
        ) (List.unique sl) in <:expr< ( $list:l$ ) >>
    in
    (* XXX: make possible to build formulae from histories *)
    let ex3 = 
        let l = List.map (fun a ->
            if Hashtbl.mem hist_table a then
                <:expr< hist#find $str: a$ >>
            else
                <:expr< Data.Substlist.find $str:a$ sbl >>
        ) (List.unique sl) in <:expr< ( $list:l$ ) >>
    in
    let ex4 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:expr<$lid:"l"^string_of_int !i$#elements>>
        ) (List.unique sl) in <:expr< ( $list:l$ ) >>
    in
    let pa2 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            try
                let (s,t,_,_) = Hashtbl.find hist_table a in
                <:patt< `$lid:s$($lid:"l"^string_of_int !i$) >>
            with Not_found -> 
                <:patt<`Mtlist($lid:"l"^string_of_int !i$) >>
        ) (List.unique sl) in <:patt< ( $list:l$ ) >>
    in
    let pa3 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:patt< [ $lid:"h"^string_of_int !i$ :: $lid:"t"^string_of_int !i$ ] >>
        ) (List.unique sl) in <:patt< ( $list:l$ ) >>
    in
    let pa4 = 
        let l = List.map (fun a -> <:patt< `Formula $lid:String.lowercase a$ >>
        ) (List.unique sl) in <:patt< ( $list:l$ ) >>
    in
    let pa5 = (* tuple of empty lists *)
        let l = List.map (fun a -> <:patt< [] >>) (List.unique sl) 
        in <:patt< ( $list:l$ ) >>
    in
    (* this is to avoid "Warning: this match case is unused." in split *)
    let ex5 =
        let l = [
            (pa3,None,<:expr< [ $ex1$::(split $ex2$) ] >>);
            (pa5,None,<:expr< [] >>)
            ]
        in
        if List.length sl = 1 then l
        else (l@[
                (<:patt< _ >>,None,
                <:expr< failwith ($str:newid$^" something about the list") >>)
                ])
    in
    <:expr<
        try
            let rec split = fun [ $list:ex5$ ]
            in
            match $ex3$ with
            [ $pa2$ ->
                    List.map (fun
                        [$pa4$ -> `Formula $formula$
                        | _ -> failwith ($str:newid$^" type node allowed" )]
                    ) (split $ex4$)
            | _ -> failwith ($str:newid$^" type node allowed") ]
        with [ Not_found -> failwith ($str:newid$^" something wrong") ] 
    >>
;;

let expand_build_formula_var loc ?(den=false) (sl,formula) newid = 
    (* there must be exactly one element in this list *)
    let ex3 =
        match sl with
        | [a] ->
            begin
            try
                match Hashtbl.find hist_table a with
                | (_,_,"History",_) -> <:expr< hist#find $str:a$ >>
                | (_,_,"Variable",_) ->
                        <:expr<
                        let varhist = List.nth varl ( $formula$ - 1 )
                        in varhist#find $str:a$ 
                        >>
                | _ -> failwith "expand_build_formula_var"
             with Not_found ->
                 <:expr< Data.Substlist.find $str:a$ sbl >>
            end
        | _ -> failwith "expand_build_formula_var"
    in
    let pa2 =
        try
            match Hashtbl.find hist_table (List.hd sl) with
                  (_,"Single","Variable",_) -> <:patt< `Set($lid:"l"$) >>
                | (s,t,_,_) -> <:patt< `$lid:s$($lid:"l"$) >>
        with Not_found -> <:patt<`Mtlist($lid:"l"$) >>
    in
    let ex2 =
        try
            match Hashtbl.find hist_table (List.hd sl) with
            | (s,"Single","Variable",_) ->
                <:expr<
                match l#elements with 
                [[`$lid:s$ ($lid:"el"$)] -> el
                |_ -> failwith ($str:newid$^" singleton")
                ]
                >>
            | _ -> <:expr< l >>
        with Not_found -> <:expr< l#elements >>
    in
    let ex4 =
        try
            match Hashtbl.find hist_table (List.hd sl) with
            | (s,"Single","Variable",e) ->
                    if Option.is_none e then
                        failwith
                        ((List.hd sl)^
                        " : conditional branching used but default not specified")
                    else <:expr< $Option.get e$ >>
            | (s,t,"Variable",e) -> <:expr< (new $uid:s$.$lid:t$) >>
            | _ -> <:expr< failwith "this is impossible" >>
        with Not_found -> <:expr< failwith "this is impossible" >>
    in
    <:expr<
        try match $ex3$ with
            [$pa2$ -> $ex2$
            |_ -> failwith ($str:newid$^" type node allowed") ]
        with
        [Not_found -> failwith ($str:newid$^" something wrong")
        |Failure "nth" -> $ex4$ ]
    >>
;;
 
let expand_condlistel loc (act,func,args) =
    let newid = new_id "history_condition" in
    let (ex2, ex3) =
        List.split
            (List.map (function 
                 ([],formula) -> (<:expr< $formula$ >>,None)
                |(sl,formula) ->
                    let newid = new_id "build" in
                    let ex = 
                    (* special case to handle arbitrary expressions as argument *)
                        if is_variable (sl,formula) then
                            expand_build_formula_var loc (sl,formula) newid
                        else expand_build_formula loc (sl,formula) newid
                    in (<:expr< $lid:newid$ >>,Some(<:patt<$lid:newid$>>,ex))
            ) args
        )
    in
    let ex4 = <:expr< $lid:func$ ( $list:ex2$ ) >> in
    let ex5 =
        let l = List.filter_map (fun e -> e) ex3 in
        if (args = []) || (l = []) then <:expr< $ex4$ >>
        else <:expr< let $list:l$ in $ex4$ >>
    in
    (<:expr< $lid:newid$ >> ,
    <:str_item< value $lid:newid$ sbl hist varl = $ex5$ >>)
;;

let expand_condlist loc cl =
    if Option.is_none cl then ([],[])
    else
        let (idl,strl) =
            List.split (
                List.map (fun a ->
                    expand_condlistel loc a
                ) (Option.get cl)
            )
        in (idl, strl)
;;

let expand_constant loc p l =
    let newid = new_id "exp_constant" in
    let s = List.hd l in
    let ex =
        <:str_item<
        value $lid:newid$ sbl fl =
            let f =
                try List.find (fun [ `Formula $p$ -> True | _ -> False ] ) fl
                with [ Not_found -> raise FailedMatch ]
            in Sbl.add sbl [ ($str:s$,[f]) ]
        >>
    in (newid,ex)
;;

let expand_rule_num loc (stringlist,formulalist) cl =
    let pl = ref [] in
    let sl = ref [] in
    let add_pattlist = function
        |_,"" -> ()
        |Single,s | SingCond(_),s | Const,s ->  pl := !pl@[s]
        |_,s -> sl := !sl@[s]
    in
    let str_items = 
        List.map2 (fun l (p,c) ->
            (* generate code for a principal formula,
             * a set or an anonimous set with or without
             * local side conditions *)
            let (id,exp) = 
                match c,p with
                |Single,_ -> expand_single loc p l
                |Const,_ -> expand_constant loc p l
                |SingCond(c),_ -> expand_single loc ~cond:c p l
                
                (* XXX: List.hd can throw an exception ... *)
                |Cond(c),<:patt< $lid:_$ >> ->
                        expand_set_anon loc ~cond:c p (List.hd l)
                |_,<:patt< $lid:_$ >> -> expand_set_anon loc p (List.hd l)
                        
                |Cond(c),_ -> expand_set loc ~cond:c p l
                |_ -> expand_set loc p l
            in
            (* add the pattern to a hashtable used to build the matchpattern
             * function *)
            let s = add_patt_table l p in
            let paid = new_id "pattern" in
            (* if the pattern is just a variable then the index must be an
             * empty string, otherwise the string used by matchpattern to index
             * formulae. if the pattern is an atom then the index is __atom *)
            let pattexp = 
                match p with
                | <:patt< $lid:_$ >> -> 
                        <:str_item<
                        value $lid:paid$ = NodePattern.newpatt "" $lid:id$ >>
                | <:patt< Atom($lid:_$,$lid:_$) >> -> 
                        <:str_item<
                        value $lid:paid$ = NodePattern.newpatt "__atom" $lid:id$ 
                        >>
                | <:patt< Constant($lid:_$,$str:_$) >> -> 
                        <:str_item<
                        value $lid:paid$ = NodePattern.newpatt "__const" $lid:id$ 
                        >>
                | _ ->
                        <:str_item<
                        value $lid:paid$ = NodePattern.newpatt $str:s$ $lid:id$ 
                        >>
            in
            (* add a pattern to a list in relation to the type c *)
            add_pattlist (c,paid) ;
            <:str_item< declare $list:[exp;pattexp]$ end>>
        ) stringlist formulalist
    in
    let pl = list_to_exprlist loc
        (List.map (fun e -> <:expr< $lid:e$ >> ) !pl )
    in
    let sl = list_to_exprlist loc
        (List.map (fun e -> <:expr< $lid:e$ >> ) !sl )
    in
    let (condidl, condstrl) = expand_condlist loc cl in
    let cl = list_to_exprlist loc condidl in
    let l = <:expr< UserRule.check node ( $list:[pl;sl]$ ) $cl$ >>
    in (l, str_items@condstrl)
;;

(* this function expand the function to build a new denominator *)
let expand_action loc sl (formula,action) = 
    let newid = new_id "exp_action" in
    let ex = 
        if is_variable (sl,formula) then
            expand_build_formula_var loc ~den:true (sl,formula) newid
        else expand_build_formula loc (sl,formula) newid
    in
    (* if the pattern is just a variable the function to implement the action is
     * much simpler and we have a special case for it *)
    let action =
        match action with
        | NoAct -> <:expr< $ex$ >>
        | Act(a) -> <:expr< $lid:a$($ex$) >>
    in
    (newid, <:str_item< value $lid:newid$ sbl hist varl = $action$ >>)
;;

(* this function expand the arguments and the function to 
 * execute side actions (history manipulation) for one denominator *)
let expand_actionlistel loc (act,func,args) =
    let newid = new_id "history_action" in
    let (ex2,ex3) =
        List.split
            (List.map (function
                (* special case to handle arbitrary expressions as argument *)
                 ([],formula) -> (<:expr< $formula$ >>,None)
                |(sl,formula) ->
                    let newid = new_id "build" in
                    let ex = 
                        if is_variable (sl,formula) then
                            expand_build_formula_var loc (sl,formula) newid
                        else expand_build_formula loc (sl,formula) newid
                    in (<:expr< $lid:newid$ >>,Some(<:patt<$lid:newid$>>,ex))
            ) args
        )
    in
    let ex4 =
        match act with
        |None -> <:expr< let _ = ($lid:func$ ( $list:ex2$ ) ) in hist >>
        |Some(h) ->
                try
                    match Hashtbl.find hist_table h with
                    (s,"Single","Variable",_) ->
                        <:expr<
                        ( $str:h$ ,
                        (`Set (
                            (new Set.set)#add (
                                `$uid:s$ (
                                    $lid:func$ ( $list:ex2$ )
                                    )
                                )
                            )
                        )
                        )
                        >>
                    |(s,_,_,_) -> 
                        <:expr<
                        ($str:h$,
                        (`$lid:s$ ( ($lid:func$ ( $list:ex2$ ))) )
                        )
                        >>
                with Not_found ->
                    failwith ("expand_actionlist: "^h^" history not declared")
    in
    let ex5 =
        let l = List.filter_map (fun e -> e) ex3 in
        if args = [] || l = [] then <:expr< $ex4$ >>
        else <:expr< let $list:l$ in $ex4$ >>
    in
    (<:expr< $lid:newid$ >>,
    <:str_item< value $lid:newid$ sbl hist varl = $ex5$ >>)
;;

let expand_actionlist loc dl hl =
    if Option.is_none hl then
        (* XXX: horrible way to make sure to have a
         * the same number of history actions and den actions *)
        (List.map (fun _ -> []) dl,[])
    else
        let (idl,strl) =
            List.split (
                List.map (fun al ->
                    List.split (
                        List.map (fun a ->
                            expand_actionlistel loc a
                        ) al
                    )
                ) (Option.get hl)
            )
        in (idl, List.flatten strl)
;;

let expand_branchlist loc dl bll =
    if Option.is_none bll then
        (* XXX: horrible way to make sure to have a
         * the same number of history actions and den actions *)
        (List.map (fun _ -> []) (List.tl dl),[])
    else
        let (idl,strl) =
            List.split (
                List.map (fun al ->
                    List.split (
                        List.map (fun a ->
                            expand_condlistel loc a
                        ) al
                    )
                ) (Option.get bll)
            )
        in (idl, List.flatten strl)
;;

let expand_sythlist loc bt =
    if Option.is_none bt then ([], [])
    else
        let (idl,strl) =
            List.split (
                List.map (fun a ->
                    expand_actionlistel loc a 
                ) (Option.get bt)
            )
        in (idl, strl)
;;

let expand_rule_den loc t dl hl bll bt =
    let expand dl tl hl =
        let is_axiom = function
            | <:expr< $lid:"axiom"$ >> -> true
            |_ -> false
        in
        let is_reserved = function
            | <:expr< $lid:"axiom"$ >>
            | <:expr< $lid:"close"$ >>
            | <:expr< $lid:"unsat"$ >> 
            | <:expr< $lid:"open"$ >>
            | <:expr< $lid:"sat"$ >> -> true
            |_ -> false
        in
        let exp_reserved l = 
            let (_,(f,_)) = try List.find (fun (sl,(f,_)) -> is_reserved f) l
                    with Not_found -> failwith "exp_reserved : impossible"
            in
            match f with
            | <:expr< $lid:"close"$ >>
            | <:expr< $lid:"unsat"$ >> -> <:expr< $str:"Closed"$ >>
            | <:expr< $lid:"open"$ >>
            | <:expr< $lid:"sat"$ >> -> <:expr< $str:"Open"$ >>
            | _ -> failwith "exp_reserved : impossible"
        in
        let __exp dl =
            let (al,strld) =
                List.split (List.filter_map (fun (sl,(f,act)) ->
                    if is_reserved f then None
                    else
                        let (id,exp) = expand_action loc sl (f,act) in
                        let s = new_id "action" in
                        let pattexp =
                            <:str_item<
                            value $lid:s$ = NodePattern.newact "" $lid:id$ >>
                        in
                        Some(
                            <:expr< $lid:s$ >>,
                            <:str_item< declare $list:[exp;pattexp]$ end>>
                        )
                    ) dl
                )
            in
            let al = list_to_exprlist loc al 
            in (al,strld)
        in
        let (actidl, actstrl) = expand_actionlist loc (dl::tl) hl in
        let (firstal,strld) = __exp dl in
        (* first node of the action list *)
        let firsthl = list_to_exprlist loc (List.hd actidl) in
        let h = <:expr< (n,$firstal$,$firsthl$) >> in
        let (nextal,strl) = List.split (
            List.map2(fun dl hl ->
                let (al,strld) = __exp dl in
                let hl = list_to_exprlist loc hl in 
                (<:expr< (n#copy,$al$,$hl$) >>, strld)
            ) tl (List.tl actidl)
        ) in
        (* all the others *)
        let tl = list_to_exprlist loc nextal in
        let exp = 
            (* if the pattern contain a keyword and the tail is empty then
             * it must be an axiom. *)
            if nextal = [] && 
            (List.exists (fun (sl,(f,_)) -> is_reserved f) dl)
            then
                if (List.exists (fun (sl,(f,_)) -> is_axiom f) dl)
                then <:expr< UserRule.down_axiom name context (fun a -> a) >>
                else
                    let axiom_t = exp_reserved dl in
                    <:expr< 
                    let status varhist =
                        match varhist#find "status" with
                        [`Set(s) ->
                            varhist#add "status" 
                            (`Set((s#empty)#add (`String($axiom_t$))))
                        |_ -> failwith "down_axiom"
                        ]
                    in
                    UserRule.down_axiom name context status >>
            else
                (* otherwise we check is the rule is invertible or not *)
                match t with
(*                | NotInv when not(nextal = []) ->
                        failwith "Not Invertible rule cannot branch" *)
                | Inv ->
                        <:expr<
                        UserRule.down_explicit name context
                        (fun [ n -> [ $h$ :: $tl$ ] ] ) 
                        >>
                | NotInv when not(nextal = []) ->
                        <:expr<
                        UserRule.down_explicit name context
                        (fun [ n -> [ $h$ :: $tl$ ] ] ) 
                        >>
                | NotInv ->
                        <:expr<
                        UserRule.down_implicit name context $firstal$ $firsthl$ 
                        >>
        in
        (exp,List.flatten (strld::strl)@actstrl)
    in
    let (sythidl, synthstrl) = expand_sythlist loc bt in
    let openrule = <:expr< UserRule.is_open >> in
    let closerule = <:expr< UserRule.is_closed >> in
    match dl,t with
    |Forall (dl::[]),NotInv ->
            let (exp,strl) = expand dl [] hl in
            let (branchidl, branchstrl) = expand_branchlist loc [dl] bll in
            let bidl = List.map (
                fun l -> list_to_exprlist loc (openrule::l) ) branchidl
            in
            let up =
                <:expr< UserRule.up_explore_simple context treelist 
                $list_to_exprlist loc sythidl$ $list_to_exprlist loc bidl$ >>
            in (up ,exp, strl@synthstrl@branchstrl)
    |Exists (dl::tl),NotInv ->  
            let (exp,strl) = expand dl tl hl in
            let (branchidl, branchstrl) = expand_branchlist loc (dl::tl) bll in
            let bidl = List.map (
                fun l -> list_to_exprlist loc (openrule::l) ) branchidl
            in
            let up =
                <:expr< UserRule.up_explore_simple context treelist 
                $list_to_exprlist loc sythidl$ $list_to_exprlist loc bidl$ >>
            in (up ,exp, strl@synthstrl@branchstrl)
    |Forall ([dl]),Inv ->
            let (exp,strl) = expand dl [] hl in
            let up =
                <:expr< UserRule.up_explore_linear context treelist 
                $list_to_exprlist loc sythidl$ >>
            in (up ,exp, strl@synthstrl)
    |Forall (dl::tl),Inv ->
            let (exp,strl) = expand dl tl hl in
            let (branchidl, branchstrl) = expand_branchlist loc (dl::tl) bll in
            let bidl = List.map (
                fun l -> list_to_exprlist loc (closerule::l) ) branchidl
            in
            let up =
                <:expr< UserRule.up_explore_simple context treelist 
                $list_to_exprlist loc sythidl$ $list_to_exprlist loc bidl$ >>
            in (up ,exp, strl@synthstrl@branchstrl)
    |User   (dl::tl),_ ->
            let (exp,strl) = expand dl tl hl in
            let (branchidl, branchstrl ) = expand_branchlist loc (dl::tl) bll in
            let bidl = List.map (fun l -> list_to_exprlist loc l ) branchidl in
            let up =
                <:expr< UserRule.up_explore_simple context treelist
                $list_to_exprlist loc sythidl$ $list_to_exprlist loc bidl$ >>
            in (up ,exp, strl@synthstrl@branchstrl)
    |_ -> failwith "expand_rule_den"
;; 

let expand_rule_back loc bt = <:expr< () >> ;;

let expand_rule_class loc s (nl,fl) dl cl hl bl bt t =
    let (pl,strln)    = expand_rule_num loc (nl,fl) cl in
    let (up,al,strld) = expand_rule_den loc t dl hl bl bt in
    strln@strld@
    [<:str_item< 
        class $lid:(String.lowercase s)^"_rule"$ = 
                object
                inherit Rule.rule;
                
                value name = $str:s$;
                method check node = $pl$ ;
                method down context = $al$ ;
                method up context treelist = $up$ ;
                end 
    >>
    ]
;;

(* generets the code for the function matchpatt. it adds two
 * special cases for atoms and a failwith entry *)
let expand_matchpatt loc =
    let l = Hashtbl.fold (fun p (s,l) strl -> 
        (<:patt< `Formula($p$) >>,None,<:expr< $str:s$ >>)::strl
        ) patt_table []
    in
    let atom = (<:patt< `Formula(Atom(_,_)) >>, None, <:expr< "__atom" >>)
    and const = (<:patt< `Formula(Constant(_,_)) >>, None, <:expr< "__const" >>)
    in
    let fail = ( <:patt< _ >>, None,
        <:expr< failwith "this formula is not mached by any pattern" >>
    )
    in
    <:str_item< Logic.__matchpatt.val := 
        Some(((fun [ $list:l@[atom;const;fail]$ ]) : Basictype.mixtype -> string ))
    >>
;;

let expand_parser loc connlist =
    let l = List.filter_map(function
    | (v,s,r) when s =~ mu_re ->
            Some(
                <:expr< ( $str:r$,[$str:(get_match 1 s)$;$str:(get_match 2 s)$], `Muconn (
                fun [ (i,a) -> $lid:v$(i,Basictype.nc,a) ]) ) >>
            )
    | (v,s,r) when s =~ u_re ->
            Some(
                <:expr< ( $str:r$,[$str:(get_match 1 s)$], `Uconn (
                fun [ a -> $lid:v$(Basictype.nc,a) ]) ) >>
            )
    | (v,s,r) when s =~ bi_re ->
            Some (
                <:expr< ( $str:r$,[$str:(get_match 1 s)$], `Biconn ( 
                fun [ (a,b) -> $lid:v$(Basictype.nc,a,b) ]) ) >>
            )

    | (v,"Const",_) -> Some ( <:expr< ( "Const",[$str:v$], `Const ) >> )
           
            
    | (_,s,_) -> failwith (s^" is not a valid pattern")
    ) connlist
    in 
    let l = list_to_exprlist loc l in
    <:str_item< Logic.__inputparser.val :=
        Some(InputParser.buildParser $l$) >>

let expand_printer loc connlist =
    let l = List.filter_map(function
        | (v,s,r) when s =~ mu_re ->
                Some(<:patt< ( $lid:v$(i,nc,a) ) >>,
                None,
                <:expr< Printf.sprintf
                $str:"("^(get_match 1 s)$
                ^(string_of_int i)^
                $str:(get_match 2 s)^" %s)"$
                (pr_aux a) >>)
        | (v,s,r) when s =~ u_re ->
                Some(<:patt< ( $lid:v$(nc,a)) >>,
                None,
                <:expr< Printf.sprintf
                $str:"("^((get_match 1 s)^" %s)")$ (pr_aux a) >>)
        | (v,s,r) when s =~ bi_re ->
                Some(<:patt< ( $lid:v$(nc,a,b) ) >>,
                None,
                <:expr< Printf.sprintf
                $str:("(%s "^(get_match 1 s)^" %s)")$ (pr_aux a) (pr_aux b) >>)
        | (v,"Const",_) -> None
        | (_,s,_) -> failwith (s^" pr_aux error")
    ) connlist
    in
    let default =
        <:patt< _ >> ,
        None,
        <:expr< failwith "this printer prints formulae only" >>
    in
    let atom = <:patt< Atom(nc,s) >> , None, <:expr< s >> in
    let const = <:patt< ( Constant(nc,a) ) >>, None, <:expr< a >>
    in
    <:str_item< Logic.__printer.val := 
        Some (let rec pr_aux = fun [ $list:List.rev([default;atom;const]@l)$ ] in
        pr_aux )
    >>
;;

type 'a tree =
    |Star of 'a tree
    |Seq of 'a tree list
    |Choice of 'a tree list
    |Rule of 'a
;;

let expand_strategy loc tree = []
(*
let expand_default_strategy loc =
    let str = <:expr< value __strategy = new Strategy.strategy "start" >> in
    let sat = 
        List.map (fun id ->
            <:expr< __strategy#add newid (R new $lid:id^"_rule") newid nextid >>
        ) inv_rule_list
    in
    let star = strategy#add "star1" S "start" "trans";
    let trans =
        List.map (fun id ->
            <:expr< __strategy#add newid (R new $lid:id^"_rule") newid nextid >>
        ) notinv_rule_list
    in
    <:expr< $list:sat$
    *)
    
(* this function creates the history list. it also add the synth history
 * "status" if it has not been user defined *)
let expand_history loc l =
    let histlist = 
        if not(List.exists (fun (s,_,_,ht,_) ->
            (s = "status") && (ht = "Variable") ) l )
        then ("status","String","Single","Variable",Some(<:expr< "Open" >>))::l
        else l
    in 
    let expr_list = List.map (function 
        | (v,s,"Single","Variable",df) ->
            let n =
                if Option.is_none df then <:expr< (new Set.set) >>
                else <:expr< ((new Set.set)#add (`$lid:s$ $Option.get df$)) >>
            in <:expr< ($str:v$, `Set $n$, Variable) >>
        | (v,s,t,ht,df) ->
                <:expr< ($str:v$,`$lid:s$ (new $uid:s$ . $lid:t$), $uid:ht$) >>
    ) histlist
    in
    List.iter (fun (v,s,t,ht,df) ->
        Hashtbl.replace hist_table v (s,t,ht,df)
    ) histlist;
    list_to_exprlist loc expr_list
;;

let expand_exit loc (func,args) = 
    let newid = new_id "history_condition" in
    let (ex2, ex3) =
        List.split
            (List.map (function 
                 ([],formula) -> (<:expr< $formula$ >>,None)
                |(sl,formula) ->
                    let newid = new_id "build" in
                    let ex = 
                    (* special case to handle arbitrary expressions as argument *)
                        if is_variable (sl,formula) then
                            expand_build_formula_var loc (sl,formula) newid
                        else expand_build_formula loc (sl,formula) newid
                    in (<:expr< $lid:newid$ >>,Some(<:patt<$lid:newid$>>,ex))
            ) args
        )
    in
    let ex4 = <:expr< $lid:func$ ( $list:ex2$ ) >> in
    let ex5 =
        let l = List.filter_map (fun e -> e) ex3 in
        if (args = []) || (l = []) then <:expr< $ex4$ >>
        else <:expr< let $list:l$ in $ex4$ >>
    in <:expr< fun [ varl -> $ex5$ ] >>
;;

let expand_preamble loc =
    let stl = [
        "Llist";"Data";"Basictype";"Comptypes";
        "Datatype";"Datatype.ConcreteNode";"Datatype.Node";
        "Datatype.NodePattern";
        "Datatype.Partition";"Datatype.Rule";"Datatype.RuleContext";
        "Datatype.Strategy";"Datatype.Visit";"UserRule";"Tree"]
    in
    let stl = List.map (fun s -> <:str_item< open $uid:s$ >> ) stl in
    <:str_item< declare $list:stl$ end >>
;;
    
EXTEND
GLOBAL : Pcaml.str_item Pcaml.patt Pcaml.expr patt_term expr_term
rewrite_expr_term rewrite_patt_term; 
  Pcaml.str_item: [[
    "CONNECTIVES"; clist = LIST1 connective SEP ";"; "END" ->
      List.iter (function
          |(v,s,r) when s =~ bi_re -> add_biconn r (get_match 1 s) v
          |(v,s,r) when s =~ mu_re -> 
                  add_muconn (get_match 1 s) (get_match 2 s) v
          |(v,s,r) when s =~ u_re -> add_uconn (get_match 1 s) v
          |(v,"Const",_) -> Hashtbl.replace const_table v ()
          |(_,s,_) -> failwith (s^" is not a valid pattern")
      ) clist ;
      let preamble = expand_preamble loc in
      let pa = expand_parser loc clist in
      let pr = expand_printer loc clist in 
      <:str_item< declare $list:[preamble;pa;pr]$ end >>
    |"HISTORIES"; hlist = LIST1 history SEP ";"; "END" ->
            let l = expand_history loc hlist in
            <:str_item< Logic.__history_list.val := Some($l$) >>
(*    |"VARIABLES"; vlist = LIST1 variable SEP ";"; "END" ->
            let l = expand_history loc vlist in
            <:str_item< Logic.__history_list.val := Some($l$) >> *)
    |"TABLEAU"; l = LIST1 rule; "END" ->
            let l = (expand_matchpatt loc)::l in 
            (* if the history is empty, then I've to add status to it *)
            if not(Hashtbl.mem hist_table "status") then
                let hl = expand_history loc [] in
                let h = <:str_item< Logic.__history_list.val := Some($hl$) >>
                in <:str_item< declare $list:(h::l)$ end >>
            else
                <:str_item< declare $list:l$ end >>
    |"PP"; OPT ":="; e = Pcaml.expr ->
            <:str_item< Logic.__pp.val := Some($e$) >>
    |"NEG"; OPT ":="; e = Pcaml.expr ->
            <:str_item< Logic.__neg.val := Some($e$) >>
    |"EXIT"; OPT ":="; f = LIDENT; "("; args = LIST0 arguments SEP ","; ")" ->
            let ex = expand_exit loc (f,args) in
            <:str_item< Logic.__exit.val := Some($ex$) >> 
    |"STRATEGY"; s = strategy ->
            (* <:str_item< declare $list:expand_strategy loc s$ end >> *)
            <:str_item< Logic.__strategy.val := Some(strategy) >>
  ]];

  connective: [[ 
        v = UIDENT; ","; s = STRING; ","; r = UIDENT -> (v,s,r)
      | v = UIDENT; ","; "Const" -> (v,"Const","")
  ]];

  history: [
      [ v = UIDENT; ":"; s = UIDENT; "."; t = LIDENT -> (v,s,t,"History", None)
      | v = LIDENT; ":"; s = UIDENT; "."; t = LIDENT -> (v,s,t,"Variable", None)
      | v = LIDENT; ":"; s = UIDENT; 
      e = OPT [ "default"; e = Pcaml.expr LEVEL "simple"-> e ] ->
              (v,s,"Single","Variable", e)
  ]];

(*  variable: [
      [ v = LIDENT; ":"; s = UIDENT; "."; t = LIDENT -> (v,s,t,"Variable", None)
      | v = LIDENT; ":"; s = UIDENT; 
      e = OPT [ "default"; e = Pcaml.expr LEVEL "simple"-> e ] ->
              (v,s,"Single","Variable", e)
  ]]; *)

  strategy:
  [ "One" LEFTA
      [ s1 = strategy LEVEL "Simple"; ";";
        s = LIST1 strategy LEVEL "Simple" SEP ";" -> Seq (s1::s)
      | s1 = strategy LEVEL "Simple"; "|";
        s = LIST1 strategy LEVEL "Simple" SEP "|" -> Choice (s1::s)
      | s = strategy LEVEL "Simple"; "*" -> Star ( s )
      | s1 = strategy LEVEL "Simple" -> Seq([s1])
      ]
  | "Simple" NONA
      [ "("; s = strategy; ")" -> s
      | lid = UIDENT -> Rule( lid^"_rule")
      | uid = UIDENT; "."; lid = UIDENT -> Rule(uid^ lid^"_rule")
      ]
  ];

  rule: [[
      "RULE";
      id = UIDENT; (nl,n) = num; t = test_sep; dl = denlist; 
      cl = OPT condition;
      hl = OPT actionlist;
      bt = OPT backtracklist;
      bl = OPT branchlist;
      "END" ->
          let rl = expand_rule_class loc id (nl,n) dl cl hl bl bt t in 
          <:str_item< declare $list:rl$ end >>
  ]];

  condition: [[
      "COND"; OPT "["; l = LIST1 usercond SEP ";"; OPT "]" -> l
  ]];

  actionlist: [[
      "ACTION"; OPT "["; l = LIST1 action SEP ";"; OPT "]" -> l
  ]];

  branchlist: [[
      "BRANCH"; OPT "["; l = LIST1 branch SEP ";"; OPT "]" -> l
  ]];

  backtracklist: [[
      "BACKTRACK"; OPT "["; l = LIST1 useract SEP ";"; OPT "]" -> l
  ]];

  branch: [[
      OPT "["; l = LIST0 usercond SEP ";"; OPT "]" -> l
  ]];

  action: [[
      OPT "["; l = LIST0 useract SEP ";"; OPT "]" -> l
  ]];
  
  useract: [[
      f = LIDENT; "("; args = LIST0 arguments SEP ","; ")" -> (None,f,args)
      | s = [ s = UIDENT -> s | s = test_variable -> s ] ; ":="; 
        f = LIDENT; "("; args = LIST0 arguments SEP ","; ")" -> (Some(s),f,args)
  ]];
  
  usercond: [[
      f = LIDENT; "("; args = LIST0 arguments SEP ","; ")" -> (None,f,args)
  ]];

  arguments: [[
        ex = expr_term -> ex
      | ex = Pcaml.expr LEVEL "simple" -> ([],ex)
  ]];
  
  (* Forall of (string list * expr) list list *)
  denlist: [[
       d = den; "|";  dl = den_forall -> Forall(d::dl)
      |d = den; "||"; dl = den_exists -> Exists(d::dl)
      |d = den; "|||"; dl = den_exists -> User(d::dl)
      |d = den -> Forall([d])
  ]];

  den_forall: [[ dl = LIST1 den SEP "|" -> dl ]];
  den_exists: [[ dl = LIST1 den SEP "||" -> dl ]];
  
  (* ( string list * (expr * cond_t)) list *)
  den: [[al = LIST1 denformula SEP ";" -> al ]];
  
  (* ( string list list * (expr * cond_t) list ) *)
  num: [[ pl = LIST1 numformula SEP ";" -> List.split pl ]]; 
  
  (* (expr * cond_t) *)
  numformula: [[
       (* single formula *)
       "{"; (s,p) = patt_term; "}" -> (s,(p,Single))

      | x = test_constant ->
              ([x], (<:patt< Constant(nc,$str:x$) >>, Const))
       
       (* set with condition *)
      |c = LIDENT; OPT "("; (s,p) = patt_term; OPT ")" -> (s,(p,Cond(c))) 
    
      (* single formula with condition *)
      |c = LIDENT; OPT "("; "{";
        (s,p) = patt_term; "}"; OPT ")" -> (s,(p,SingCond(c)))
    
      (* set with no conditions *)
      |(s,p) = patt_term           -> (s,(p,NoCond))
  ]];
  
  (* ( string list * (expr * cond_t)) *)
  denformula: [[
       (s,p) = expr_term -> (s,(p,NoAct)) 
      |a = LIDENT; OPT "("; (s,p) = expr_term; OPT ")" -> (s,(p,Act(a))) 
  ]];
 
  expr_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ "."; x = LIDENT ->
              let nc = <:expr< Basictype.newcore 1 [|0|] >> in
              ([x], <:expr< Atom($nc$,$lid:x$)>>)
      | x = test_variable; "("; i = INT; ")" -> ([x], <:expr< $int:i$ >>)
      | x = test_constant ->
              let nc = <:expr< Basictype.newcore 1 [|0|] >> in
              ([x], <:expr< Constant($nc$,$str:x$)>>)
      | x = UIDENT -> ([x], <:expr< $lid:String.lowercase x$ >> )
      | "("; p = expr_term; ")" -> p
      ] 
    ];

  patt_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ "."; x = LIDENT -> (["atom___"^x], <:patt< Atom(nc,$lid:x$) >>)
      | x = UIDENT -> ([x], <:patt< $lid:String.lowercase x$>>)
      | "("; p = patt_term; ")" -> p
      ] 
    ];
    
  Pcaml.expr: LEVEL "simple"  
      [[ "term"; "("; e = rewrite_expr_term; ")" ->
          <:expr< $e$ >> 
(*      | "atm"; "("; x = LIDENT; ")" ->
              let nc = <:expr< Basictype.newcore 1 [|0|] >> in
              (<:expr< Atom($nc$,$lid:x$)>>)
      | "atm"; "("; x = UIDENT; ")" ->
              let nc = <:expr< Basictype.newcore 1 [|0|] >> in
              (<:expr< Atom($nc$,$str:x$)>>) 
      | "const"; "("; x = LIDENT; ")" ->
              let nc = <:expr< Basictype.newcore 1 [|0|] >> in
              (<:expr< Constant($nc$,$lid:x$)>>) *)
      | "const"; "("; x = test_constant ; ")" ->
              let nc = <:expr< Basictype.newcore 1 [|0|] >> in
              (<:expr< Constant($nc$,$str:x$)>>) 
  ]];
  Pcaml.patt: LEVEL "simple"
      [[ "term"; "("; p = rewrite_patt_term; ")"->
          <:patt< $p$ >>
(*      | "atm"; "("; x = LIDENT; ")" ->
                <:patt< Atom(nc,$lid:x$) >>
      | "const"; "("; x = LIDENT; ")"->
                <:patt< Constant(nc,$lid:x$) >>
      | "const"; "("; x = test_constant; ")"->
                <:patt< Constant(nc,$str:x$) >>
                *)
  ]];

  rewrite_expr_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ x = LIDENT -> <:expr< $lid:x$ >>
(*      | x = test_constant ->
              let nc = <:expr< Basictype.newcore 1 [|0|] >> in
              <:expr< Constant($nc$,$str:x$) >> *)
      | x = UIDENT ->
          let nc = <:expr< Basictype.newcore 1 [|0|] >> in
          <:expr< Atom($nc$,$str:x$)>>
      | "("; p = rewrite_expr_term; ")" -> p
      ] 
    ];

  rewrite_patt_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ x = LIDENT -> <:patt< $lid:x$>>
      | "." ; x = LIDENT -> <:patt< Atom(_,$lid:x$)>>
      | x = test_constant -> <:patt< Constant(_,$str:x$) >>
      | "Constant" -> <:patt< Constant(_,_) >>
      | "("; p = rewrite_patt_term; ")" -> p
      ] 
    ];

END
