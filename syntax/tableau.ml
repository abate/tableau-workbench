(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open ExtLib

let patt_term    = Grammar.Entry.create Pcaml.gram "patt_term";;
let expr_term    = Grammar.Entry.create Pcaml.gram "expr_term";;

(* generates fresh ids given a string *)
let new_id = 
  let counter = ref 0 in
  fun s ->
      incr counter;
      "__" ^s^ string_of_int !counter
;;

(* given a patter, returns an pattern where all lid as
 * substituted with _ *)
let rec remove_lid = 
    let loc = Token.dummy_loc in 
    function
    | <:patt< Atom(_,_) >> -> <:patt< _ >>
    | <:patt< $uid:s$ ( $list:pl$ ) >> ->
        let l = List.map (remove_lid) pl in
        <:patt< $uid:s$ ( $list:l$ ) >>
    | <:patt< $lid:s$ >> -> <:patt< _ >>
    | <:patt< $int:i$ >> -> <:patt< _ >>
    | <:patt< _ >> -> <:patt< _ >>
    | _ as p -> failwith "remove_lid : parsing error" 
;;

let hist_table = Hashtbl.create 50 ;;
let patt_table = Hashtbl.create 50 ;;

(* this table is used to generate the matchpattern function
 * out of all ids generate while parsing the rules *)
let add_patt_table l p =
    let patt = remove_lid p in
    try let (s,l) = Hashtbl.find patt_table patt in s
    with Not_found ->
        let s = new_id "pattern" in
        match patt with
        | <:patt< _ >> -> s
        | <:patt< Atom(_,_) >> -> s
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
    | Some(_,s) when s =~ "==+" -> Stream.junk strm; NotInv
    | Some(_,s) when s =~ "--+" -> Stream.junk strm; Inv
    | _ -> raise Stream.Failure
;;
let test_sep = Grammar.Entry.of_parser Pcaml.gram "test_sep" test_sep ;;

(* generate the code pattern match a set of formulae *)
let expand_set loc ?cond formula l =
    let newid = new_id "exp_set" in
    let is_variable = function
        | <:patt< $lid:a$ >> -> true
        | _ -> false
    in
    let pa1 =
        let l = List.map (fun a -> <:patt< $lid:("l"^a)$ >>) l 
        in <:patt< ( $list:l$ ) >>
    in
    let pa2 =
        let l = List.map (fun a -> <:patt< $lid:a$ >>) l 
        in <:patt< ( $list:l$ ) >>
    in
    let ex1 =
        let l = List.map (
            function 
            |a when a =~ "atom___\\(.*\\)" ->
                    <:expr< `Formula (Atom (nc,$lid:get_match 1 a$)) >>
            |a -> <:expr< `Formula $lid:a$ >>
        ) l 
        in <:expr< ( $list:l$ ) >>
    in
    let ex3 = (* tuple of lists *)
        let l = List.map (fun a ->
            <:expr< [$lid:a$ :: $lid:("l"^a)$ ] >>
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
                    let b = [<:expr<$str:String.uppercase (get_match 1 a)$>>;
                    <:expr<$lid:("l"^a)$ >>] in
                    <:expr< ( $list:b$ ) >>
            |a -> 
                    let b = [<:expr<$str:String.uppercase a$>>;<:expr<$lid:("l"^a)$ >>] in
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
    let ex1 =
        let l = List.map (
            function 
            |a when a =~ "atom___\\(.*\\)" ->
                    <:expr< `Formula (Atom (nc,$lid:get_match 1 a$)) >>
            |a -> <:expr< `Formula $lid:a$ >>
        ) l 
        in list_to_exprlist loc l
    in
    let ex2 =
        let l = List.map (
            function
            |a when a =~ "atom___\\(.*\\)" ->
                    <:expr< $str:String.uppercase (get_match 1 a)$ >>
            |a -> <:expr< $str:String.uppercase a$>>
        ) l
        in list_to_exprlist loc l
    in
    let ex3 =
        if Option.is_none cond then <:expr< True >>
        (* this List.hd cannot be empty because it is a principal formula *)
        else <:expr< $lid:Option.get cond$(List.hd fl) >>
    in
    (newid,
    <:str_item<
        value $lid:newid$ sbl fl =
            let __rec = fun
                [`Formula($formula$) -> 
                            List.map2 (fun [ f ->
                                fun [ s -> 
                                    try if Sbl.mem sbl s f then [] else raise FailedMatch
                                    with [ Not_found -> [f] ] 
                                ]
                            ]) $ex1$ $ex2$ 
                |`Formula(_) -> raise FailedMatch
                |_ -> failwith ($str:newid$^": type mismatch") ]
            in
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
            Sbl.add sbl [($str:String.uppercase a$,fl)]
        else raise FailedMatch
    >>)
;;

type cond_t =
    | Single
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

let is_variable = function
    | <:expr< $lid:a$ >> -> true
    | _ -> false
;;

(* this is the monster that builds formulae *)
let expand_build_formula loc (sl,formula) newid =
    let ex1 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:expr<$lid:"h"^string_of_int !i$>>
        ) sl in <:expr< ( $list:l$ ) >>
    in
    let ex2 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:expr<$lid:"t"^string_of_int !i$>>
        ) sl in <:expr< ( $list:l$ ) >>
    in
    (* XXX: make possible to build formulae from histories *)
    let ex3 = 
        let l = List.map (fun a ->
            if Hashtbl.mem hist_table (String.uppercase a) then
                <:expr< hist#find $str:String.uppercase a$ >>
            else
                <:expr< Data.Substlist.find $str:String.uppercase a$ sbl >>
        ) sl in <:expr< ( $list:l$ ) >>
    in
    let ex4 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:expr<$lid:"l"^string_of_int !i$#elements>>
        ) sl in <:expr< ( $list:l$ ) >>
    in
    let pa2 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            try
                let (s,t) = Hashtbl.find hist_table (String.uppercase a) in
                <:patt< `$lid:s$($lid:"l"^string_of_int !i$) >>
            with Not_found -> 
                <:patt<`Mtlist($lid:"l"^string_of_int !i$) >>
        ) sl in <:patt< ( $list:l$ ) >>
    in
    let pa3 = 
        let i = ref 0 in
        let l = List.map (fun a ->
            incr i;
            <:patt< [ $lid:"h"^string_of_int !i$ :: $lid:"t"^string_of_int !i$ ] >>
        ) sl in <:patt< ( $list:l$ ) >>
    in
    let pa4 = 
        let l = List.map (fun a -> <:patt< `Formula $lid:a$ >>
        ) sl in <:patt< ( $list:l$ ) >>
    in
    let pa5 = (* tuple of empty lists *)
        let l = List.map (fun a -> <:patt< [] >>) sl 
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
        with [ Not_found -> failwith $str:newid$ ] 
    >>
;;

let expand_build_formula_var loc ?(hist=false) (sl,formula) newid = 
    let ex3 = 
        let l = List.map (fun a ->
            if Hashtbl.mem hist_table (String.uppercase a) then
                <:expr< hist#find $str:String.uppercase a$ >>
            else
                <:expr< Data.Substlist.find $str:String.uppercase a$ sbl >>
        ) sl in <:expr< ( $list:l$ ) >>
    in
    let pa2 =
        try
            (* there must be exactly one element in this list *)
            let (s,t) = Hashtbl.find hist_table (String.uppercase (List.hd sl)) in
            <:patt< `$lid:s$($lid:"l"$) >>
        with Not_found -> <:patt<`Mtlist($lid:"l"$) >>
    in
    let ex2 = if hist then <:expr< l >> else <:expr< l#elements >> 
    in
    <:expr<
        try match $ex3$ with
            [$pa2$ -> $ex2$
            |_ -> failwith ($str:newid$^" type node allowed") ]
        with [Not_found -> failwith ($str:newid$^" something wrong")]
    >>
;;
 
let expand_condlistel loc (act,func,args) =
    let newid = new_id "history_condition" in
    let (ex2,ex3) =
        List.split
            (List.map (fun (sl,formula) ->
                let newid = new_id "build" in
                let ex = 
                    if is_variable formula then
                        expand_build_formula_var ~hist:true loc (sl,formula) newid
                    else expand_build_formula loc (sl,formula) newid
                in (<:expr< $lid:newid$ >>,(<:patt<$lid:newid$>>,ex))
            ) args
        )
    in
    let ex4 = <:expr< $lid:func$ ( $list:ex2$ ) >> in
    let ex5 =
        if args = [] then <:expr< $ex4$ >>
        else <:expr< let $list:ex3$ in $ex4$ >>
    in
    (<:expr< $lid:newid$ >> ,
    <:str_item< value $lid:newid$ sbl hist = $ex5$ >>)
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

let expand_rule_num loc (stringlist,formulalist) cl =
    let pl = ref [] in
    let sl = ref [] in
    let add_pattlist = function
        |_,"" -> ()
        |Single,s ->  pl := s::!pl
        |_,s -> sl := s::!sl
    in
    let str_items = 
        List.map2 (fun l (p,c) ->
            (* generate code for a principal formula,
             * a set or an anonimous set with or without
             * local side conditions *)
            let (id,exp) = 
                match c,p with
                |Single,_ -> expand_single loc p l
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
            (* if the pattern is just a variable then the index must be an
             * empty string, otherwise the string used by matchpattern to index
             * formulae. if the pattern is an atom then the index is __atom *)
            let pattexp = 
                match p with
                | <:patt< $lid:_$ >> -> 
                        <:str_item<
                        value $lid:s$ = NodePattern.newpatt "" $lid:id$ >>
                | <:patt< Atom($lid:_$,$lid:_$) >> -> 
                        <:str_item<
                        value $lid:s$ = NodePattern.newpatt "__atom" $lid:id$ >>
                | _ ->
                        <:str_item<
                        value $lid:s$ = NodePattern.newpatt $str:s$ $lid:id$ >>
            in
            (* add a pattern to a list in relation to the type c *)
            add_pattlist (c,s) ;
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
    let l = 
        <:expr<
            let match_all node (pl,sl) hl =
                let (map,hist) = node#get in
                let enum = match_node map (pl,sl) in
                let (enum,sbl,newmap) =
                    let rec check_hist e =
                        try match Enum.get e with
                        [Some(sbl,ns) ->
                            if List.exists (fun c -> not(c sbl hist) ) hl then 
                                raise FailedMatch
                            else (e,sbl,ns)
                        |None -> (e,Substlist.empty,map)]
                        with [ FailedMatch -> check_hist e ]
                    in check_hist enum
                in
                let newnode = node#set (map,hist) in
            new context (enum,sbl,newnode)
            in match_all node ( $list:[pl;sl]$ ) $cl$ 
        >>
    in (l, str_items@condstrl)
;;

(* this function expand the function to build a new denominator *)
let expand_action loc sl (formula,action) = 
    let newid = new_id "exp_action" in
    let ex = 
        if is_variable formula then
            expand_build_formula_var loc (sl,formula) newid
        else expand_build_formula loc (sl,formula) newid
    in
    (* if the pattern is just a variable the function to implement the action is
     * much simpler and we have a special case for it *)
    let action =
        match action with
        | NoAct -> <:expr< $ex$ >>
        | Act(a) -> <:expr< $lid:a$($ex$) >>
    in
    (newid, <:str_item< value $lid:newid$ sbl = $action$ >>)
;;

(* this function expand the arguments and the function to 
 * execute side actions (history manipulation) for one denominator *)
let expand_actionlistel loc (act,func,args) =
    let newid = new_id "history_action" in
    let (ex2,ex3) =
        List.split
            (List.map (fun (sl,formula) ->
                let newid = new_id "build" in
                let ex = 
                    if is_variable formula then
                        expand_build_formula_var ~hist:true loc (sl,formula) newid
                    else expand_build_formula loc (sl,formula) newid
                in (<:expr< $lid:newid$ >>,(<:patt<$lid:newid$>>,ex))
            ) args
        )
    in
    let ex4 =
        match act with
        |None -> <:expr< let _ = ($lid:func$ ( $list:ex2$ ) ) in hist >>
        |Some(h) ->
                let ex1 =
                    try
                        let (s,_) = Hashtbl.find hist_table h in 
                        <:expr< `$lid:s$ >>
                    with Not_found ->
                        failwith ("expand_actionlist: "^h^" history not declared")
                in
                <:expr< hist#add $str:h$ ($ex1$ ($lid:func$ ( $list:ex2$ ) )) >>
    in
    let ex5 =
        if args = [] then <:expr< $ex4$ >>
        else <:expr< let $list:ex3$ in $ex4$ >>
    in
    (<:expr< $lid:newid$ >> ,
    <:str_item< value $lid:newid$ sbl hist = $ex5$ >>)
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

let expand_rule_den loc t dl hl =
    let expand dl tl hl =
        let is_reserved = function
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
            | <:expr< $lid:"unsat"$ >> -> <:expr< $uid:"Closed"$ >>
            | <:expr< $lid:"open"$ >>
            | <:expr< $lid:"sat"$ >> -> <:expr< $uid:"Open"$ >>
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
        let h =
            let hl = list_to_exprlist loc (List.hd actidl) in
            <:expr< (newnode,$firstal$,$hl$) >>
        in
        let (nextal,strl) = List.split (
            List.map2(fun dl hl ->
                let (al,strld) = __exp dl in
                let hl = list_to_exprlist loc hl in 
                (<:expr< (newnode#copy,$al$,$hl$) >>, strld)
            ) tl (List.tl actidl)
        ) in
        (* all the others *)
        let tl = list_to_exprlist loc nextal in
        let exp = 
            (* if the pattern contain a keyword and the tail is empty then
                * it must be an axiom *)
            if nextal = [] && 
            (List.exists (fun (sl,(f,_)) -> is_reserved f) dl) then
                let axiom_t = exp_reserved dl in
                <:expr< let (enum,sbl,newnode) = context#get in
                Leaf(newnode#set_status Data.$axiom_t$) >>
            else
                (* otherwise we check is the rule is invertible or not *)
                match t with
                | NotInv when not(nextal = []) ->
                        failwith "Not Invertible rule cannot branch"
                | Inv -> <:expr< 
                            let action_all node sbl al hl =
                                let (map,hist) = node#get in
                                let newmap = Build.build_node map sbl al in
                                let newhist =
                                    List.fold_left (fun h f -> f sbl h) hist hl
                                in 
                                node#set (newmap,newhist)
                            in
                            let rec make_llist sbl = fun
                                [[] -> Empty
                                |[(node,al,hl)::t] -> 
                                        LList(action_all node sbl al hl,
                                        lazy(make_llist sbl t))]
                            in
                            let (enum,sbl,newnode) = context#get in
                            Tree(make_llist sbl [ $h$ :: $tl$ ]) >>
                | NotInv ->
                        <:expr<
                            let action_all node sbl al hl =
                                let (map,hist) = node#get in
                                let newmap = Build.build_node map sbl al in
                                let newhist =
                                    List.fold_left (fun h f -> f sbl h) hist hl
                                in
                                node#set (newmap,newhist)
                            in
                            let rec make_llist = fun
                                [Empty -> Empty
                                |LList((node,sbl,al,hl),t) ->
                                        LList(action_all node sbl al hl,
                                        lazy(make_llist (Lazy.force t)))]
                            in
                            (* here we dynamically (lazily) generate the 
                             * tail of the action list *)
                            let rec next context =
                                let (enum,sbl,node) = context#get in
                                let (map,hist) = node#get in
                                let (newsbl,newmap) = 
                                    match Enum.get enum with
                                    [Some(sbl,ns) -> (sbl,ns)
                                    |None -> (Substlist.empty,map)]
                                in
                                let newnode = node#set (map,hist) in
                                if Data.Substlist.is_empty newsbl then
                                    LList((node,sbl,$firstal$,[]),lazy(Empty))
                                else
                                    LList((node,sbl,$firstal$,[]),
                                    lazy(next (context#set (enum,newsbl,newnode))))
                            in
                            Tree(make_llist ( next context ))
                        >>
        in
        (exp,List.flatten (strld::strl)@actstrl)
    in
    match dl,t with
    |Forall (dl::[]),NotInv ->
            let (exp,strl) = expand dl [] hl in
            (<:class_str_item< inherit exist_rule >>, exp, strl)
    |Forall (dl::[]),Inv ->
            let (exp,strl) = expand dl [] hl in
            (<:class_str_item< inherit linear_rule >>, exp, strl)
    |Forall (dl::tl),Inv ->
            let (exp,strl) = expand dl tl hl in
            (<:class_str_item< inherit forall_rule >>,exp, strl)
    |Exists (dl::tl),Inv ->  
            let (exp,strl) = expand dl tl hl in
            (<:class_str_item< inherit exist_rule >>, exp, strl)
    |_ -> failwith "expand_rule_den"
;; 

let expand_rule_class loc s (nl,fl) dl cl hl bl t =
    let (pl,strln)    = expand_rule_num loc (nl,fl) cl in
    let (rt,al,strld) = expand_rule_den loc t dl hl in
    strln@strld@
    [<:str_item< 
        class $lid:(String.lowercase s)^"_rule"$ = 
                object 
                $rt$; (* FIXME: this is the antiquotation *)
                
                method check node = $pl$ ;
                method down context = $al$ ;
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
    in
    let fail = ( <:patt< _ >>, None,
        <:expr< failwith "this formula is not mached by any pattern" >>
    )
    in
    <:str_item< Logic.__matchpatt.val := 
            Some(((fun [ $list:l@[atom;fail]$ ]) : Basictype.mixtype -> string ))
    >>
;;

let expand_parser loc connlist =
    let l = List.map(function
    | (v,s,r) when s =~ mu_re ->
            <:expr< ( $str:r$,[$str:(get_match 1 s)$;$str:(get_match 2 s)$], `Muconn (
            fun [ (i,a) -> $lid:v$(i,Basictype.nc,a) ]) ) >>
    | (v,s,r) when s =~ u_re ->
            <:expr< ( $str:r$,[$str:(get_match 1 s)$], `Uconn (
            fun [ a -> $lid:v$(Basictype.nc,a) ]) ) >>
    | (v,s,r) when s =~ bi_re ->
            <:expr< ( $str:r$,[$str:(get_match 1 s)$], `Biconn ( 
            fun [ (a,b) -> $lid:v$(Basictype.nc,a,b) ]) ) >>

    | (_,s,_) -> failwith (s^" is not a valid pattern")
    ) connlist
    in 
    let l = list_to_exprlist loc l in
    <:str_item< Logic.__inputparser.val :=
        Some(InputParser.buildParser $l$) >>

type 'a tree =
    |Star of 'a tree
    |Seq of 'a tree list
    |Choice of 'a tree list
    |Rule of 'a
;;

let expand_strategy loc tree = []

let expand_history loc l =
    let expr_list = List.map (
        fun (v,s,t) ->
            <:expr< ($str:v$,`$lid:s$ (new $uid:s$ . $lid:t$)) >>
    ) l
    in
    List.iter (fun (v,s,t) ->
        Hashtbl.replace hist_table v (s,t)
    ) l;
    list_to_exprlist loc expr_list
;;


let expand_preamble loc =
    let stl = [
        "Llist";"Data";"Basictype";"Comptypes";
        "Datatype";"Datatype.NodeType";"Datatype.Node";
        "Datatype.NodePattern";"Datatype.HistPattern";
        "Datatype.Partition";"Datatype.Rule";"Datatype.RuleContext";
        "Datatype.Strategy";"Datatype.Visit";"UserRule";"Tree"]
    in
    let stl = List.map (fun s -> <:str_item< open $uid:s$ >> ) stl in
    <:str_item< declare $list:stl$ end >>
;;

EXTEND
GLOBAL : Pcaml.str_item Pcaml.patt Pcaml.expr patt_term expr_term; 
  Pcaml.str_item: [[
    "CONNECTIVES"; clist = LIST1 connective SEP ";"; "END" ->
      List.iter (function
          |(v,s,r) when s =~ bi_re -> add_biconn r (get_match 1 s) v
          |(v,s,r) when s =~ mu_re -> 
                  add_muconn (get_match 1 s) (get_match 2 s) v
          |(v,s,r) when s =~ u_re -> add_uconn (get_match 1 s) v
          |(_,s,_) -> failwith (s^" is not a valid pattern")
      ) clist ;
      let preamble = expand_preamble loc in
      let pa = expand_parser loc clist in
      <:str_item< declare $list:[preamble;pa]$ end >>
    |"HISTORIES"; hlist = LIST1 history SEP ";"; "END" ->
            let l = expand_history loc hlist in
            <:str_item< Logic.__history_list.val := Some($l$) >>
    |"TABLEAU"; l = LIST1 rule; "END" ->
            let l = (expand_matchpatt loc)::l in 
            <:str_item< declare $list:l$ end >> 
    |"STRATEGY"; s = strategy ->
            (* <:str_item< declare $list:expand_strategy loc s$ end >> *)
            <:str_item< Logic.__strategy.val := Some(strategy) >>
  ]];

  Pcaml.expr : [[ "@"; (_,e) = expr_term; "@" -> <:expr< `Formula $e$ >> ]];
  Pcaml.patt : [[ (_,p) = patt_term -> <:patt< `Formula $p$ >> ]];

  connective: [[
      v = UIDENT; ","; s = STRING; ","; r = UIDENT -> (v,s,r)
  ]];

  history: [[
      v = UIDENT; ":"; s = UIDENT; "."; t = LIDENT -> (v,s,t)
  ]];
  
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
      | lid = UIDENT -> Rule(String.lowercase lid^"_rule")
      | uid = UIDENT; "."; lid = UIDENT -> Rule(uid^String.lowercase lid^"_rule")
      ]
  ];
  
(*
  strategy:
  [[ s1 = strategy; ";"; s = LIST1 strategy SEP ";" ->
          <:expr< Seq($list_to_exprlist loc (s1::s)$) >>
      | s1 = strategy; "|"; s = LIST1 strategy SEP "|" ->
          <:expr< Choice($list_to_exprlist loc (s1::s)$) >>
      | s = strategy; "*" -> <:expr< Star([ $s$ ]) >>
      | "("; s = strategy; ")" -> s
      | lid = UIDENT -> <:expr< Rule($lid:String.lowercase lid^"_rule"$) >>
      | uid = UIDENT; "."; lid = UIDENT ->
              <:expr< Rule($uid:uid$.$lid:String.lowercase lid^"_rule"$) >>
      ]
  ];
*)

  rule: [[
      "RULE";
      id = UIDENT; (nl,n) = num; t = test_sep; dl = denlist; 
      cl = OPT condition;
      hl = OPT actionlist;
      bl = OPT branchlist;
      "END" ->
          let rl = expand_rule_class loc id (nl,n) dl cl hl bl t in 
          <:str_item< declare $list:rl$ end >>
  ]];

  condition: [[
      "COND"; OPT "["; l = LIST1 usercond SEP ";"; OPT "]" -> l
  ]];

  actionlist: [[
      "ACTION"; OPT "["; l = LIST1 action SEP ";"; OPT "]" -> l
  ]];

  branchlist: [[
      "BRANCH"; OPT "["; l = LIST1 action SEP ";"; OPT "]" -> l
  ]];

  action: [[
      OPT "["; l = LIST1 useract SEP ";"; OPT "]" -> l
  ]];
  
  useract: [[
      f = LIDENT; OPT "("; args = LIST0 expr_term SEP ","; OPT ")" ->
          (None,f,args)
      | s = UIDENT; ":="; 
        f = LIDENT; OPT "("; args = LIST0 expr_term SEP ","; OPT ")" ->
          (Some(s),f,args)
  ]];
  
  usercond: [[
      f = LIDENT; OPT "("; args = LIST0 expr_term SEP ","; OPT ")" ->
          (None,f,args)
  ]];

  (* Forall of (string list * expr) list list *)
  denlist: [[
       d = den; "|";  dl = den_forall -> Forall(d::dl)
      |d = den; "||"; dl = den_exists -> Exists(d::dl)
(*    |d = den; "||>"; cl = LIST1 branch_cond SEP ";"; "<||"; dl = den_exists -> 
      |d = den; "|>"; cl = LIST1 branch_cond SEP ";"; "<|"; dl = den_forall ->
      |d = den; "|||>"; cl = LIST0 branch_cond SEP ";"; "<|||"; dl = den_all -> 
      |"("; dl = denlist; ")" -> dl
*)
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
      [ x = UIDENT ->
          ([String.lowercase(x)],
          <:expr< $lid:String.lowercase(x)$>>)
      | "."; x = LIDENT ->
              let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
              ([String.lowercase(x)],
              <:expr< Atom($nc$,$lid:String.lowercase(x)$)>>)
      | "("; p = expr_term; ")" -> p
      ] 
    ];

  patt_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ x = UIDENT ->
          ([String.lowercase(x)],
          <:patt< $lid:String.lowercase(x)$>>)
      | "."; x = LIDENT ->
              (["atom___"^String.lowercase(x)],
              <:patt< Atom(nc,$lid:String.lowercase(x)$)>>)
      | "("; p = patt_term; ")" -> p
      (* | cut = LIDENT; "("; p = expr_term; ")" -> p *)
      ] 
    ];
    
END
