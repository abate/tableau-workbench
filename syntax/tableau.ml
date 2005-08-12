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

(*
let insert_this () =
    let loc = Token.dummy_loc in
    let stl = [
        "Llist";"Data";"Basictype";"Comptypes";
        "Datatype";"Datatype.NodeType";"Datatype.Node";
        "Datatype.NodePattern";"Datatype.HistPattern";
        "Datatype.Partition";"Datatype.Rule";"Datatype.RuleContext";
        "Datatype.Strategy";"Datatype.Visit";"UserRule";"Tree"]
    in
    let stl = List.map (fun s -> <:str_item< open $uid:s$ >> ) stl in
    (<:str_item< declare $list:stl$ end >>, loc)

let _ =
  let first = ref true in
  let parse strm =
    let (l, stopped) = Grammar.Entry.parse Pcaml.implem strm in
    let l' = 
      if !first then
        insert_this () :: l
      else l in
    (l', stopped) in
  Pcaml.parse_implem := parse
  *)

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

let hist_table = ref [];;
let add_hist_table e = hist_table := e::!hist_table;;

(* XXX: big enough ?? *)
let patt_table = Hashtbl.create 300 ;;

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
let expand_set loc formula l =
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
    (newid,
    <:str_item<
        value $lid:newid$ sbl fl =
            let __rec = fun [ $list:ex6$ ] in 
            let $pa1$ = List.fold_left (
                fun [ $pa1$ ->
                    fun [ el -> 
                        let $pa2$ = __rec el in $ex3$ 
                    ]
                ]
            ) $ex4$ fl
            in Sbl.add sbl $ex5$
    >>)
;;

(* generate the code to pattern match a principal formula *)
let expand_single loc formula l =
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
            in Sbl.add sbl (List.combine $ex2$ (__rec (List.hd fl)))
    >>)
;;

(* generate the code to pattern match a generic variable *)
let expand_set_anon loc formula a =
    let newid = new_id "exp_anon" in
    (newid,
    <:str_item<
    (* catch all pattern *)
    value $lid:newid$ sbl fl =
        Sbl.add sbl [($str:String.uppercase a$,fl)]
    >>)
;;

type cond_t = | Single (*    | Cond of ?? *) | NoCond
type branch_t =
    | Forall of (string list * MLast.expr) list list
    | Exists of (string list * MLast.expr) list list
    | User   of (string list * MLast.expr) list list
(*  | Cond of ?? *)

let expand_rule_num loc stringlist formulalist =
    let pl = ref [] in
    let sl = ref [] in
    let el = ref [] in
    let add_pattlist = function
        |_,"" -> ()
        |Single,s ->  pl := s::!pl
        |_,s -> sl := s::!sl
    in
    let str_items = 
        List.map2 (fun l (p,c) ->
            (* generate code for a principal formula,
             * a set or an anonimous set *)
            let (id,exp) = 
                match c,p with
                |Single,_ -> expand_single loc p l
                |_,<:patt< $lid:_$ >> -> expand_set_anon loc p (List.hd l)
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
                        <:str_item< value $lid:s$ = NodePattern.newpatt "" $lid:id$ >>
                | <:patt< Atom($lid:_$,$lid:_$) >> -> 
                        <:str_item< value $lid:s$ = NodePattern.newpatt "__atom" $lid:id$ >>
                | _ ->
                        <:str_item< value $lid:s$ = NodePattern.newpatt $str:s$ $lid:id$ >>
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
    let el = list_to_exprlist loc
        (List.map (fun e -> <:expr< $lid:e$ >> ) !el )
    in
    (* return a list of patterns and all related functions *)
    ([pl;sl;el], str_items)
;;


let expand_action loc sl formula = 
    let newid = new_id "exp_action" in
    let is_variable = function
        | <:expr< $lid:a$ >> -> true
        | _ -> false
    in
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
    let ex3 = 
        let l = List.map (fun a ->
            <:expr<Data.Substlist.find $str:String.uppercase a$ sbl>>
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
            <:patt<`L($lid:"l"^string_of_int !i$)>>
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
        let l = List.map (fun a -> <:patt< $lid:a$ >>
        ) sl in <:patt< ( $list:l$ ) >>
    in
    let pa5 = (* tuple of empty lists *)
        let l = List.map (fun a -> <:patt< [] >>) sl 
        in <:patt< ( $list:l$ ) >>
    in
    (* if the pattern is just a variable the function to implement the action is
     * much simpler and we have a special case for it *)
    if is_variable formula then
        (newid,
        <:str_item<
        value $lid:newid$ sbl = 
        try match $ex3$ with
            [`L(l) -> l#elements
            |_ -> failwith ($str:newid$^" type node allowed") ]
        with [Not_found -> failwith ($str:newid$^" something wrong")]
        >>)
    else
        (newid,
        <:str_item<
            value $lid:newid$ sbl = 
            try
                let rec split = fun 
                    [ $pa3$ -> [ $ex1$::(split $ex2$) ]
                    | $pa5$ -> []
                    | _ -> failwith ($str:newid$^" something about the list") ]
                in    
                match $ex3$ with
                [ $pa2$ ->
                        List.map (fun
                            [$pa4$ -> `Formula $formula$
                            | _ -> failwith ($str:newid$^" type node allowed" )]
                        ) (split $ex4$)
                | _ -> failwith ($str:newid$^" type node allowed") ]
            with [ Not_found -> failwith $str:newid$ ] 
        >>)
;;

let expand_rule_den loc t dl =
    let expand dl tl =
        let is_reserved = function
            | <:expr< $lid:"close"$ >>
            | <:expr< $lid:"unsat"$ >> 
            | <:expr< $lid:"open"$ >>
            | <:expr< $lid:"sat"$ >> -> true
            |_ -> false
        in
        let exp_reserved l = 
            let (_,f) = try List.find (fun sl,f -> is_reserved f) l
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
                List.split (List.filter_map (fun (sl,f) ->
                    if is_reserved f then None
                    else
                    let (id,exp) = expand_action loc sl f in
                    let s = new_id "action" in
                    let pattexp =
                        <:str_item<
                        value $lid:s$ = NodePattern.newact "" $lid:id$ >> in
                    Some(<:expr< $lid:s$ >>,<:str_item< declare $list:[exp;pattexp]$ end>>)
                    ) dl
                )
            in
            let al = list_to_exprlist loc al 
            in (al,strld)
        in
        let (firstal,strld) = __exp dl in
        (* first node of the action list *)
        let h = <:expr< (newnode,$firstal$) >> in
        let (nextal,strl) = List.split (
            List.map(fun dl ->
                let (al,strld) = __exp dl in
                (<:expr< (newnode#copy,$al$) >>, strld)
            ) tl 
        ) in
        (* all the others *)
        let tl = list_to_exprlist loc nextal in
        let exp = 
            (* if the pattern contain a keyword and the tail is empty then
                * it must be an axiom *)
            if nextal = [] && (List.exists (fun (sl,f) -> is_reserved f) dl) then
                let axiom_t = exp_reserved dl in
                <:expr< let (enum,sbl,newnode) = context#get in
                Leaf(newnode#set_status Data.$axiom_t$) >>
            else
                (* otherwise we check is the rule is invertible or not *)
                match t with
                | NotInv when not(nextal = []) -> failwith "Not Invertible rule cannot branch"
                | Inv -> <:expr< 
                            let action_all node sbl al =
                                let (map,hist) = node#get in
                                let newmap = Build.build_node map sbl al in
                                (* let newhist = Build.build_hist node sbl [] in
                            * *)
                                node#set (newmap,hist)
                            in
                            let rec make_llist sbl = fun
                                [[] -> Empty
                                |[(node,al)::t] -> 
                                        LList(action_all node sbl al,
                                        lazy(make_llist sbl t))]
                            in
                            let (enum,sbl,newnode) = context#get in
                            Tree(make_llist sbl [ $h$ :: $tl$ ]) >>
                | NotInv ->
                        <:expr<
                            let action_all node sbl al =
                                let (map,hist) = node#get in
                                let newmap = Build.build_node map sbl al in
                                (* let newhist = Build.build_hist node sbl [] in
                            * *)
                                node#set (newmap,hist)
                            in
                            let rec make_llist = fun
                                [Empty -> Empty
                                |LList((node,sbl,al),t) ->
                                        LList(action_all node sbl al,
                                        lazy(make_llist (Lazy.force t)))]
                            in
                            (* here we dynamically (lazily) generate the tail of the
                             * action list *)
                            let rec next context =
                                let (enum,sbl,node) = context#get in
                                let (map,hist) = node#get in
                                let (newsbl,newmap) = match_hist enum hist map [] in
                                let newnode = node#set (newmap,hist) in
                                if Data.Substlist.is_empty newsbl then
                                    LList((node,sbl,($firstal$) ),lazy(Empty))
                                else
                                    LList((node,sbl,($firstal$)),
                                    lazy(next (context#set (enum,newsbl,newnode))))
                            in
                            Tree(make_llist ( next context ))
                        >>
        in
        (exp,List.flatten (strld::strl))
    in
    match dl,t with
    |Forall (dl::[]),NotInv ->
            let (exp,strl) = expand dl [] in
            (<:class_str_item< inherit exist_rule >>, exp, strl)
    |Forall (dl::[]),Inv ->
            let (exp,strl) = expand dl [] in
            (<:class_str_item< inherit linear_rule >>, exp, strl)
    |Forall (dl::tl),Inv ->
            let (exp,strl) = expand dl tl in
            (<:class_str_item< inherit forall_rule >>,exp, strl)
    |Exists (dl::tl),Inv ->  
            let (exp,strl) = expand dl tl in
            (<:class_str_item< inherit exist_rule >>, exp, strl)
    |_ -> failwith "expand_rule_den"
;; 

let expand_rule_class loc s (nl,fl) dl t =
    let (pl,strln) = expand_rule_num loc nl fl in 
    let (rt,al,strld) = expand_rule_den loc t dl in
    strln@strld@
    [<:str_item< 
        class $lid:(String.lowercase s)^"_rule"$ = 
                object 
                $rt$; (* FIXME: this is the antiquotation *)
                
                method check node = 
                    let match_all node (pl,sl,ll) hl =
                        let (map,hist) = node#get in
                        let enum = match_node map (pl,sl,ll) in
                        let (sbl,newmap) = match_hist enum hist map hl in
                        let newnode = node#set (newmap,hist) in
                    new context (enum,sbl,newnode)
                    in
                    match_all node ( $list:pl$ ) [] ;

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
        ((fun [ $list:l@[atom;fail]$ ]) : Basictype.mixtype -> string )
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
    <:str_item< Logic.__inputparser.val := InputParser.buildParser $l$ >>

type 'a tree =
    |Star of 'a tree
    |Seq of 'a tree list
    |Choice of 'a tree list
    |Rule of 'a
;;

let expand_strategy loc tree = []

(*
let expand_userfun loc = function
     (sl, <:expr $lid:a$ >> -> if history a then .. else ..
    |(sl, expr ->
            *)

let expand_history loc l =
    let (idlist,expr_list) = List.split l in
    List.iter (fun e -> add_hist_table e) idlist;
    list_to_exprlist loc expr_list

let hist_type loc = function
    "Set" -> <:expr< `S(new Set.set) >>
    |_ -> assert(false)
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
GLOBAL : Pcaml.str_item patt_term expr_term; 
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
            <:str_item< Logic.__history_list.val := $l$ >>
    |"TABLEAU"; l = LIST1 rule; "END" ->
            let l = (expand_matchpatt loc)::l in 
            <:str_item< declare $list:l$ end >> 
    |"STRATEGY"; s = strategy ->
            (* <:str_item< declare $list:expand_strategy loc s$ end >> *)
            <:str_item< Logic.__strategy.val := Strategy.newstate "start" >>
  ]];

  connective: [[
      v = UIDENT; ","; s = STRING; ","; r = UIDENT -> (v,s,r)
  ]];

  history: [[
      v = UIDENT; ":"; t = UIDENT -> (v,<:expr< ($str:v$,$hist_type loc t$) >>)
  ]];
  
  strategy:
  [ "One" LEFTA
      [ s1 = strategy LEVEL "Simple"; ";";
        s = LIST1 strategy LEVEL "Simple" SEP ";" -> Seq (s1::s)
      | s1 = strategy LEVEL "Simple"; "|";
        s = LIST1 strategy LEVEL "Simple" SEP "|" -> Choice (s1::s)
      | s = strategy LEVEL "Simple"; "*" -> Star ( s )
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
       OPT condition;
       OPT actionlist;
       OPT branchlist;
       "END" ->
           let rl = expand_rule_class loc id (nl,n) dl t in 
           <:str_item< declare $list:rl$ end >>
  ]];

  condition: [[
      "COND"; OPT "["; l = LIST0 userfun SEP ";"; OPT "]" -> l
  ]];

  actionlist: [[
      "ACTION"; OPT "["; l = LIST0 action SEP ";"; OPT "]" -> l
  ]];

  branchlist: [[
      "BRANCH"; OPT "["; l = LIST0 action SEP ";"; OPT "]" -> l
  ]];

  action: [[
      OPT "["; l = LIST0 userfun SEP ";"; OPT "]" -> l
  ]];
  
  userfun: [[
      f = LIDENT; OPT "("; LIST0 expr_term SEP ","; OPT ")" -> f
      | s = UIDENT; "="; f = LIDENT; OPT "("; LIST0 expr_term SEP ","; OPT ")" -> f
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
  
  (* ( string list * expr) list *)
  den: [[al = LIST1 denformula SEP ";" -> al]];
  
  (* ( string list list * expr list ) *)
  num: [[ pl = LIST1 numformula SEP ";" -> List.split pl ]]; 
  
  numformula: [[
       "{"; (s,p) = patt_term; "}" -> (s,(p,Single))  (* single formula *)
 (*     |"["; (s,p) = patt_term; "]" -> (s,(p,NoCond))  (* not empty set *) *)
      |"<"; (s,p) = patt_term; ">" -> (s,(p,NoCond))  (* empty set *)
      |c = LIDENT; OPT "("; (s,p) = patt_term; OPT ")" -> (s,(p,NoCond)) 
      |(s,p) = patt_term           -> (s,(p,NoCond))  (* no conditions *)
  ]];
  
  denformula: [[
      (s,p) = expr_term -> (s,p) (* string list * expr) *)
  ]];
  
  expr_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ x = UIDENT -> ([String.lowercase(x)],<:expr< $lid:String.lowercase(x)$>>)
      | "."; x = LIDENT ->
              let nc = <:expr<  Basictype.newcore 1 [|0|] >> in
              ([String.lowercase(x)],<:expr< Atom($nc$,$lid:String.lowercase(x)$)>>)
      | "("; p = expr_term; ")" -> p
      ] 
    ];

  patt_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ x = UIDENT -> ([String.lowercase(x)],<:patt< $lid:String.lowercase(x)$>>)
      | "."; x = LIDENT ->
              (["atom___"^String.lowercase(x)],<:patt< Atom(nc,$lid:String.lowercase(x)$)>>)
      | "("; p = patt_term; ")" -> p
(*      | f = LIDENT; "("; p = patt_term; ")" -> p *)
      ] 
    ];
    
END
