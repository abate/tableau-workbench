(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Parselib

let expand_preamble _loc =
    let stl = [
        "Llist";"Data";"Tree";
        "Basictype";"Comptypes";
        "Datatype";"Datatype.Node";
        "Datatype.NodePattern";
        "Datatype.Partition";"Datatype.Rule";"Datatype.RuleContext";
        "Datatype.Strategy";"Datatype.Visit";"UserRule"]
    in
    List.map (fun s -> <:str_item< open $uid:s$ >> ) stl
;;

let expand_parser _loc clist = 
    let l = filter_map(function
    |Ast.Connective(v,s,r) when s =~ u_re -> 
            Some(
                <:expr< ( $str:r$,[$str:(get_match 1 s)$], `Uconn (
                    fun [ a -> $lid:v$(a) ]) ) >>
            ) 
    |Ast.Connective(v,s,r) when s =~ bi_re ->
            Some (
                <:expr< ( $str:r$,[$str:(get_match 1 s)$], `Biconn (
                    fun [ (a,b) -> $lid:v$(a,b) ]) ) >>
            )
    |Ast.Connective(v,"Const",_) -> Some ( <:expr< ( "Const",[$str:v$], `Const ) >> )
    |Ast.Connective(_,s,_) -> failwith (s^" is not a valid pattern")
    ) clist
    in
    let l = list_to_exprlist _loc l in
    let p1 = <:patt< __connlist >> in
    let e1 = <:expr< $l$ >> in
    let p2 = <:patt< _ >> in
    let e2 = <:expr<
        Logic.__inputparser.val := Some(InputParser.buildParser __connlist) >> 
    in
    let st1 = <:str_item< value rec $list:[(p1,e1)]$ >> in
    let st2 = <:str_item< value $list:[(p2,e2)]$ >> in
    <:str_item< declare $list:[st1;st2]$ end >>
;;

let expand_printer _loc clist =
    let l = filter_map(function
        |Ast.Connective(v,s,r) when s =~ u_re ->
                Some(<:patt< ( $lid:v$(a)) >>,
                None,
                <:expr< Printf.sprintf
                $str:"("^((get_match 1 s)^" %s)")$ (__printer a) >>)
        |Ast.Connective(v,s,r) when s =~ bi_re ->
                Some(<:patt< ( $lid:v$(a,b) ) >>,
                None,
                <:expr< Printf.sprintf
                $str:("(%s "^(get_match 1 s)^" %s)")$ (__printer a) (__printer b) >>)
        |Ast.Connective(v,"Const",_) -> None
        |Ast.Connective(_,s,_) -> failwith (s^" __printer error")
    ) clist
    in
    let default =
        <:patt< _ >> ,
        None,
        <:expr< failwith "this __printer prints formulae only" >>
    in
    let atom = <:patt< Atom(s) >> , None, <:expr< s >> in
    let const = <:patt< Constant(a) >>, None, <:expr< a >> in
    let p1 = <:patt< __printer >> in
    let e1 = <:expr< fun [ $list:List.rev([default;atom;const]@l)$ ] >> in
    let p2 = <:patt< _ >> in
    let e2 = <:expr< Logic.__printer.val := Some(__printer) >> in
    let st1 = <:str_item< value rec $list:[(p1,e1)]$ >> in
    let st2 = <:str_item< value $list:[(p2,e2)]$ >> in
    <:str_item< declare $list:[st1;st2]$ end >>
;;

(* substitute all occurrences of t by s *)
let expand_substitute _loc clist =
    let l = filter_map(function
        |Ast.Connective(v,s,r) when s =~ u_re ->
                Some(<:patt< ( $lid:v$(a)) >>,
                None,
                <:expr<
                if a = t then $lid:v$ (s) else $lid:v$(__substitute s t a) >>)
        |Ast.Connective(v,s,r) when s =~ bi_re ->
                Some(<:patt< ( $lid:v$(a,b) ) >>,
                None,
                <:expr<
                 if a = t then
                     if b = t then $lid:v$ (s,s)
                     else $lid:v$ (s, __substitute s t b)
                 else
                     if b = t then $lid:v$ (__substitute s t a, s)
                     else $lid:v$ (__substitute s t a, __substitute s t b)
                >>)
        |Ast.Connective(v,"Const",_) -> None
        |Ast.Connective(_,s,_) -> failwith (s^" __substitute error")
    ) clist
    in
    let equiv = <:patt< f >>, Some(<:expr< f = t >>), <:expr< s >> in
    let default =
        <:patt< _ >> ,
        None,
        <:expr< failwith "can __subsitute only formulae " >>
    in
    let atom = <:patt< ( Atom(s) as f ) >> , None, <:expr< f >> in
    let const = <:patt< ( Constant(a) as f ) >>, None, <:expr< f >> in
    let p = <:patt< __substitute >> in
    let e = <:expr< fun s -> fun t -> fun [
        $list:List.rev([default;atom;const]@l@[equiv])$ ] >>
    in
    <:str_item< value rec $list:[(p,e)]$ >>
;;

let expand_matchpatt _loc =
    let pattlist = Hashtbl.fold (fun t s l -> (s,t) :: l) patt_table [] in
    let rec term_patt = function
        |Ast.Bicon(id,t1,t2) -> <:patt< $uid:id$ ($term_patt t1$,$term_patt t2$) >>
        |Ast.Ucon(id,t) -> <:patt< $uid:id$ ($term_patt t$) >>
        |Ast.Const(id) -> <:patt< Constant(_) >>
        |Ast.Atom(id) -> <:patt< Atom(_) >>
        |Ast.Var(id) -> <:patt< _ >>
        |_ -> failwith "expand_matchpatt"
    in
    let pel =
        filter_map (fun (s,p) ->
            let patt =
                match p with
                    |Ast.Bicon(id,t1,t2) ->
                        Some <:patt< `LabeledFormula ( _, $uid:id$ ($term_patt t1$,$term_patt t2$)) >>
                    |Ast.Ucon(id,t) -> Some <:patt< `LabeledFormula (_, $uid:id$ ($term_patt t$)) >>
                    |_ -> None
            in
            if Option.is_none patt then None
            else Some (Option.get patt, None, <:expr< $str:s$ >>)
        ) (sort_pattlist pattlist)
    in
    let def = (
        <:patt< _ >>,
        None,
        <:expr< failwith "this formula is not mached by any pattern" >>)
    in
    let atom = ( <:patt< `LabeledFormula (_, Atom(_)) >>, None, <:expr< "__atom" >>) in
    let const = ( <:patt< `LabeledFormula (_, Constant(_)) >>, None, <:expr< "__const" >>) in
    let id = <:patt< __matchpatt >> in
    let ex1 = <:expr< fun [ $list:pel@[atom;const;def]$ ] >> in
    let ex2 = <:expr< Logic.__matchpatt.val := Some(__matchpatt) >> in
    let st1 = <:str_item< value rec $list:[(id,ex1)]$ >> in
    let st2 = <:str_item< value _ = $ex2$ >>
    in <:str_item< declare $list:[st1;st2]$ end >>
;;

let rec build_hist_type t =
    let rec inner l =
        List.fold_left (fun s ->
            function
                |Ast.Type("Set") 
                |Ast.Type("List") -> failwith "basic type not specified : Ex: Set of Formula"
                |Ast.Type(id) -> s ^ id 
                |Ast.Container("Set",[Ast.Type(id)]) -> "Set"
                |Ast.Container("List",[Ast.Type(id)]) -> "List"
                |Ast.Container(id,l) -> id ^ (inner l)
            ) "" l
    in
    match t with
    |Ast.Type("Set") 
    |Ast.Type("List") -> failwith "basic type not specified : Ex: Set of Formula"
    |Ast.Type(id) -> ("Singleton",id)
    |Ast.Container("Set",[Ast.Type(id)]) -> ("Set", id)
    |Ast.Container("List",[Ast.Type(id)]) -> ("List", id)
    |Ast.Container(id,l) -> (id ^ inner l, inner l)
;;

let expand_histories _loc (Ast.Histories ( histlist )) =
    let _ = 
        List.iter (function
            |Ast.VDecl(id,t,ex,def) 
            |Ast.HDecl(id,t,ex,def) ->
                    let outer,inner = build_hist_type t in
                    Hashtbl.replace hist_table id (outer,inner,ex,def)
        ) histlist
    in
    let histlist =
        if not(Hashtbl.mem hist_table "status") then
            let (id,t,ex,def) = 
                ("status",
                "String",
                <:expr< new Set.set >>,
                Some <:expr< "Open" >>)
            in
            let status = Ast.VDecl(id,Ast.Type(t),ex,def)
            in
            Hashtbl.replace hist_table id ("Singleton",t,ex,def) ;
            status::histlist 
        else histlist
    in
    let expr_list = List.map (function
        |Ast.VDecl(id,t,ex,def) ->
                let (outer,inner) = build_hist_type t in
                let n =
                    if Option.is_none def then <:expr< $ex$ >>
                    else <:expr< ($ex$)#add (`$inner$ $Option.get def$) >>
                in <:expr< ($str:id$, `$outer$ ($n$), Variable) >>

        |Ast.HDecl(id,t,ex,def) ->
                let (outer,inner) = build_hist_type t in
                let n =
                    if Option.is_none def then <:expr< $ex$ >>
                    else <:expr< ($ex$)#add (`$inner$ $Option.get def$) >>
                in <:expr< ($str:id$, `$outer$ ($n$), History) >>
    ) histlist
    in
    let l = list_to_exprlist _loc expr_list in
    <:str_item< Logic.__history_list.val := Some($l$) >>
;;

let rec expand_term_expr _loc = function
    |Ast.Bicon(id,t1,t2) ->
            <:expr< $uid:id$ ($expand_term_expr _loc t1$,$expand_term_expr _loc t2$) >>
    |Ast.Ucon(id,t) -> <:expr< $uid:id$ ($expand_term_expr _loc t$) >>
    |Ast.Const(id) -> <:expr< Constant($str:id$) >>
    |Ast.Atom(id) -> <:expr< Atom($str:id$) >>
    |Ast.FAtom(id,ex) -> <:expr< Atom($str:id$^(string_of_int $ex$)) >>
    |Ast.Var(id) -> <:expr< $lid:id$ >>
    |Ast.History(id) -> <:expr< $lid:id$ >>
    |Ast.Variable(id,_) -> <:expr< $lid:id$ >>
    |Ast.Expr(ex) -> <:expr< $ex$ >>
;;

let rec expand_term_patt _loc = function
    |Ast.Bicon(id,t1,t2) ->
            <:patt< $uid:id$ ($expand_term_patt _loc t1$,$expand_term_patt _loc t2$) >>
    |Ast.Ucon(id,t) -> <:patt< $uid:id$ ($expand_term_patt _loc t$) >>
    |Ast.Const("") -> <:patt< Constant(_) >>
    |Ast.Atom("") -> <:patt< Atom(_) >>
    |Ast.Const(id) -> <:patt< Constant($str:id$) >>
    |Ast.Atom(id) -> <:patt< Atom($str:id$) >>
    |Ast.Var(id) -> <:patt< $lid:id$ >>
    |_ -> failwith "expand_term_patt"
;;

let rec expand_term_type _loc id =
    try
        let (outer,inner,ex,def) = Hashtbl.find hist_table id in
        <:patt< `$outer$ $lid:String.lowercase id^"cont"$ >>
    with Not_found ->
        <:patt< `Set $lid:String.lowercase id^"cont"$ >>
;;

let rec expand_term_cont _loc term id =
    try
        let (outer,inner,ex,def) = Hashtbl.find hist_table id in
        let default =
            if Option.is_none def
            then <:expr< `$outer$ $ex$ >>
            else <:expr< `$outer$ (($ex$)#add (`$inner$ $Option.get def$)) >>
        in
        match term with
        (* FIXME: refactor *)
        |Ast.Variable(id,Ast.Last) ->
                <:expr<
                try
                    let varhist = List.nth varl (List.length varl - 1)
                    in varhist#find $str:id$
                with [Failure "nth" -> $default$
                ]
                >>
        |Ast.Variable(id,Ast.Int(vi)) ->
                <:expr<
                try
                    let varhist = List.nth varl ($int:string_of_int vi$ - 1)
                    in varhist#find $str:id$
                with [Failure "nth" -> $default$
                ]
                >>
        |Ast.History(id) -> <:expr< hist#find $str:id$ >>
        |_ -> failwith "expand_term_cont"
    with Not_found ->
        <:expr<
        try sbl#find $str:id$
        with [Not_found -> failwith ("__find: " ^ $str:id$)]
        >>
;;

let rec get_term_ids = function
    |Ast.Bicon(id,t1,t2) -> get_term_ids t1 @ get_term_ids t2
    |Ast.Ucon(id,t) -> get_term_ids t
    |Ast.Const(_) -> []
    |Ast.Atom(_) -> []
    |Ast.FAtom(_,_) -> []
    |Ast.Var(id) -> [id]
    |Ast.History(id) -> [id]
    |Ast.Variable(id,_) -> [id]
    |Ast.Expr(_) -> []
;;

let expand_set _loc term =
    let ids = get_term_ids term in
    let patt = expand_term_patt _loc term in
    let termid = patt_to_string ~generic:false term in
    let ids_list = list_to_exprlist _loc (
        List.map (fun x -> <:expr< $str:x$ >> ) ids
        )
    in
    let frl = List.map (fun x -> <:expr< `LabeledFormula (label, $lid:x$) >> ) ids in
    let frl_list = list_to_exprlist _loc frl in
    match term with
    |Ast.Var(id) -> <:expr< fun sbl fl -> sbl#add [($str:id$,fl)] >>
    |_ ->
            <:expr<
            fun sbl fl ->
                let __rec = fun
                    [`LabeledFormula (label, $patt$) -> $frl_list$
                    |`LabeledFormula _ -> raise FailedMatch
                    |_ -> failwith ("set : type mismatch")]
                in (sbl#add (ExtList.fold __rec fl $ids_list$))#add
                [($str:termid$,fl)]
            >>
;;

let expand_single _loc term =
    let ids = get_term_ids term in
    let patt = expand_term_patt _loc term in
    let ids_list = list_to_exprlist _loc (
        List.map (fun x -> <:expr< $str:x$ >> ) ids
        )
    in
    let frl_list = list_to_exprlist _loc (
        List.map (fun x -> <:expr< `LabeledFormula (label, $lid:x$) >> ) ids
        )
    in
    let act =
        (<:patt< `LabeledFormula (label, $patt$) >>, None,
        <:expr<
            List.map2
            (fun f s ->
                try 
                    if sbl#mem s f then []
                    else raise FailedMatch
                with [Not_found -> [f]]
            ) $frl_list$ $ids_list$
        >>)
    in
    let def =
        if is_var term then
            [(<:patt< _ >>, None, <:expr< failwith ("single : type mismatch") >>)]
        else
            [(<:patt< `LabeledFormula _ >>, None, <:expr< raise FailedMatch >>);
             (<:patt< _ >>, None, <:expr< failwith ("single : type mismatch") >>)]
    in
    (* NB: I'm re-using the same vars ... bad ?? *)
    let (act,ids_list) = 
        let termid = patt_to_string ~generic:false term in
        if not(is_var term) then
            let (p,_,e) = act in
            ((<:patt< ( $p$ as bf ) >>, None, <:expr< [ [bf :: []] :: $e$ ] >>),
            (<:expr< [ $str:termid$ :: $ids_list$ ] >>))
        else
            (act,ids_list)
    in
    <:expr<
    fun sbl -> fun fl ->
        let __rec = fun [ $list:act::def $ ] in
        match fl with
        [[] -> sbl#add (List.combine $ids_list$ [[]])
        |[ h::_ ] -> sbl#add (List.combine $ids_list$ (__rec h))
        ]
    >>
;;

(* if ruleid is None then the function is generating a term in a custom function
    * outside the tablaue defintion *)
let rec build_term _loc ?ruleid ?(naked=false) ?(action=false) term =
    let ids = unique (get_term_ids term) in
    let expr = expand_term_expr _loc term in
    let term_type = List.map (expand_term_type _loc) ids in
    let patt_list = List.map (fun x -> <:patt< `LabeledFormula (_, $lid:x$) >> ) ids in
    let dressedcont id = <:expr< $lid:id$#elements >> in
    let nakedcont id inner =
        <:expr<
        match $lid:id$#head with
            [`$inner$ i -> i
            |_ -> failwith "__build"]
        >>
    in
    let build_term_aux1 term ex = 
        let term_cont = List.map (expand_term_cont _loc term) ids in
        <:expr<
        fun sbl hist varl ->
            match ( $list:term_cont$ ) with
            [( $list:term_type$ ) -> $ex$
            |_ -> failwith ("__build")
            ]
        >>
    in
    let build_term_aux2 term = 
        let term_cont = List.map (expand_term_cont _loc term) ids in
        let term_elem = 
            List.map (fun x -> dressedcont (String.lowercase x^"cont") ) ids
        in
            <:expr<
            fun sbl hist varl ->
                match ( $list:term_cont$ ) with
                [( $list:term_type$ ) ->
                    ExtList.$lid:"map"^string_of_int(List.length ids)$ (fun
                        [( $list:patt_list$ ) -> `LabeledFormula ([], $expr$)
                        |_ -> failwith ("__build")
                        ]
                    ) ( $list:term_elem$ )
                |_ -> failwith ("__build")
                ]
            >>
    in
    let build_term_aux3 term =
        let s = patt_to_string ~generic:false term in
        <:expr<
        fun sbl hist varl ->
            match
            try sbl#find $str:s$ with [Not_found -> failwith ("__find: " ^ $str:s$)]
            with
            [`Set cont -> cont#elements
            |_ -> failwith ("__build")
            ]
        >>
    in
    match term with
    |Ast.Var(_) ->
            let ex =
                if naked
                then nakedcont (String.lowercase (List.hd ids)^"cont") "LabeledFormula"
                else dressedcont (String.lowercase (List.hd ids)^"cont")
            in build_term_aux1 term ex
    |Ast.Variable(id,Ast.All) ->
            let hist = List.hd ids in
            let (outer,inner,_,_) = Hashtbl.find hist_table hist in
            let ex =  nakedcont (String.lowercase hist^"cont") inner in
            (* FIXME: this bit to refactor *)
            <:expr< fun sbl hist varl ->
                List.map (fun varhist ->
                    match varhist#find $str:id$ with 
                    [$List.hd term_type$ -> $ex$
                    |_ -> failwith ("__build")
                    ]
                ) varl
            >>
    |Ast.History(_)
    |Ast.Variable(_,_) ->
            let hist = List.hd ids in
            let (outer,inner,_,_) = Hashtbl.find hist_table hist in
            let ex =
                match outer, action with
                |"Singleton",_ -> nakedcont (String.lowercase hist^"cont") inner
                |_, true -> <:expr< $lid:String.lowercase hist^"cont"$#elements >>
                |_, false -> <:expr< $lid:String.lowercase hist^"cont"$ >>
            in build_term_aux1 term ex
    |Ast.Const(id) ->
            let ex = <:expr< Constant($str:id$) >> in
            if naked then <:expr< fun _ _ _ -> $ex$ >>
            else <:expr< fun sbl _ _ ->
                match sbl#find $str:id$ with
                [`Set cont -> cont#head
                |_ -> failwith ("__build")]
                >>
    |_ -> 
            if List.length ids = 0 then
                <:expr< fun _ _ _ -> [`LabeledFormula ([], $expr$)] >>
            else if Option.is_none ruleid then build_term_aux2 term
            else
                let l = Hashtbl.find rule_table (Option.get ruleid) in
                if List.mem (patt_to_string ~generic:false term) l
                then build_term_aux3 term
                else build_term _loc ~naked:naked ~action:action term
;;

let expand_constant _loc s =
    let ex =
        <:expr<
        try List.find (fun
            [`LabeledFormula (_,(Constant ($str:s$))) -> True
            |_ -> False ]
            ) fl
        with [ Not_found -> raise FailedMatch ]
        >>
    in
    <:expr< fun sbl fl -> let f = $ex$ in sbl#add [ ( $str:s$, [f] ) ] >>
;;

let rec expand_expression_patt _loc = function
    |Ast.Filter("__single",[Ast.Term t]) ->
            (new_id "single", expand_single _loc t)
    |Ast.Filter("__empty",[Ast.Term t]) ->
            (new_id "empty", expand_single _loc t)
    |Ast.Term(Ast.Const(s)) -> (new_id "const", expand_constant _loc s)
    |Ast.Term(t) -> (new_id "set", expand_set _loc t)
    |_ -> failwith "expand_expression_patt not implemented"
;;

let rec expand_expression_expr ?ruleid ?(action=false) ?(naked=false) _loc = function
    |Ast.Term(Ast.Expr(e)) -> (new_id "term", e)
    |Ast.Term(t) -> (new_id "term", build_term ?ruleid ~action:action _loc t)
    |Ast.Apply("__simpl",Ast.Term t::l) ->
            let aux_fun =
                    List.map (function
                    |Ast.Apply("__simplarg",[Ast.Term t1]) ->
                            (new_id "term", build_term ?ruleid ~naked:true _loc t1)
                    |Ast.Apply("__simplarg",[e]) ->
                            expand_expression_expr ?ruleid ~action:true ~naked:true _loc e
                    |_ -> failwith "expand_expression_expr not implemented 3"
                    ) l
            in
            let (id,term) = (new_id "term", build_term ?ruleid _loc t) in
            let mapt = 
                List.map (fun (h,_) -> <:expr< $lid:h$ sbl hist varl >>) aux_fun
            in
            let sublist = list_to_exprlist _loc mapt in
            let pel = List.map (fun (s,e) ->
                (<:patt< $lid:s$ >>,e)) ((id,term)::aux_fun)
            in
            let appex =
                <:expr<
                let $list:pel$ in
                fun sbl hist varl ->
                    (List.fold_left (fun l (_,t) ->
                        Basictype.map (fun phi ->
                            match Logic.__simplification.val with
                            [None -> failwith "SIMPLIFICATION not defined"
                            |Some(sfun) -> sfun t phi]
                            ) l
                        ) ($lid:id$ sbl hist varl) $sublist$ 
                    )
                >>
            in (new_id "apply", appex )
    |Ast.Apply(f,[]) -> (new_id "apply", <:expr< fun _ _ _ -> $lid:f$ () >>)
    |Ast.Apply(f,l) ->
            let aux_fun = List.map (function
                |Ast.Term(Ast.Expr(e)) -> (new_id "term", <:expr< fun _ _ -> $e$ >>)
                |Ast.Term(t) -> (new_id "term", build_term ?ruleid _loc t)
                |Ast.List(l) -> 
                        let exl =
                            List.map(fun e ->
                                expand_expression_expr ?ruleid ~action:true ~naked:true _loc e
                            ) l
                        in
                        let pel =
                            List.map (fun (s,e) ->
                                (<:patt< $lid:s$ >>,e)) exl
                        in
                        let args =
                            list_to_exprlist _loc (
                                List.map (fun (s,_) ->
                                    <:expr< $lid:s$ sbl hist varl >>) exl
                            )
                        in
                        let ex = <:expr< let $list:pel$ in fun sbl hist varl -> $args$ >>
                        in (new_id "term", ex)
                |e ->  expand_expression_expr ?ruleid ~action:true ~naked:true _loc e
                ) l
            in
            let args = List.map (fun (s,_) -> <:expr< $lid:s$ sbl hist varl >>) aux_fun in
            let pel = List.map (fun (s,e) -> (<:patt< $lid:s$ >>,e)) aux_fun in
            let appex =
                <:expr<
                let $list:pel$ in
                fun sbl hist varl ->
                    $lid:f$ ( $list:args$ )
                >>
            in (new_id "apply", appex )

    |_ -> failwith "expand_expression_expr not implemented 1"
;;

let expand_status _loc s =
    let ex = 
        <:expr<
        fun varhist ->
            match varhist#find "status" with
            [`Singleton s ->
                varhist#add "status" (`Singleton (s#empty#add (`String $str:s$)))
            | _ -> failwith "down_axiom"]
        >>
    in (new_id "status", ex)
;;

let expand_rule_num _loc name (Ast.Numerator numlist) =
    List.map (fun n ->
        let (nid,nfun) = expand_expression_patt _loc n in
        let pid = new_id "pattern" in
        let sid = add_patt_table _loc name n in
        let ex = <:expr<
            let $lid:nid$ = $nfun$ in
            NodePattern.newpatt $str:sid$ $lid:nid$
            >>
        in (pid,ex)
    ) numlist
;;

let expand_condition _loc name (condlist) =
    List.map (fun Ast.CCondition e ->
        expand_expression_expr _loc ~ruleid:name e
    ) condlist
;;

let expand_denominator _loc name = function
    |Ast.Denominator denlist ->
            List.map (fun n ->
                let (nid,nfun) = expand_expression_expr _loc ~ruleid:name ~action:true n in
                let pid = new_id "action" in
                let sid = find_patt_table _loc n in
                let ex = <:expr<
                    let $lid:nid$ = $nfun$ in
                    NodePattern.newact $str:sid$ $lid:nid$
                    >>
                in (pid,ex)
            ) denlist
    |Ast.Status(s) -> [expand_status _loc s] 
;;

let expand_rule_denlist _loc name denlist =
    List.map (expand_denominator _loc name) denlist
;;

let expand_action _loc name actionlist =
    List.map (function
        |Ast.AAssign(t,e) ->
                let (idf, exf) = expand_expression_expr _loc ~ruleid:name e in
                let hist = List.hd (get_term_ids t) in
                let (outer,inner,ex,_) = Hashtbl.find hist_table hist in
                let id = new_id "assign" in
                let tid = <:expr< $str:hist$ >> in
                let ass = 
                    match outer with
                    |"Singleton" -> 
                            <:expr<
                            `$outer$ (($ex$)#add (`$inner$ ($lid:idf$ sbl hist varl))) >>
                    |_ -> <:expr< `$outer$ ($lid:idf$ sbl hist varl) >>
                in
                let pel = [(<:patt< $lid:idf$ >>,exf)] in
                let ex = <:expr<
                    let $list:pel$ in fun sbl hist varl ->
                        ( $list:[tid;ass]$ ) >>
                in (id,ex)
        |Ast.AFunction(e) -> expand_expression_expr _loc ~ruleid:name e
    ) actionlist
;;

let expand_rule_actionlist _loc name actionlist =
    List.map (expand_action _loc name) actionlist
;;

let expand_rule_branchcondlist _loc name branchcondlist =
    List.map (expand_condition _loc name) branchcondlist
;;

let is_axiom = function |[Ast.Status(s)] -> true |_ -> false ;;

let expand_ruledown _loc ruletype condition denlist numlist actionlist =
    if is_axiom denlist then 
        let axiom_arg = List.hd numlist in
        <:expr< UserRule.down_axiom name context $axiom_arg$ >>
    else
        match ruletype,condition with
        |Ast.NotInvertible,Ast.CCondition(Ast.Apply("linear",[])) ->
                let num = List.hd numlist in
                let act = List.hd actionlist in
                <:expr< UserRule.down_implicit name context $num$ $act$ >>
        |_,_ ->
            let da =
                let i = ref 1 in
                list_to_exprlist _loc (
                    List.map2 (fun nl al ->
                        let node =
                            if !i = 1 then <:expr< n >>
                            else <:expr< n#copy >>
                        in
                        incr i;
                        <:expr< ( $node$ , $nl$, $al$ ) >>
                    ) numlist actionlist
                )
            in <:expr< UserRule.down_explicit name context (fun n -> $da$ ) >>
;;

let expand_ruleup _loc ruletype condition denlist brlist btlist =
    let bt_arg = list_to_exprlist _loc btlist in
    let d = List.length denlist in
    let add_rule rule ll =
        let n = List.length ll in
        let rec def acc = function
            |0 -> acc
            |i -> def ([]::acc) (i-1)
        in
        let defll = ll@(def [] (d-n)) in
        match defll with 
        |[] -> <:expr< [ [ $rule$ ] ] >>
        |ll -> list_to_exprlist _loc (
                List.map (fun l ->
                    list_to_exprlist _loc (rule::l)
                ) ll
            )
    in
    let ll_to_exprll ll =
        list_to_exprlist _loc (
            List.map (fun l -> list_to_exprlist _loc l) ll
        )
    in
    let opencond = <:expr< UserRule.is_open >> in
    let closedcond = <:expr< UserRule.is_closed >> in
    if is_axiom denlist then
        let br_arg = list_to_exprlist _loc (List.flatten (brlist@[btlist])) in
        <:expr< UserRule.up_explore_linear context treelist $br_arg$ >>
    else
        match ruletype,condition with
        |Ast.Invertible,Ast.CCondition(Ast.Apply("linear",[])) ->
                <:expr< UserRule.up_explore_linear context treelist $bt_arg$ >>
        |Ast.NotInvertible,Ast.CCondition(Ast.Apply("linear",[])) ->
                let br_arg = add_rule opencond brlist in
                <:expr< UserRule.up_explore_implicit context treelist $bt_arg$ $br_arg$ >>

        |Ast.Invertible,Ast.CCondition(Ast.Apply("forall",[])) ->
                let br_arg = add_rule closedcond brlist in
                <:expr< UserRule.up_explore_simple context treelist $bt_arg$ $br_arg$ >>
        |Ast.NotInvertible,Ast.CCondition(Ast.Apply("forall",[])) ->
                let br_arg = add_rule opencond brlist in
                <:expr< UserRule.up_explore_simple context treelist $bt_arg$ $br_arg$ >>

        |Ast.Invertible,Ast.CCondition(Ast.Apply("exists",[])) ->
                let br_arg = add_rule opencond brlist in
                <:expr< UserRule.up_explore_simple context treelist $bt_arg$ $br_arg$ >>
        |Ast.NotInvertible,Ast.CCondition(Ast.Apply("exists",[])) ->
                let br_arg = add_rule closedcond brlist in
                <:expr< UserRule.up_explore_simple context treelist $bt_arg$ $br_arg$ >>

        |Ast.Invertible,Ast.CCondition(Ast.Apply("user",[])) 
        |Ast.NotInvertible,Ast.CCondition(Ast.Apply("user",[])) ->
                let br_arg = ll_to_exprll brlist in
                <:expr< UserRule.up_explore_simple context treelist $bt_arg$ $br_arg$ >>

        |_,_ -> failwith "Rule badly specified"
;;

let expand_num_triple _loc (Ast.Numerator numl) num_args =
    List.fold_left (fun (empty,single,set) (e,(id,_)) ->
        let exid = <:expr< $lid:id$ >> in
        match e with
        |Ast.Filter("__single",[Ast.Term t]) ->
                if is_var t then (empty,exid::single,set)
                else (empty,single@[exid],set)
        |Ast.Filter("__empty",[Ast.Term t]) ->
                if is_var t then (exid::empty,single,set)
                else (empty@[exid],single,set)
        |_ -> (empty,single,exid::set)
    ) ([],[],[]) (List.combine numl num_args)
;;

let expand_rule _loc (Ast.Rule r) =
    let (
        name,
        ruletype,
        num,
        (denlist,cond),
        condlist,
        actionlist,
        branchcondlist,
        backtracklist,
        cache) = r
    in

    (* numerator *)
    let numl = expand_rule_num _loc name num in
    let nump = List.map (fun (s,e) ->
        <:str_item< value $lid:s$ = $e$ >>) numl
    in
    let num_args =
        let (empty,single,set) = expand_num_triple _loc num numl in
        let exemptyl = list_to_exprlist _loc (List.rev empty) in
        let exsinglel = list_to_exprlist _loc (List.rev single) in
        let exsetl = list_to_exprlist _loc (List.rev set) in
        <:expr< ( $exemptyl$, $exsinglel$ , $exsetl$ ) >>
    in
    let num_aux_fun = <:str_item< declare $list:nump$ end >> in

    (* side condition on the numerator *)
    let condl = expand_condition _loc name condlist in
    let condp = List.map (fun (s,e) ->
        <:str_item< value $lid:s$ = $e$ >>) condl
    in
    let cond_args = list_to_exprlist _loc (
        List.map (fun (s,_) -> <:expr< $lid:s$ >> ) condl
    ) in
    let cond_aux_fun = <:str_item< declare $list:condp$ end >> in

    (* denominators *)
    let denll = expand_rule_denlist _loc name denlist in
    let den_args = 
            List.map (fun denl ->
                list_to_exprlist _loc (
                    List.map (fun (s,_) -> <:expr< $lid:s$ >> ) denl
                )
            ) denll
    in
    let denp = 
        List.flatten (
            List.map (fun denl ->
                List.map (fun (s,e) ->
                    <:str_item< value $lid:s$ = $e$ >>
                ) denl
            ) denll
        )
    in
    let den_aux_fun = <:str_item< declare $list:denp$ end >> in

    (* actions on the denominators *)
    let actionll = expand_rule_actionlist _loc name actionlist in
    let action_args = 
            List.map (fun actionl ->
                list_to_exprlist _loc (
                    List.map (fun (s,_) -> <:expr< $lid:s$ >> ) actionl
                )
            ) actionll
    in
    let actionp = 
        List.flatten (
            List.map (fun actionl ->
                List.map (fun (s,e) ->
                    <:str_item< value $lid:s$ = $e$ >>
                ) actionl
            ) actionll
        )
    in
    let action_aux_fun = <:str_item< declare $list:actionp$ end >> in

    (* branch conditions *)
    let branchcondll = expand_rule_branchcondlist _loc name branchcondlist in
    let branchcond_args = 
        List.map (fun branchcondl ->
                List.map (fun (s,_) -> <:expr< $lid:s$ >> ) branchcondl
        ) branchcondll
    in
    let branchcondp = 
        List.flatten (
            List.map (fun branchcondl ->
                List.map (fun (s,e) ->
                    <:str_item< value $lid:s$ = $e$ >>
                ) branchcondl
            ) branchcondll
        )
    in
    let branchcond_aux_fun = <:str_item< declare $list:branchcondp$ end >> in

    let alist l =
        let rec def acc = function
            |0 -> acc
            |i -> def (<:expr< []>>::acc) (i-1)
        in
        let n = List.length den_args - List.length l in
        if n != 0 then l @ (def [] n)
        else l 
    in

    (* backtrack *)
    let backtrackl = expand_action _loc name backtracklist in
    let backtrackp = List.map (fun (s,e) ->
        <:str_item< value $lid:s$ = $e$ >>) backtrackl
    in
    let backtrack_args = List.map (fun (s,_) -> <:expr< $lid:s$ >> ) backtrackl in
    let backtrack_aux_fun = <:str_item< declare $list:backtrackp$ end >> in

    let num_fun = <:expr< UserRule.check name node $num_args$ $cond_args$ >> in
    let den_fun = expand_ruledown _loc ruletype cond denlist den_args (alist action_args) in
    let up_fun  = expand_ruleup _loc ruletype cond denlist branchcond_args backtrack_args in

    let cache_ex =
        if Option.is_none cache then <:expr< False >>
        else <:expr< True >>
    in

    let rule_class = 
        <:str_item<
            class $lid:(String.lowercase name)^"_rule"$ =
                object
                inherit Rule.rule;

                value name = $str:name$;
                method check node = $num_fun$ ;
                method down context = $den_fun$ ;
                method up context treelist = $up_fun$ ;
                method use_cache = $cache_ex$ ;
                end
     >>
    in <:str_item<
    declare $list:[
        num_aux_fun;
        cond_aux_fun;
        den_aux_fun;
        action_aux_fun;
        branchcond_aux_fun;
        backtrack_aux_fun;
        rule_class
    ]$ end >>
;;

let expand_tableau _loc (Ast.Tableau rulelist ) =
    let l = List.map ( expand_rule _loc ) rulelist in
    let mp = expand_matchpatt _loc in
    if Hashtbl.length hist_table = 0 then
        let h = expand_histories _loc (Ast.Histories([]))
        in <:str_item< declare $list:mp::h::l$ end >>
    else  <:str_item< declare $list:mp::l$ end >>
;;

let rec expand_tactic _loc = function
    |Ast.TVar(id) -> <:expr< $lid:id$ >>
    |Ast.Basic(uid) ->
            let id = String.lowercase uid in
            <:expr< Rule( new $lid:id^"_rule"$ ) >>
    |Ast.Seq(t1,t2) ->
            let ext1 = expand_tactic _loc t1 in
            let ext2 = expand_tactic _loc t2 in
            <:expr< Seq( $list:[ext1;ext2]$ ) >>
    |Ast.Alt(t1,t2) ->
            let ext1 = expand_tactic _loc t1 in
            let ext2 = expand_tactic _loc t2 in
            <:expr< Alt( $list:[ext1;ext2]$ ) >>
    |Ast.Repeat(t) ->
            let ext = expand_tactic _loc t in
            <:expr< Repeat( $ext$ ) >>
;;

let expand_strategy _loc (Ast.Strategy t) =
    let ext = expand_tactic _loc t in
    let str =
        <:str_item< Logic.__strategy.val := Some(Strategy.strategy $ext$) >>
    in
    let main = <:str_item< Twb.main () >> in
    <:str_item< declare $list:[str;main]$ end >>
;;

let expand_preproc _loc e =
    <:str_item< Logic.__pp.val := Some(Basictype.map $e$) >>
;;

let expand_negation _loc e =
    <:str_item< Logic.__neg.val := Some(Basictype.map $e$) >>
;;

let expand_exit _loc f =
    let (exid,exfun) = expand_expression_expr _loc f in
    let exitp = <:str_item< value $lid:exid$ = $exfun$ >> in
    let ex =
        <:expr< fun v ->
            $lid:exid$ (new Substitution.substitution) (History.make ()) v  >>
    in
    let decl = <:str_item< Logic.__exit.val := Some($ex$) >> in
     <:str_item< declare $list:[exitp;decl]$ end >>
;;

let expand_options _loc olist =
    let ol = 
        list_to_exprlist _loc (
            List.map (fun Ast.Options (s,e,a) ->
                <:expr< ( $str:s$, $e$, $str:a$ ) >>
            ) olist
        )
    in
    <:str_item< Logic.__options.val := Some ([ $list:ol$ ]) >>
;;

let expand_rewrite_expr _loc = function
    |Ast.Term(Ast.Expr(e)) -> <:expr< $e$ >>
    |Ast.Term(t) -> <:expr< $expand_term_expr _loc t$ >>
    |Ast.Apply("__substitute",[Ast.Term v; Ast.Term s ; Ast.Term t]) ->
            let ext = expand_term_expr _loc t in
            let exs = expand_term_expr _loc s in
            let exv = expand_term_expr _loc v in
            <:expr< __substitute $exs$ $ext$ $exv$ >>
    |_ -> failwith "expand_expression_expr not implemented 1"
;;

let expand_rewrite_patt _loc = function
    |Ast.Term(t) -> <:patt< $expand_term_patt _loc t$ >>
    |_ -> failwith "expand_pattession_patt not implemented 1"
;;

let expand_simplification _loc ex =
    <:str_item< Logic.__simplification.val := Some($ex$) >>
;;

let expand_connectives _loc clist =
      let preamble = expand_preamble _loc in
      let pa = expand_parser _loc clist in
      let pr = expand_printer _loc clist in
      let sb = expand_substitute _loc clist in
      <:str_item< declare $list:preamble@[pa;pr;sb]$ end >>
;;

