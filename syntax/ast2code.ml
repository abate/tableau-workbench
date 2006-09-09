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
                        Some <:patt< `Formula $uid:id$ ($term_patt t1$,$term_patt t2$) >>
                    |Ast.Ucon(id,t) -> Some <:patt< `Formula $uid:id$ ($term_patt t$) >>
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
    let atom = ( <:patt< `Formula Atom(_) >>, None, <:expr< "__atom" >>) in
    let const = ( <:patt< `Formula Constant(_) >>, None, <:expr< "__const" >>) in
    let id = <:patt< __matchpatt >> in
    let ex1 = <:expr< fun [ $list:pel@[atom;const;def]$ ] >> in
    let ex2 = <:expr< Logic.__matchpatt.val := Some(__matchpatt) >> in
    let st1 = <:str_item< value rec $list:[(id,ex1)]$ >> in
    let st2 = <:str_item< value _ = $ex2$ >>
    in <:str_item< declare $list:[st1;st2]$ end >>
;;

let rec build_hist_type t =
    let all_basic =
        List.for_all (function |Ast.Type(id) -> true |_ -> false)
    in
    let rec aux = function
        |Ast.Type("Set") 
        |Ast.Type("List") -> failwith "basic type not specified : Ex: Set of Formula"
        |Ast.Type(id) -> id 
        |Ast.Container("Set",l) when all_basic l -> "Set"
        |Ast.Container(id,l) -> id ^ (inner l)
    and inner l =
        List.fold_left (fun s ->
            function
                |Ast.Type(id) -> s
                |e -> s ^ (aux e)
            ) "" l
    in
    match t with
    |Ast.Type("Set") 
    |Ast.Type("List") -> failwith "basic type not specified : Ex: Set of Formula"
    |Ast.Type(id) -> ("Singleton",id)
    |Ast.Container("Set",l) -> ("Set", inner l)
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
            let status = 
                Ast.VDecl("status",
                Ast.Type("String"),
                <:expr< new Set.set >>,
                Some <:expr< "Open" >>)
            in status::histlist 
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
        <:patt< `List $lid:String.lowercase id^"cont"$ >>
;;

let rec expand_term_cont _loc term id =
    if Hashtbl.mem hist_table id then
        match term with
        |Ast.Variable(id,Ast.Int(vi)) ->
                <:expr<
                let varhist = List.nth varl ($int:string_of_int vi$ - 1) 
                in varhist#find $str:id$ >>
        |Ast.History(id) -> <:expr< hist#find $str:id$ >>
        |_ -> failwith "expand_term_cont"
    else <:expr< sbl#find $str:id$ >>
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
    let ids_list = list_to_exprlist _loc (
        List.map (fun x -> <:expr< $str:x$ >> ) ids
        )
    in
    let frl = List.map (fun x -> <:expr< `Formula $lid:x$ >> ) ids in
    let frl_list = list_to_exprlist _loc frl in
    match term with
    |Ast.Var(id) -> <:expr< fun sbl fl -> sbl#add [($str:id$,fl)] >>
    |_ ->
            <:expr<
            fun sbl fl ->
                let __rec = fun
                    [`Formula $patt$ -> $frl_list$
                    |`Formula _ -> raise FailedMatch
                    |_ -> failwith ("set : type mismatch")]
                in sbl#add (ExtList.fold __rec fl $ids_list$)
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
        List.map (fun x -> <:expr< `Formula $lid:x$ >> ) ids
        )
    in
    let act =
        (<:patt< `Formula $patt$ >>, None,
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
        match term with
        |Ast.Var(id) -> 
            [(<:patt< _ >>, None, <:expr< failwith ("single : type mismatch") >>)]
        |_ ->
            [(<:patt< `Formula _ >>, None, <:expr< raise FailedMatch >>);
             (<:patt< _ >>, None, <:expr< failwith ("single : type mismatch") >>)]
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

let build_term _loc ?(naked=false) ?(action=false) term =
    let ids = unique (get_term_ids term) in
    let expr = expand_term_expr _loc term in
    let term_type = List.map (expand_term_type _loc) ids in
    let term_cont = List.map (expand_term_cont _loc term) ids in
    let patt_list = List.map (fun x -> <:patt< `Formula $lid:x$ >> ) ids in
    let dressedcont id = <:expr< $lid:id$#elements >> in
    let nakedcont id inner =
        <:expr<
        match $lid:id$#head with
            [`$inner$ i -> i
            |_ -> failwith "__build"]
        >>
    in
    let build_term_aux1 term ex = 
        <:expr<
        fun sbl hist varl ->
            match ( $list:term_cont$ ) with
            [( $list:term_type$ ) -> $ex$
            |_ -> failwith ("__build")
            ]
        >>
    in
    let build_term_aux2 term = 
        let term_elem = 
            List.map (fun x -> dressedcont (String.lowercase x^"cont") ) ids
        in
            <:expr<
            fun sbl hist varl ->
                match ( $list:term_cont$ ) with
                [( $list:term_type$ ) ->
                    ExtList.$lid:"map"^string_of_int(List.length ids)$ (fun
                        [( $list:patt_list$ ) -> `Formula $expr$
                        |_ -> failwith ("__build")
                        ]
                    ) ( $list:term_elem$ )
                |_ -> failwith ("__build")
                ]
            >>
    in
    match term with
    |Ast.Var(_) ->
            let ex =
                if naked then nakedcont (String.lowercase (List.hd ids)^"cont") "Formula"
                else dressedcont (String.lowercase (List.hd ids)^"cont")
            in build_term_aux1 term ex
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
            else <:expr< fun _ _ _ -> `Formula $ex$ >>
    |_ -> build_term_aux2 term
;;

let expand_constant _loc s =
    let ex =
        <:expr<
        try List.find (fun
            [`Formula (Constant ($str:s$)) -> True
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

let rec expand_expression_expr ?(action=false) _loc = function
    |Ast.Term(Ast.Expr(e)) -> (new_id "term", e)
    |Ast.Term(t) -> (new_id "term", build_term ~action:action _loc t)
    |Ast.Apply("__simpl",Ast.Term t::l) ->
            let aux_fun =
                List.flatten (
                    List.map (function
                    |Ast.Apply("__simpl",[Ast.Term s;Ast.Term v]) ->
                            [(new_id "term", build_term ~naked:true _loc s);
                             (new_id "term", build_term ~naked:true _loc v)]
                    |_ -> failwith "expand_expression_expr not implemented 3"
                    ) l
                )
            in
            let (id,term) = (new_id "term", build_term _loc t) in
            let rec mapt = function
                |(s1,_)::(s2,_)::t ->
                        let t1 = <:expr< $lid:s1$ sbl hist varl >> in
                        let t2 = <:expr< $lid:s2$ sbl hist varl >> in
                        <:expr< ( $list:[t1;t2]$ ) >> :: mapt t
                |[] -> []
                |_ -> failwith "expand_expression_expr"
            in
            let sublist = list_to_exprlist _loc (mapt aux_fun) in
            let pel = List.map (fun (s,e) ->
                (<:patt< $lid:s$ >>,e)) ((id,term)::aux_fun)
            in
            let appex =
                <:expr<
                let $list:pel$ in
                fun sbl hist varl ->
                    __simplification (List.fold_left (fun l (s,v) ->
                            Basictype.map (fun t -> __substitute t s v) l
                        ) ($lid:id$ sbl hist varl) $sublist$ 
                    )
                >>
            in (new_id "apply", appex )
    |Ast.Apply(f,[]) -> (new_id "apply", <:expr< fun _ _ _ -> $lid:f$ () >>)
    |Ast.Apply(f,l) ->
            let aux_fun = List.map (function
                |Ast.Term(Ast.Expr(e)) -> (new_id "term", <:expr< fun _ _ -> $e$ >>)
                |Ast.Term(t) -> (new_id "term", build_term _loc t)
                |_ -> failwith "expand_expression_expr not implemented 2"
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

let expand_rule_num _loc (Ast.Numerator numlist) =
    List.map (fun n ->
        let (nid,nfun) = expand_expression_patt _loc n in
        let pid = new_id "pattern" in
        let sid = add_patt_table _loc n in
        let ex = <:expr<
            let $lid:nid$ = $nfun$ in
            NodePattern.newpatt $str:sid$ $lid:nid$
            >>
        in (pid,ex)
    ) numlist
;;

let expand_condition _loc (condlist) =
    List.map (fun Ast.CCondition e ->
        expand_expression_expr _loc e
    ) condlist
;;

let expand_denominator _loc = function
    |Ast.Denominator denlist ->
            List.map (fun n ->
                let (nid,nfun) = expand_expression_expr ~action:true _loc n in
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

let expand_rule_denlist _loc denlist =
    List.map (expand_denominator _loc) denlist
;;

let expand_action _loc actionlist =
    List.map (function
        |Ast.AAssign(t,e) ->
                let (idf, exf) = expand_expression_expr _loc e in
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
        |Ast.AFunction(e) -> expand_expression_expr _loc e
    ) actionlist
;;

let expand_rule_actionlist _loc actionlist =
    List.map (expand_action _loc) actionlist
;;

let expand_rule_branchcondlist _loc branchcondlist =
    List.map (expand_condition _loc) branchcondlist
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
        let br_arg = ll_to_exprll brlist in
        <:expr< UserRule.up_explore_linear context treelist $br_arg$ >>
    else
        match ruletype,condition with
        |Ast.Invertible,Ast.CCondition(Ast.Apply("linear",[])) ->
                <:expr< UserRule.up_explore_linear context treelist $bt_arg$ >>
        |Ast.NotInvertible,Ast.CCondition(Ast.Apply("linear",[])) ->
                let br_arg = add_rule opencond brlist in
                <:expr< UserRule.up_explore_simple context treelist $bt_arg$ $br_arg$ >>

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
            |Ast.Filter("__single",_) -> (empty,exid::single,set)
            |Ast.Filter("__empty",_) -> (exid::empty,single,set)
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
        backtracklist) = r
    in

    (* numerator *)
    let numl = expand_rule_num _loc num in
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
    let condl = expand_condition _loc condlist in
    let condp = List.map (fun (s,e) ->
        <:str_item< value $lid:s$ = $e$ >>) condl
    in
    let cond_args = list_to_exprlist _loc (
        List.map (fun (s,_) -> <:expr< $lid:s$ >> ) condl
    ) in
    let cond_aux_fun = <:str_item< declare $list:condp$ end >> in

    (* denominators *)
    let denll = expand_rule_denlist _loc denlist in
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
    let actionll = expand_rule_actionlist _loc actionlist in
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
    let branchcondll = expand_rule_branchcondlist _loc branchcondlist in
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
    let backtrackl = expand_action _loc backtracklist in
    let backtrackp = List.map (fun (s,e) ->
        <:str_item< value $lid:s$ = $e$ >>) backtrackl
    in
    let backtrack_args = List.map (fun (s,_) -> <:expr< $lid:s$ >> ) backtrackl in
    let backtrack_aux_fun = <:str_item< declare $list:backtrackp$ end >> in

    let num_fun = <:expr< UserRule.check name node $num_args$ $cond_args$ >> in
    let den_fun = expand_ruledown _loc ruletype cond denlist den_args (alist action_args) in
    let up_fun  = expand_ruleup _loc ruletype cond denlist branchcond_args backtrack_args in

    let rule_class = 
        <:str_item<
            class $lid:(String.lowercase name)^"_rule"$ =
                object
                inherit Rule.rule;

                value name = $str:name$;
                method check node = $num_fun$ ;
                method down context = $den_fun$ ;
                method up context treelist = $up_fun$ ;
                method use_cache = False ;
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
    |Ast.Apply("__substitute",[Ast.Term t; Ast.Term e ; Ast.Term s]) ->
            let ext = expand_term_expr _loc t in
            let exe = expand_term_expr _loc e in
            let exs = expand_term_expr _loc s in
            <:expr< __substitute $ext$ $exe$ $exs$ >>
    |_ -> failwith "expand_expression_expr not implemented 1"
;;

let expand_rewrite_patt _loc = function
    |Ast.Term(t) -> <:patt< $expand_term_patt _loc t$ >>
    |_ -> failwith "expand_pattession_patt not implemented 1"
;;


