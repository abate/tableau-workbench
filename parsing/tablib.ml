(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Parselib

let rec expand_pa_term = function
    |Ast.PaConn(id,l) -> <:patt< `$uid:id$($list:List.map expand_pa_term l$) >>
    |Ast.PaCons(id)   -> <:patt< ( `$uid:id$ as $lid:String.lowercase id$ ) >>
    |Ast.PaAtom(s)    -> <:patt< ( `Atom _ as $lid:String.lowercase s$ ) >>
    |Ast.PaVar(s)     -> <:patt< $lid:String.lowercase s$ >>
    |Ast.PaVari(s,i)  ->  failwith "not yet"
    |Ast.PaHist(s)    ->  failwith "not yet"

let rec expand_pa_expr = function
    |Ast.PaTerm(t)       -> <:patt< $expand_pa_term t$ >>
    |Ast.PaLabt(label,t) -> <:patt< ($label$, $expand_pa_term t$) >>
    |Ast.PaTupl(l)       -> <:patt< ($list:List.map expand_pa_expr l$) >>
    |Ast.PaPatt(pa)      -> pa

let rec extract_pa_term_vars acc = function
    |Ast.PaConn(id,l) -> (List.flatten (List.map (extract_pa_term_vars []) l)) 
    |Ast.PaCons(s) |Ast.PaAtom(s)
    |Ast.PaVar(s)  |Ast.PaHist(s) -> s::acc
    |Ast.PaVari(s,i)  -> s::acc

let rec extract_ex_term_vars acc = function
    |Ast.ExConn(id,l) -> (List.flatten (List.map (extract_ex_term_vars []) l)) 
    |Ast.ExCons(s) |Ast.ExAtom(s) |Ast.ExVar(s) |Ast.ExHist(s) -> (String.lowercase s)::acc
    |Ast.ExVari(s,i)  -> (String.lowercase s)::acc

let rec extract_patt_vars acc = function
    |MLast.PaAny(_)   -> acc 
    |MLast.PaLid(_,s) -> (String.lowercase s)::acc
    |MLast.PaVrn(_,s) -> (String.lowercase s)::acc
    |MLast.PaTup(_,l) -> (List.flatten (List.map (extract_patt_vars []) l)) @ acc 
    |MLast.PaArr(_,l) -> (List.flatten (List.map (extract_patt_vars []) l)) @ acc
    |_ -> acc

let rec extract_expr_vars acc = function
    |MLast.ExLid(_,s) -> (String.lowercase s)::acc
    |MLast.ExVrn(_,s) -> (String.lowercase s)::acc
    |MLast.ExTup(_,l) -> (List.flatten (List.map (extract_expr_vars []) l)) @ acc 
    |MLast.ExArr(_,l) -> (List.flatten (List.map (extract_expr_vars []) l)) @ acc
    |MLast.ExSeq(_,l) -> (List.flatten (List.map (extract_expr_vars []) l)) @ acc
    |MLast.ExApp(_,e1,e2) -> (extract_expr_vars [] e1) @ (extract_expr_vars [] e2)
    |_ -> acc

let rec extract_pa_expr_vars = function
    |Ast.PaTerm(t) ->
            List.map (fun id -> 
                (<:expr< $str:id$ >>,<:expr< `Term $lid:String.lowercase id$ >>) )
            (extract_pa_term_vars [] t)
    |Ast.PaLabt(label,t) ->
            List.append
                (List.map (fun id -> 
                    (<:expr< $str:id$ >>,<:expr< `Label $lid:String.lowercase id$ >>) )
                (extract_patt_vars [] label))
                (List.map (fun id ->
                    (<:expr< $str:id$ >>,<:expr< `Term $lid:String.lowercase id$ >>) )
                (extract_pa_term_vars [] t))
    |Ast.PaTupl(l) -> List.flatten (List.map extract_pa_expr_vars l)
    |Ast.PaPatt(pa) -> 
                (List.map (fun id -> 
                    (<:expr< $str:id$ >>,<:expr< `Label $lid:String.lowercase id$ >>) )
                (extract_patt_vars [] pa))

let pa_expr_to_string =
    let rec pa_term_to_string = function
        |Ast.PaAtom(s) -> "__atom"
        |Ast.PaCons(s) -> "__const"
        |Ast.PaConn(id,l) -> List.fold_left (fun s e -> s^(pa_term_to_string e)) id l
        |_ -> ""
    in function
        |Ast.PaTerm(t) -> pa_term_to_string t
        |Ast.PaLabt(_,t) -> pa_term_to_string t
        |_ -> failwith "pa_expr_to_string"

let ctyp_to_patt ctyp =
    let counter = ref 0 in
    let rec aux = function
        |MLast.TyTup(_,l)  -> <:patt< ($list:List.map aux l$) >>
        |MLast.TyLid(_,id) ->
                incr counter; 
                <:patt< $lid:"__t"^string_of_int !counter$ >>
        |MLast.TyAcc(_,_,ctyp) -> aux ctyp
        |_ -> failwith "ctyp_to_patt"
    in aux ctyp

let ctyp_to_method_expr m ctyp = 
    let counter = ref 0 in
    let rec aux = function
        |MLast.TyTup(_,l)  ->
                <:expr< ($list:List.map aux l$) >>
        |MLast.TyLid(_,"int")
        |MLast.TyLid(_,"string") -> 
                incr counter; 
                <:expr< $lid:"__t"^string_of_int !counter$ >>
        |MLast.TyLid(_,id) ->
                incr counter;
                begin match m with
                |"" -> <:expr< $lid:"__t"^string_of_int !counter$ >>
                |_ -> <:expr< $lid:"__t"^string_of_int !counter$#$lid:m$ >>
                end
        |MLast.TyAcc(_,_,ctyp) -> aux ctyp
        |_ -> failwith "ctyp_to_method_expr"
    in aux ctyp

let expand_history_type histlist =
    let ctyp_to_string_expr ctyp =
        let counter = ref 0 in
        let rec aux = function
            |MLast.TyTup(_,l)  ->
                    let f = List.fold_left (fun acc _ -> acc^",%s") "" l in
                    List.fold_left (fun acc arg ->
                        <:expr< $acc$ $arg$ >>
                    ) <:expr< Printf.sprintf $str:"("^f^")"$ >> (List.map aux l)
            |MLast.TyLid(_,"int") ->
                    incr counter; 
                    <:expr< string_of_int $lid:"__t"^string_of_int !counter$ >>
            |MLast.TyLid(_,"string") ->
                    incr counter; 
                    <:expr< $lid:"__t"^string_of_int !counter$ >>
            |MLast.TyLid(_,id) ->
                    incr counter; 
                    <:expr< $lid:"__t"^string_of_int !counter$#to_string >>
            |MLast.TyAcc(_,_,ctyp) -> aux ctyp
            |_ -> failwith "ctyp_to_string_expr"
        in aux ctyp
    in
    let tlist =
        let l =
            List.map (fun (id,var,ctyp,ex) ->
                <:ctyp< [= `$uid:var$ of $ctyp$ ] >>
            ) histlist
        in
        match l with
        |[] -> <:ctyp< [= ] >>
        |[hd] -> hd
        |hd::tl -> 
            List.fold_left (fun acc t ->
                <:ctyp< [= $acc$ | $t$ ] >>
            ) hd tl
    in
    let copylist =
        List.map (fun (id,var,ctyp,ex) ->
            (<:patt< `$uid:var$ $ctyp_to_patt ctyp$ >> , None, 
            <:expr< `$uid:var$ $ctyp_to_method_expr "copy" ctyp$ >>)
        ) histlist
    in
    let to_stringlist = 
        List.map (fun (id,var,ctyp,ex) ->
            (<:patt< `$uid:var$ $ctyp_to_patt ctyp$ >> , None, 
            <:expr< $ctyp_to_string_expr ctyp$ >>)
        ) histlist
    in 
    (tlist,copylist,to_stringlist) 

let expand_histories =
    let aux (id,ctyp,def) =
        let var = new_co "Hist" in
        Hashtbl.replace hist_table id (var,ctyp,def);
        (id,var,ctyp,def)
    in function
    |Ast.Variable(l) ->
            let l' = (List.map aux l) in
            let (tlist,copylist,to_stringlist) = expand_history_type l' in
            let exl = List.map (fun (id,var,_,def) ->
                    <:expr< ($str:id$ , `$uid:var$ $def$) >>
                ) l'
            in
            Hashtbl.add expr_table "varlist" (list_to_exprlist exl);
            <:str_item<
            module VarType =
              struct
                  type t = $tlist$ ;
                  value copy = fun [ $list:copylist$ ] ;
                  value to_string = fun [ $list:to_stringlist$ ] ;
              end    
            >>
    |Ast.History(l)  ->
            let l' = (List.map aux l) in
            let (tlist,copylist,to_stringlist) = expand_history_type l' in
            let exl =
                List.map (fun (id,var,_,def) ->
                    <:expr< ( $str:id$ , `$uid:var$ $def$ ) >>
                ) l'
            in
            Hashtbl.add expr_table "histlist" (list_to_exprlist exl);
            <:str_item<
            module HistType =
              struct
                  type t = $tlist$ ;
                  value copy = fun [ $list:copylist$ ] ;
                  value to_string = fun [ $list:to_stringlist$ ] ;
              end
            >>

let expand_principal expr =
    let (idlist,termlist) = List.split (extract_pa_expr_vars expr) in
    let act =
        ((expand_pa_expr expr), None,
        <:expr<
            List.map2
            (fun f s ->
                try if sbl#mem s f then [] else raise FailedMatch
                with [Not_found -> [f]]
            ) $list_to_exprlist termlist$ $list_to_exprlist idlist$
        >>)
    in
    let def = (<:patt< _ >>, None, <:expr< raise FailedMatch >>)
    in
    <:expr<
    fun sbl -> fun fl ->
        let __rec = fun [ $list:[act;def]$ ] in
        match (* $heuristic$ *) fl with
        [[] -> sbl#add (List.combine $list_to_exprlist idlist$ [[]])
        |[ h::_ ] -> sbl#add (List.combine $list_to_exprlist idlist$ (__rec h))
        ]
    >>

let expand_set pa_expr = 
    let (idlist,termlist) = List.split (extract_pa_expr_vars pa_expr) in
    if pa_expr_is_var pa_expr then
        <:expr<
        fun sbl fl ->
            let __rec = fun
                [ $expand_pa_expr pa_expr$ ->  $List.hd termlist$ ]
            in sbl#add [($List.hd idlist$, List.map __rec fl)]
        >>
    else
        <:expr<
        fun sbl fl ->
            let __rec = fun
                [ $expand_pa_expr pa_expr$ ->  $list_to_exprlist termlist$
                | _ -> raise FailedMatch ]
            in sbl#add (ExtList.fold __rec fl $list_to_exprlist idlist$)
        >>

let expand_arity_pa_expr t = function
    |Ast.Single | Ast.Empty -> expand_principal t
    |Ast.Set -> expand_set t

let expand_numcont index numcontlist =
        List.map (fun (arity, pa_expr) ->
            let nfun = expand_arity_pa_expr pa_expr arity in
            let nid = new_id "numcont" in
            let pid = new_id "pattern" in
            let ex = <:expr<
                let $lid:nid$ = $nfun$ in
                NodePattern.newpatt $int:string_of_int index$
                $str:pa_expr_to_string pa_expr$ $lid:nid$
                >>
            in (pid,ex)
        ) numcontlist

let expand_rule_num name (Ast.Numerator arr) =
    List.flatten (Array.to_list (Array.mapi expand_numcont arr))

let expand_num_triple numl (Ast.Numerator arr) =
    let aux num numl =
        List.fold_left (fun (empty,single,set) ((arity, pa_expr),(id,_)) ->
            let exid = <:expr< $lid:id$ >> in
            match arity with
            |Ast.Single->
                    if pa_expr_is_var pa_expr then (empty,exid::single,set)
                    else (empty,single@[exid],set)
            |Ast.Empty ->
                    if pa_expr_is_var pa_expr then (exid::empty,single,set)
                    else (empty@[exid],single,set)
            |Ast.Set -> (empty,single,exid::set)
        ) ([],[],[]) (List.combine num numl)
    in
    aux (List.flatten (Array.to_list arr)) numl

let rec expand_ex_term use = function
    |Ast.ExConn(id,l) as ex_term ->
            let rec aux = function
                |Ast.ExConn(id,l) -> <:expr< `$uid:id$($list:List.map aux l$) >>
                |Ast.ExCons(id)   -> <:expr< `$uid:id$ >>
                |Ast.ExAtom(s)    -> <:expr< `Atom $str:s$ >>
                |Ast.ExVar(s)     -> <:expr< $lid:String.lowercase s$ >>
                |Ast.ExVari(s,i)  ->  failwith "not yet"
                |Ast.ExHist(s)    ->  failwith "not yet"
            in
            let (exl,pel) =
                List.split (
                    List.map (fun (pa,ex) ->
                        (<:expr< $lid:pa$ sbl hist varl >>,
                        (<:patt< $lid:pa$ >>,
                        <:expr< fun sbl hist varl -> $ex$ >>))
                        (* XXX: does this really work ??? *)
                    ) (List.map (expand_ex_term `Var) l)
                )
            in
            let idlist =
                List.map (fun s -> <:patt< `Term $lid:s$ >>) 
                (extract_ex_term_vars [] ex_term)
            in
            (new_id "ex_expr",
            <:expr< let $list:pel$ in
            ExtList.$lid:"map"^string_of_int(List.length pel)$ (fun
                [( $list:idlist$ ) -> $aux ex_term$
                |_ -> failwith ("__build")
                ]
            ) ( $list:exl$ ) >>
            )
    |Ast.ExVar(id) |Ast.ExCons(id) |Ast.ExAtom(id) ->
            begin match use with
            |`List | `Obj ->
                (new_id "ex_term",
                <:expr<
                ExtList.map1 (fun
                    [`Term e -> e
                    |_ -> failwith ("__build")
                    ]
                ) ( try (sbl#find $str:id$)#elements
                    with [Not_found -> failwith ("__find: " ^ $str:id$)]) >>
                )
             |`Var ->
                (new_id "ex_term",
                <:expr<
                try (sbl#find $str:id$)#elements
                with [Not_found -> failwith ("__find: " ^ $str:id$)] >>
                )
            end
    |Ast.ExVari(id,Ast.Int i) ->
            let (var,ctyp,def) =
                try Hashtbl.find hist_table id
                with Not_found -> failwith ("History "^id^ "not declared")
            in begin match use with
            |`List ->
                (new_id "ex_term",
                <:expr<
                try
                    let varhist = List.nth varl ($int:string_of_int i$ - 1) in 
                    match varhist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ ->
                        $ctyp_to_method_expr "elements" ctyp$
                    | _ -> failwith "varhist"]
                    (varhist#find $str:id$)#elements
                with [Failure "nth" -> 1 ] >>
                )
            |`Obj |`Var ->
                (new_id "ex_term",
                <:expr<
                try
                    let varhist = List.nth varl ($int:string_of_int i$ - 1) in
                    match varhist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ -> $ctyp_to_method_expr "" ctyp$
                    | _ -> failwith "varhist"]
                with [Failure "nth" -> 1 ] >>
                )
            end
    |Ast.ExVari(id,Ast.Last) ->
            let (var,ctyp,def) =
                try Hashtbl.find hist_table id
                with Not_found -> failwith ("History "^id^ "not declared")
            in begin match use with
            |`List ->
                (new_id "ex_term",
                <:expr<
                try
                    let varhist = List.nth varl (List.length varl) in
                    match varhist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ ->
                        $ctyp_to_method_expr "elements" ctyp$
                    | _ -> failwith "varhist"]
                with [Failure "nth" -> 1 ] >>
                )
            |`Obj |`Var ->
                (new_id "ex_term",
                <:expr<
                try
                    let varhist = List.nth varl (List.length varl) in
                    match varhist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ -> $ctyp_to_method_expr "" ctyp$
                    | _ -> failwith "varhist"]
                with [Failure "nth" -> 1 ] >>
                )
            end
    |Ast.ExVari(id,Ast.All) ->
            begin match use with
            |`List -> failwith "expand_ex_term var all"
            |`Obj |`Var ->
                (new_id "ex_term",
                <:expr<
                try List.map (fun v -> v#find $str:id$) varl
                with [Failure "nth" -> 1 ] >>
                )
            end
    |Ast.ExVari(id,Ast.Null) -> failwith "exvari null"
    |Ast.ExHist(id) ->
            let (var,ctyp,def) =
                try Hashtbl.find hist_table id
                with Not_found -> failwith ("History "^id^ "not declared")
            in begin match use with
            |`List ->
                (new_id "ex_term",
                <:expr< 
                try match hist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ ->
                        $ctyp_to_method_expr "elements" ctyp$
                    | _ -> failwith "varhist"]
                with [Not_found -> failwith ("__find: " ^ $str:id$)] >>
                )
            |`Obj |`Var -> 
                (new_id "ex_term",
                <:expr< 
                try match hist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ -> $ctyp_to_method_expr "" ctyp$
                    | _ -> failwith "varhist"]
                with [Not_found -> failwith ("__find: " ^ $str:id$)] >>
                )
            end

let expand_ex_patt ex =
    let vars = extract_expr_vars [] ex in
    let idlist = List.map (fun s -> <:patt< `Label $lid:s$ >>) vars in
    let exl = List.map (fun s -> <:expr< sbl#find $str:s$ >>) vars in
    (new_id "ex_label",
    <:expr<
    try
       ExtList.$lid:"map"^string_of_int(List.length idlist)$ (fun
           [( $list:idlist$ ) -> $ex$
           |_ -> failwith ("__build")
           ]
       ) ( $list:exl$ ) 
    with [Not_found -> failwith ("__find: ")] >>
    )

let rec expand_ex_expr use = function
    |Ast.ExAppl(f,ex_expr) ->
            let (pa,ex) = expand_ex_expr use ex_expr in
            (new_id "ex_expr",
            <:expr< let $lid:pa$ = $ex$ in
            fun sbl hist varl -> $lid:f$ ( $lid:pa$ sbl hist varl ) >>)
    |Ast.ExLabt(label,ex_term) ->
            let (pa1,ex1) = expand_ex_term use ex_term in
            let (pa2,ex2) = expand_ex_patt label in
            (new_id "ex_expr",
            <:expr<
            let $lid:pa1$ = fun sbl hist varl -> $ex1$ in
            let $lid:pa2$ = fun sbl hist varl -> $ex2$ in
            fun sbl hist varl ->
                ExtList.map2 (fun l e -> (l,e))
                ($lid:pa2$ sbl hist varl, $lid:pa1$ sbl hist varl) >>)
    |Ast.ExTerm(ex_term) -> 
            let (pa,ex) = expand_ex_term use ex_term in
                (new_id "ex_expr",
                <:expr< let $lid:pa$ = fun sbl hist varl -> $ex$ in $lid:pa$ >>)
    |Ast.ExTupl(l) ->
            let (exl,pel) =
                List.split (
                    List.map (fun (pa,ex) ->
                        (<:expr< $lid:pa$ sbl hist varl >>,
                        (<:patt< $lid:pa$ >>,ex))
                    ) (List.map (expand_ex_expr use) l)
                )
            in 
            (new_id "ex_expr",
            <:expr< let $list:pel$ in fun sbl hist varl -> ( $list:exl$ ) >>)

    |Ast.ExExpr(ex) -> (new_id "ex_expr",ex)

let expand_condition name condlist =
        List.map (fun Ast.Condition ex_expr ->
            expand_ex_expr `Obj ex_expr
        ) condlist

let expand_dencont index dencontlist =
        List.map (fun ex_expr ->
            let (pa,ex) = expand_ex_expr `List ex_expr in
            (new_id "action",
            <:expr<
                let $lid:pa$ = $ex$ in
                NodePattern.newact $int:string_of_int index$ "" $lid:pa$
                >>
            )
        ) dencontlist

let expand_status s =
    let ex =
        let (var,ctyp,def) =
            try Hashtbl.find hist_table "status"
            with Not_found -> failwith ("History status not declared")
        in
        <:expr<
        fun varhist ->
            match varhist#find "status" with
            [`$uid:var$ $ctyp_to_patt ctyp$ ->
                varhist#add "status" (`$uid:var$ $str:s$)
            | _ -> failwith "down_axiom"]
        >>
    in (new_id "status", ex)

let expand_denominator name = function
    |Ast.Denominator arr ->
            List.flatten (Array.to_list (Array.mapi expand_dencont arr))
    |Ast.Status s -> [expand_status s]

let expand_ruledown ruletype bcond den_args action_args =
    let rec aux acc = function
        |[], h::_ -> failwith "expand_ruledown"
        |[d],[] -> <:expr< ( n, $d$, [] ) >>::acc
        |[d],[a] -> <:expr< ( n, $d$, $a$ ) >>::acc
        |d::dl,a::al -> aux (<:expr< ( n#copy, $d$, $a$ ) >>::acc) (dl,al)
        |d::dl,[] -> aux (<:expr< ( n#copy, $d$, [] ) >>::acc) (dl,[])
        |_ -> failwith "expand_ruledown"
    in
    function
        |[] -> failwith "expand_ruledown"
        |[Ast.Status(s)] -> 
                 <:expr< UserRule.down_axiom name context $List.hd den_args$ >>
        |_ ->
            begin match ruletype,bcond with
            |Ast.Explicit, _ ->
                <:expr< UserRule.down_explicit 
                name context (fun n ->
                    $list_to_exprlist ((aux [] (List.rev den_args,List.rev action_args)))$ ) >>
            |Ast.Implicit, Ast.Linear ->
                    <:expr< UserRule.down_implicit
                    name context $List.hd den_args$ $List.hd action_args$ >>
            |Ast.Implicit,_ -> failwith "Rule type not allowed"
            end

let expand_action name actionlist =
    List.map (function
        |Ast.Assign(Ast.ExHist(id),ex_expr)
        |Ast.Assign(Ast.ExVari(id,Ast.Null),ex_expr) ->
                let (pa,ex) = expand_ex_expr `Obj ex_expr in
                let (var,ctyp,def) =
                    try Hashtbl.find hist_table id
                    with Not_found -> failwith ("History "^id^ "not declared")
                in
                (new_id "action",
                <:expr< let $lid:pa$ = $ex$ in
                fun sbl hist varl ->
                    ( $str:id$, `$uid:var$ ( $lid:pa$ sbl hist varl ) ) >>
                )
        |Ast.Function(ex_expr) -> 
                let (pa,ex) = expand_ex_expr `Obj ex_expr in
                (new_id "action",
                <:expr< let $lid:pa$ = $ex$ in fun sbl hist varl -> $lid:pa$>>
                )
        |_ -> failwith "expand_action"
    ) actionlist

let expand_status_defaults () =
    let (var,_,_) =
        try Hashtbl.find hist_table "status"
        with Not_found ->
            let v = new_co "Hist" in
            let t = <:ctyp< $lid:"string"$ >> in
            let d = <:expr< $str:"Open"$ >> in
            Hashtbl.add hist_table "status" (v,t,d) ; 
            (v,t,d)
    in
    <:str_item<
    value status s sbl hist varlist =
        let varhist = 
            try List.nth varlist ((List.length varlist) - 1)
            with [ Failure "nth" -> failwith "status: nth" ]
        in
        try match varhist#find "status" with
            [`$uid:var$ t when s = t -> True
            |`$uid:var$ _ -> False
            |_ -> failwith "status"]
        with [ Not_found -> failwith "custom status: not found" ]
    >>

let expand_ruleup ruletype bcond denlist branchcond_args backtrack_args =
    let bt_arg = list_to_exprlist backtrack_args in
    let opencond = <:expr< status "Open" >> in
    let closedcond = <:expr< status "Close" >> in
    let add_rule rule ll =
        let n = List.length ll in
        let rec def acc = function
            |0 -> acc
            |i -> def ([]::acc) (i-1)
        in
        let defll = ll@(def [] ((List.length denlist)-n)) in
        match defll with
        |[] -> <:expr< [ [ $rule$ ] ] >>
        |ll -> list_to_exprlist (
                List.map (fun l ->
                    list_to_exprlist (rule::l)
                ) ll
            )
    in
    let ll_to_exprll ll =
        list_to_exprlist (
            List.map (fun l -> list_to_exprlist l) ll
        )
    in
    match ruletype,bcond with
    |Ast.Explicit,Ast.Linear ->
            <:expr< UserRule.up_explore_linear name context treelist $bt_arg$ >>
    |Ast.Implicit,Ast.Linear ->
            let br_arg = add_rule opencond branchcond_args in
            <:expr< UserRule.up_explore_implicit name context treelist $bt_arg$ $br_arg$ >>

    |Ast.Explicit,Ast.ForAll ->
            let br_arg = add_rule closedcond branchcond_args in
            <:expr< UserRule.up_explore_simple name context treelist $bt_arg$ $br_arg$ >>
    |Ast.Implicit,Ast.ForAll ->
            let br_arg = add_rule opencond branchcond_args in
            <:expr< UserRule.up_explore_simple name context treelist $bt_arg$ $br_arg$ >>

    |Ast.Explicit,Ast.Exists ->
            let br_arg = add_rule opencond branchcond_args in
            <:expr< UserRule.up_explore_simple name context treelist $bt_arg$ $br_arg$ >>
    |Ast.Implicit,Ast.Exists ->
            let br_arg = add_rule closedcond branchcond_args in
            <:expr< UserRule.up_explore_simple name context treelist $bt_arg$ $br_arg$ >>

    |Ast.Explicit,Ast.User |Ast.Implicit,Ast.User ->
            let br_arg = ll_to_exprll branchcond_args in
            <:expr< UserRule.up_explore_simple name context treelist $bt_arg$ $br_arg$ >>

let expand_rule (Ast.Rule rule) =
    let ( name,
        ruletype,
        num,
        (denlist,bcond),
        condlist,
        actionlist,
        branchcondlist,
        backtracklist,
        cache,
        heurisitic
    ) = rule
    in

    (* numerator *)
    let numl = expand_rule_num name num in
    let num_args =
        let (empty,single,set) = expand_num_triple numl num in
        let exemptyl = list_to_exprlist (List.rev empty) in
        let exsinglel = list_to_exprlist (List.rev single) in
        let exsetl = list_to_exprlist (List.rev set) in
        <:expr< ( $exemptyl$, $exsinglel$, $exsetl$ ) >>
    in
    let num_aux_fun =
        let sil = List.map (fun (pa,ex) -> 
            <:str_item< value $lid:pa$ = $ex$ >>
        ) numl 
        in <:str_item< declare $list:sil$ end >>
    in

    (* side condition on the numerator *)
    let condl = expand_condition name condlist in
    let (pl,exl) = List.split condl in
    let cond_args = list_to_exprlist ( List.map (fun p -> <:expr< $lid:p$ >>) pl) in

    let cond_aux_fun =
        let sil = List.map (fun (pa,ex) -> 
            <:str_item< value $lid:pa$ = $ex$ >>
        ) condl
        in <:str_item< declare $list:sil$ end >>
    in

    (* denominators *)
    let denll = List.map (expand_denominator name) denlist in
    let den_args =
            List.map (fun denl ->
                list_to_exprlist (
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
    let actionll = List.map (expand_action name) actionlist in
    let action_args =
            List.map (fun actionl ->
                list_to_exprlist (
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
    let branchcondll = List.map (expand_condition name) branchcondlist in
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

    (* backtrack *)
    let backtrackl = expand_action name backtracklist in
    let backtrackp =
        List.map (fun (s,e) ->
            <:str_item< value $lid:s$ = $e$ >>
        ) backtrackl
    in
    let backtrack_args =
        List.map (fun (s,_) ->
            <:expr< $lid:s$ >> 
        ) backtrackl
    in
    let backtrack_aux_fun = <:str_item< declare $list:backtrackp$ end >> in

    let num_fun = <:expr< UserRule.check name node $num_args$ $cond_args$ >> in
    let den_fun = expand_ruledown ruletype bcond den_args action_args denlist in 
    let up_fun  = expand_ruleup ruletype bcond denlist branchcond_args backtrack_args in

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

let expand_preamble =
    <:str_item<
    declare
    module BaseType =
        struct
            type t = expr ;
            value copy s = s ;
            value to_string = expr_printer ;
        end
    ;
    module SblType =
        struct
            type t = [= `Label of int |`Term of formula ];
            value copy s = s ;
            value to_string = fun
                [`Label i -> string_of_int i
                |`Term f -> formula_printer f];
        end
    ;
    module MapSet   = TwbSet.Make(BaseType);
    module SblSet   = TwbSet.Make(SblType);

    module MapCont  = struct type t = BaseType.t; class set = MapSet.set; end;
    module SblCont  = struct type t = SblType.t ; class set = SblSet.set; end;

    module TwbMain  = TwbMain.Make(MapCont)(SblCont)(HistType)(VarType);
    open TwbMain;
    open TwbMain.UserRule;
    open TwbMain.UserRule.DataType;
    open TwbMain.UserRule.DataType.Strategy;
    open TwbMain.UserRule.DataType.Partition;

    module TwbCont = TwbMap.Make(MapCont);
    end >>

let expand_init =
    <:str_item< 
    declare
        module AstTrans = struct 
            type t = formula;
            value ast2input = formula_ast2input;
        end;
        module TwbParser   = InputParser.Make(AstTrans);
        TwbParser.initParser ();
        TwbMain.init ();
    end >>

let expand_matchpatt rulelist =
    let get_schema (Ast.Rule rule) =
        let aux = List.map (fun (_,pa_expr) -> pa_expr ) in
        let (_, _, Ast.Numerator arr, _, _, _, _, _, _, _ ) = rule in
        List.flatten (Array.to_list (Array.map aux arr))
    in
    let pa_expr_to_patt =
        let rec pa_term_to_patt = function
            |Ast.PaAtom(s) -> <:patt< `Atom _ >>
            |Ast.PaCons(s) -> <:patt< `$uid:s$ >>
            |Ast.PaConn(id,l) -> <:patt< `$uid:id$($list:List.map pa_term_to_patt l$) >>
            |Ast.PaVar(_) -> <:patt< _ >>
            |_ -> failwith "matchpatt"
        in function
            |Ast.PaTerm(Ast.PaVar(_)) -> None
            |Ast.PaLabt(_,Ast.PaVar(_)) -> None
            |Ast.PaTerm(t) -> Some(<:patt< $pa_term_to_patt t$ >>)
            |Ast.PaLabt(_,t) -> Some(<:patt< (_,$pa_term_to_patt t$) >>)
            |_ -> None
    in
    let pel = 
        List.rev (List.sort compare (unique (
            List.flatten (
                List.map (fun rule ->
                    filter_map (fun pa_expr ->
                        match pa_expr_to_patt pa_expr with
                        |None -> None
                        |Some(pa) -> Some(pa,None,<:expr< $str:pa_expr_to_string pa_expr$ >>)
                    ) (get_schema rule)
                ) rulelist 
            )
        )))
    in
    let def = <:patt< _ >>, None, <:expr< failwith "match_schema" >> in
    <:str_item< value match_schema = fun [ $list:pel@[def]$ ] >>

let expand_tableau (Ast.Tableau rulelist) =
    let sd = expand_status_defaults () in
    let l = List.map expand_rule rulelist in
    <:str_item< declare 
    $list:
        expand_matchpatt rulelist::
        expand_preamble::sd::
        l@[expand_init]$ end
    >>

let rec expand_tactic = function
    |Ast.TaVar(id) -> <:expr< $lid:id$ >>
    |Ast.TaSkip -> <:expr< Skip >>
    |Ast.TaFail -> <:expr< Fail >>
    |Ast.TaBasic(uid) ->
            let id = String.lowercase uid in
            <:expr< Rule( new $lid:id^"_rule"$ ) >>
    |Ast.TaSeq(t1,t2) ->
            let ext1 = expand_tactic t1 in
            let ext2 = expand_tactic t2 in
            <:expr< Seq( $list:[ext1;ext2]$ ) >>
    |Ast.TaAlt(t1,t2) ->
            let ext1 = expand_tactic t1 in
            let ext2 = expand_tactic t2 in
            <:expr< Alt( $list:[ext1;ext2]$ ) >>
    |Ast.TaCut(t) ->
            let ext = expand_tactic t in
            <:expr< Cut( $ext$ ) >>
    |Ast.TaMu(x,t) ->
            let ext = expand_tactic t in
            <:expr< Mu( $str:x$ , $ext$ ) >>
    |Ast.TaMVar(x) -> <:expr< Var( $str:x$ ) >>

let expand_main () =
    let pp =
        try Some(<:expr< ~pp:$Hashtbl.find expr_table "pp"$ >> )
        with Not_found -> None
    in
    let neg =
        try Some(<:expr< ~neg:$Hashtbl.find expr_table "neg"$>> )
        with Not_found -> None
    in
    let histlist = 
        try Some(<:expr< ~histlist:$Hashtbl.find expr_table "histlist"$ >>)
        with Not_found -> None
    in
    let varlist = 
        try Some(<:expr< ~varlist:$Hashtbl.find expr_table "varlist"$ >>)
        with Not_found -> None
    in
    let mapcont =
        Some(<:expr< ~mapcont:[| new TwbCont.map match_schema |] >>)
    in
    let strategy =
        try Some(<:expr< ~strategy:$Hashtbl.find expr_table "strategy"$ >>)
        with Not_found -> failwith "Strategy not specified"
    in
    let inputparser = Some(<:expr< ~inputparser:TwbParser.buildParser >>) in
    let exitfun =
        try Some(<:expr< ~exitfun$Hashtbl.find expr_table "exitfun"$ >>)
        with Not_found ->
            let (var,_,_) =
                try Hashtbl.find hist_table "status"
                with Not_found -> failwith ("status not declared")
            in
            let ex = <:expr< fun [node -> 
                match UserRule.status node with [ `$uid:var$ s -> s ]
                ] >>
            in Some(<:expr< ~exitfun:$ex$ >>)
    in
    let ex =
        List.fold_left (fun acc label ->
            match label with
            |None -> acc
            |Some(e) -> <:expr< $acc$ $e$>>
        ) <:expr< TwbMain.main >>
        [histlist;varlist;neg;pp;mapcont;inputparser;strategy;exitfun]
    in <:str_item< $exp:ex$ >>

let expand_strategy e = Hashtbl.add expr_table "strategy" e ; <:str_item< "" >>
let expand_preproc e  = Hashtbl.add expr_table "pp" e ; <:str_item< "" >>
let expand_negation e = Hashtbl.add expr_table "neg" e ; <:str_item< "" >>
let expand_exit e     = Hashtbl.add expr_table "exitfun" e ; <:str_item< "" >>
let expand_simplification s = failwith "expand_simplification"
let expand_options s = failwith "expand_options"

let expand_source m =
    let tmp_dir =
        let str = "/tmp/twb" ^ Unix.getlogin () in
        let _ =
            try ignore(Unix.stat str) with
            |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
        in str ^ "/"
    in
    let ch = open_in (tmp_dir^String.lowercase m^".gramm") in
    let gramms = Marshal.from_channel ch in
    let _ = close_in ch in
    ExtGramm.extgramm gramms;
    let ty = ExtGramm.expand_grammar_type_list gramms in
    let pr = ExtGramm.expand_printer gramms in
    let sty = <:str_item< type $list:ty$ >> in
    <:str_item< declare $list:[sty;pr]$ end >>
