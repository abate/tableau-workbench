(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Parselib

let rec expand_pa_term = function
    |Ast.PaConn(_,id,l) -> <:patt< `$uid:id$($list:List.map expand_pa_term l$) >>
    |Ast.PaCons(_,id)   -> <:patt< ( `$uid:id$ as $lid:String.lowercase id$ ) >>
    |Ast.PaAtom(_,s)    -> <:patt< ( `Atom _ as $lid:String.lowercase s$ ) >>
    |Ast.PaVar(_,s)     -> <:patt< $lid:String.lowercase s$ >>
    |Ast.PaVari(s,i)  -> assert(false)
    |Ast.PaHist(s)    -> assert(false)

let rec expand_pa_expr = function
    |Ast.PaTerm(t)       -> <:patt< $expand_pa_term t$ >>
    |Ast.PaLabt((_,deco),t) -> <:patt< ($deco$, $expand_pa_term t$) >>
    |Ast.PaTupl(l)       -> <:patt< ($list:List.map expand_pa_expr l$) >>
    |Ast.PaPatt(pa)      -> pa

let rec extract_pa_term_vars acc = function
    |Ast.PaConn(_,id,l) -> (List.flatten (List.map (extract_pa_term_vars []) l)) 
    |Ast.PaCons(label,s) |Ast.PaAtom(label,s) |Ast.PaVar(label,s) -> 
            (String.capitalize label,s)::acc
    |Ast.PaHist(s) |Ast.PaVari(s,_) -> ("AAA",s)::acc

let rec extract_ex_term_vars acc = function
    |Ast.ExConn(_,id,l) -> (List.flatten (List.map (extract_ex_term_vars []) l)) 
    |Ast.ExCons(label,s) |Ast.ExAtom(label,s) |Ast.ExVar(label,s) ->
            (String.capitalize label,String.lowercase s)::acc
    |Ast.ExHist(s) |Ast.ExVari(s,_) -> ("AAA",String.lowercase s)::acc

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
            List.map (fun (label,id) -> 
                (<:expr< $str:id$ >>,<:expr< `$uid:label$ $lid:String.lowercase id$ >>) )
            (extract_pa_term_vars [] t)
    |Ast.PaLabt((decolabel,deco),t) ->
            List.append
                (List.map (fun id -> 
                    (<:expr< $str:id$ >>,
                    <:expr< `$uid:String.capitalize decolabel$ $lid:String.lowercase id$ >>) )
                (extract_patt_vars [] deco))
                (List.map (fun (label,id) ->
                    (<:expr< $str:id$ >>,<:expr< `$uid:label$ $lid:String.lowercase id$ >>) )
                (extract_pa_term_vars [] t))
    |Ast.PaTupl(l) -> List.flatten (List.map extract_pa_expr_vars l)
    |Ast.PaPatt(pa) -> 
                (List.map (fun id -> 
                    (<:expr< $str:id$ >>,<:expr< `Label $lid:String.lowercase id$ >>) )
                (extract_patt_vars [] pa))

let pa_expr_to_string =
    let rec pa_term_to_string = function
        |Ast.PaAtom(_,s) -> "__atom"
        |Ast.PaCons(_,s) -> "__const"
        |Ast.PaConn(_,id,l) -> List.fold_left (fun s e -> s^(pa_term_to_string e)) id l
        |_ -> ""
    in function
        |Ast.PaTerm(t) -> pa_term_to_string t
        |Ast.PaLabt(_,t) -> pa_term_to_string t
        |_ -> assert(false)

let ctyp_to_patt ctyp =
    let counter = ref 0 in
    let rec aux = function
        |MLast.TyTup(_,l)  -> <:patt< ($list:List.map aux l$) >>
        |MLast.TyLid(_,id) ->
                incr counter; 
                <:patt< $lid:"__t"^string_of_int !counter$ >>
        |MLast.TyAcc(_,_,ctyp) -> aux ctyp
        |_ -> assert(false)
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
        |_ -> assert(false) 
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
            |_ -> assert(false)
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

let expand_histories_aux table =
    let aux2 vt vl tlist copylist to_stringlist =
        <:str_item<
        module $uid:vt$ =
          struct
              type t = $tlist$ ;
              value copy = fun [ $list:copylist$ ] ;
              value to_string = fun [ $list:to_stringlist$ ] ;
          end    
        >>
    in
    let aux1 vt vl table =
        let l = Hashtbl.fold (fun i (v,c,d) init -> 
            (i,v,c,d)::init) table []
        in
        let (tlist,copylist,to_stringlist) = expand_history_type l in
        let exl = List.map (fun (id,var,_,def) ->
                <:expr< ($str:id$ , `$uid:var$ $def$) >>
            ) l
        in
        Hashtbl.add expr_table vl (list_to_exprlist exl);
        aux2 vt vl tlist copylist to_stringlist
    in 
    function
    |Ast.Variable(_) ->
            if Hashtbl.length table > 0 && Hashtbl.mem table "status" then
                aux1 "VarType" "varlist" table
            else begin
                let var = new_co "Hist" in
                Hashtbl.add table "status" 
                (var,<:ctyp< $lid:"string"$ >>,<:expr< "Open" >>);
                aux1 "VarType" "varlist" table
                end
    |Ast.History(_)  ->
            if Hashtbl.length table > 0 then aux1 "HistType" "histlist" table
            else aux2 "HistType" "histlist" <:ctyp< [= `Null ] >> [] []

let expand_histories =
    let aux table (id,ctyp,def) =
        let var = new_co "Hist" in
        Hashtbl.replace table id (var,ctyp,def)
    in 
    function
        |Ast.Variable(l) -> List.iter (aux vars_table) l ; <:str_item< "" >>
        |Ast.History(l)  -> List.iter (aux hist_table) l ; <:str_item< "" >>

let expand_principal pa_expr =
    let (idlist,termlist) = List.split (extract_pa_expr_vars pa_expr) in
    let act =
        ((expand_pa_expr pa_expr), None,
        <:expr<
            List.map2
            (fun f s ->
                try if sbl#mem s f then [] else raise FailedMatch
                with [Not_found -> [f]]
            ) $list_to_exprlist termlist$ $list_to_exprlist idlist$
        >>)
    in
    let def = (<:patt< _ >>, None, <:expr< raise FailedMatch >>) in
    let l = if pa_expr_is_var pa_expr then [act] else [act;def] in
    <:expr<
    fun sbl -> fun fl ->
        let __rec = fun [ $list:l$ ] in
        match (* $heuristic$ *) fl with
        [[] -> sbl#add (List.combine $list_to_exprlist idlist$ [[]])
        |[ h::_ ] -> sbl#add (List.combine $list_to_exprlist idlist$ (__rec h))
        ]
    >>

let expand_set pa_expr = 
    let (idlist,termlist) = List.split (extract_pa_expr_vars pa_expr) in
    let rec aux = function
        |[id],[ex] -> 
            <:expr<
            try
                if (sbl#find $id$)#elements = [$ex$]
                then $list_to_exprlist termlist$
                else [] 
            with [ Not_found -> $list_to_exprlist termlist$ ]
            >>
        |id::tl1,ex::tl2 ->
            <:expr<
            try
                if (sbl#find $id$)#elements = [$ex$]
                then $aux (tl1,tl2)$ 
                else [] 
            with [ Not_found -> $aux (tl1,tl2)$ ]
            >>
        |_ -> assert(false) 
    in
    let exl =
         let ex = (expand_pa_expr pa_expr,None,aux (idlist,termlist)) in
         let def = (<:patt< _ >>, None, <:expr< raise FailedMatch >>) in
         if pa_expr_is_var pa_expr then [ex] else [ex;def]
    in
    <:expr<
    fun sbl fl ->
        let __rec = fun [ $list:exl$ ]
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
    |Ast.ExConn(_,id,l) as ex_term ->
            let argall = 
                let rec aux = function
                    |Ast.ExConn(_,id,l) ->
                           List.flatten (List.map (fun e -> aux e) l ) 
                    |e -> [expand_ex_term `Term e]
                in List.flatten (List.map (fun e -> aux e) l )
            in
            let rec filter (acc,exacc) = function
                |(pa,ex)::tl when (List.mem ex exacc) -> filter (acc,exacc) tl
                |(pa,ex)::tl -> filter (((pa,ex)::acc),(ex::exacc)) tl
                |[] -> acc
            in
            let (exl,pel) =
                List.split (
                    List.map (function (pa,ex) ->
                        (<:expr< $lid:pa$ sbl hist varl >>,
                        (<:patt< $lid:pa$ >>,
                        <:expr< fun sbl hist varl -> $ex$ >>))
                    ) (filter ([],[]) argall)
                )
            in
            let rec aux = function
                |Ast.ExConn(_,id,l) -> <:expr< `$uid:id$($list:List.map aux l$) >>
                |Ast.ExCons(_,id)   -> <:expr< `$uid:id$ >>
                |Ast.ExAtom(_,s)    -> <:expr< `Atom $str:s$ >>
                |Ast.ExVar(_,s)     -> <:expr< $lid:String.lowercase s$ >>
                |Ast.ExVari(s,i)  -> assert(false) 
                |Ast.ExHist(s)    -> assert(false)
            in
            let idlist =
                List.rev (
                    List.map (fun (label,s) -> <:patt< `$uid:label$ $lid:s$ >>) 
                    ( unique(extract_ex_term_vars [] ex_term) )
                )
            in
            (new_id "ex_expr",
            <:expr< let $list:pel$ in
            ExtList.$lid:"map"^string_of_int(List.length pel)$ (fun
                [( $list:idlist$ ) -> $aux ex_term$
                |_ -> failwith ("__build")
                ]
            ) ( $list:exl$ ) >>
            )
    |Ast.ExAtom(label,id) ->
            begin match use with
            |`List | `Obj -> assert(false)
            |`Term -> (new_id "ex_term",
            <:expr< [`$uid:String.capitalize label$ ( `Atom $str:id$ ) ] >>)
            end
    |Ast.ExCons(label,id) ->
            begin match use with
            |`List | `Obj -> assert(false)
            |`Term -> (new_id "ex_term",
            <:expr< [`$uid:String.capitalize label$ `$uid:id$] >>)
            end
    |Ast.ExVar(label,id) ->
            begin match use with
            |`List | `Obj ->
                (new_id "ex_term",
                <:expr<
                ExtList.map1 (fun
                    [`$uid:String.capitalize label$ e -> e
                    |_ -> failwith ("__build")
                    ]
                ) ( try (sbl#find $str:id$)#elements
                    with [Not_found -> failwith ("__find: " ^ $str:id$)]) >>
                )
             |`Term ->
                (new_id "ex_term",
                <:expr<
                try (sbl#find $str:id$)#elements
                with [Not_found -> failwith ("__find: " ^ $str:id$)] >>
                )
            end
    |Ast.ExVari(id,Ast.Int i) ->
            let (var,ctyp,def) =
                try Hashtbl.find vars_table id
                with Not_found -> failwith ("Variable "^id^ " not declared")
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
                with [Failure "nth" -> [] ] >>
                )
            |`Obj | `Term ->
                (new_id "ex_term",
                <:expr<
                try
                    let varhist = List.nth varl ($int:string_of_int i$ - 1) in
                    match varhist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ -> $ctyp_to_method_expr "" ctyp$
                    | _ -> failwith "varhist"]
                with [Failure "nth" -> $def$ ] >>
                )
            end
    |Ast.ExVari(id,Ast.Last) ->
            let (var,ctyp,def) =
                try Hashtbl.find vars_table id
                with Not_found -> failwith ("Variable "^id^ " not declared")
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
                with [Failure "nth" -> [] ] >>
                )
            |`Obj |`Term ->
                (new_id "ex_term",
                <:expr<
                try
                    let varhist = List.nth varl (List.length varl) in
                    match varhist#find $str:id$ with
                    [`$uid:var$ $ctyp_to_patt ctyp$ -> $ctyp_to_method_expr "" ctyp$
                    | _ -> failwith "varhist"]
                with [Failure "nth" -> $def$ ] >>
                )
            end
    |Ast.ExVari(id,Ast.All) ->
            begin match use with
            |`List -> assert(false)
            |`Obj |`Term ->
                (new_id "ex_term",
                <:expr<
                try List.map (fun v -> v#find $str:id$) varl
                with [Failure "nth" -> failwith $str:id^ " index out of bound"$ ] >>
                )
            end
    |Ast.ExVari(id,Ast.Null) -> assert(false)
    |Ast.ExHist(id) ->
            let (var,ctyp,def) =
                try Hashtbl.find hist_table id
                with Not_found -> failwith ("History "^id^ " not declared")
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
            |`Obj |`Term -> 
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
    |Ast.ExLabt((_,deco),ex_term) ->
            let (pa1,ex1) = expand_ex_term use ex_term in
            let (pa2,ex2) = expand_ex_patt deco in
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
    |Ast.ExTupl([]) -> (new_id "ex_expr", <:expr< fun sbl hist varl -> () >>)
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
            try Hashtbl.find vars_table "status"
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
    let aux l1 l2 =
        let rec fill_list acc l1 l2 =
            match l1,l2 with
            |[],_ -> acc
            |a::la,[] -> fill_list (([a],[])::acc) la []
            |a::la,b::lb -> fill_list (([a],[b])::acc) la lb
        in
        match List.rev (fill_list [] l1 l2) with
        |([a],b) :: tl ->
                let acc =
                    match b with
                    |[]  -> <:expr< ( n , $a$, [] ) >>
                    |[b] -> <:expr< ( n , $a$, $b$ ) >>
                    |_ -> assert(false)
                in
                List.rev (
                    List.fold_left (fun acc -> function
                        |([a],[b]) -> <:expr< ( n#copy, $a$, $b$ ) >>::acc
                        |([a],[])  -> <:expr< ( n#copy, $a$, [] ) >>::acc
                        |_ -> assert(false)
                    ) [acc] tl
                )
        |_ -> assert(false)
    in
    function
        |[] -> assert(false)
        |[Ast.Status(s)] -> 
                 <:expr< UserRule.down_axiom name context $List.hd den_args$ >>
        |_ ->
            begin match ruletype,bcond with
            |Ast.Explicit, _ ->
                <:expr< UserRule.down_explicit 
                name context (fun n ->
                    $list_to_exprlist (aux den_args action_args)$ ) >>
            |Ast.Implicit, Ast.Linear ->
                    let aa =
                        if action_args = [] then <:expr< [] >>
                        else List.hd action_args
                    in
                    <:expr< UserRule.down_implicit
                    name context $List.hd den_args$ $aa$ >>
            |Ast.Implicit,_ -> failwith "Rule type not allowed"
            end

let expand_action name actionlist =
    List.map (function
        |Ast.Assign(arg,ex_expr) ->
                let (pa,ex) = expand_ex_expr `Obj ex_expr in
                let ((var,ctyp,def),id) =
                    try match arg with
                    |Ast.ExVari(id,Ast.Null) -> (Hashtbl.find vars_table id,id)
                    |Ast.ExHist(id) -> (Hashtbl.find hist_table id,id)
                    |_ -> assert(false)
                    with Not_found -> failwith ("History or Variable not declared")
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
    ) actionlist

let expand_status_defaults () =
    let (var,_,_) =
        try Hashtbl.find vars_table "status"
        with Not_found -> assert(false)
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

let expand_preamble () =
    let hist = expand_histories_aux hist_table (Ast.History([])) in
    let vars = expand_histories_aux vars_table (Ast.Variable([])) in
    let l = Hashtbl.fold (fun k _ acc -> k::acc) gramm_table [] in
    let sbltype =
        let aux s = <:ctyp< [= `$uid:String.capitalize s$ of $lid:s$ ] >> in
        match l with
        |[] -> assert(false)
        |[h] -> aux h
        |h::tl -> List.fold_left (fun acc s -> 
                    <:ctyp< [= $acc$ | $aux s$ ] >>) (aux h) tl
    in
    let sblprint = 
        List.fold_left (fun acc c ->
            (<:patt< `$uid:String.capitalize c$ f >>, None, 
            <:expr< $lid:c^"_printer"$ f >>)::acc
        ) [] l
    in
    <:str_item< declare
    $hist$;
    $vars$;
    module BaseType =
        struct
            type t = expr ;
            value copy s = s ;
            value to_string = expr_printer ;
        end
    ;
    module SblType =
        struct
            type t = $sbltype$;
            value copy s = s ;
            value to_string = fun [ $list:sblprint$ ];
        end
    ;
    (* XXX it's not necessary to build all these modules all the time,
     * but it shouldn't hurt run time performances *)
    module MapSet         = TwbSet.Make(BaseType);
    module MapMSet        = TwbMSet.Make(BaseType);
    module SblSet         = TwbSet.Make(SblType);

    module MapContSet  = struct type t = BaseType.t; class set = MapSet.set; end;
    module MapContMSet  = struct type t = BaseType.t; class set = MapMSet.set; end;
    module SblCont  = struct type t = SblType.t ; class set = SblSet.set; end;

    (* MapContMSet in TwbMain is used only to provide the base type, but it is
     * not instantiated anywhere... XXX *)
    module TwbMain  = TwbMain.Make(MapContSet)(SblCont)(HistType)(VarType);
    open TwbMain;
    open TwbMain.UserRule;
    open TwbMain.UserRule.DataType;
    open TwbMain.UserRule.DataType.Strategy;
    open TwbMain.UserRule.DataType.Partition;

    module TwbContSet = TwbMap.Make(MapContSet);
    module TwbContMSet = TwbMap.Make(MapContMSet);
    module TwbContSingleton = TwbSingleton.Make(BaseType);
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
        (* we inject all constants and atom *)
        let constlist = Hashtbl.fold (fun k v acc -> 
            Ast.PaTerm(Ast.PaCons("AAA",k))::acc) const_table []
        in Ast.PaTerm(Ast.PaAtom("AAA","")):: (* XXX *)
            (List.flatten (Array.to_list (Array.map aux arr)))@constlist
    in
    let pa_expr_to_patt =
        let rec pa_term_to_patt = function
            |Ast.PaAtom(_,s) -> <:patt< `Atom _ >>
            |Ast.PaCons(_,s) -> <:patt< `$uid:s$ >>
            |Ast.PaConn(_,id,l) -> <:patt< `$uid:id$($list:List.map pa_term_to_patt l$) >>
            |Ast.PaVar(_,_) -> <:patt< _ >>
            |_ -> assert(false)
        in function
            |Ast.PaTerm(Ast.PaVar(_,_)) -> None
            |Ast.PaLabt(_,Ast.PaVar(_,_)) -> None
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
                        |Some(pa) ->
                                Some(pa,None,<:expr< $str:pa_expr_to_string pa_expr$ >>)
                    ) (get_schema rule)
                ) rulelist
            )
        )))
    in
    let def = <:patt< f >>, None,
    <:expr< failwith ("no rule match this formula"^(formula_printer f)) >> in
    <:str_item< value match_schema = fun [ $list:pel@[def]$ ] >>

let expand_tableau (Ast.Tableau rulelist) =
    let pa = expand_preamble () in
    let sd = expand_status_defaults () in
    let l = List.map expand_rule rulelist in
    <:str_item< declare 
    $list: expand_matchpatt rulelist:: pa::sd:: l@[expand_init]$
    end >>

let rec expand_tactic = function
    |Ast.TaVar(id) -> <:expr< $lid:id$ >>
    |Ast.TaSkip -> <:expr< Skip >>
    |Ast.TaFail -> <:expr< Fail >>
    |Ast.TaBasic(uid) ->
            let id = String.lowercase uid in
            <:expr< Rule( new $lid:id^"_rule"$ ) >>
    |Ast.TaModule(m,uid) ->
            let id = String.lowercase uid in
            <:expr< Rule( new $uid:m$.$lid:id^"_rule"$ ) >>
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
        try <:expr< ~pp:$Hashtbl.find expr_table "pp"$ >>
        with Not_found -> <:expr< ~pp:(fun x -> x) >>
    in
    let neg =
        try <:expr< ~neg:$Hashtbl.find expr_table "neg"$>>
        with Not_found -> <:expr< ~neg:(fun x -> x) >>
    in
    let histlist = 
        try <:expr< ~histlist:$Hashtbl.find expr_table "histlist"$ >>
        with Not_found -> <:expr< ~histlist:[] >>
    in
    let varlist = 
        try <:expr< ~varlist:$Hashtbl.find expr_table "varlist"$ >>
        with Not_found -> <:expr< ~varlist:[] >>
    in
    let mapcont = 
        try <:expr< ~mapcont:$Hashtbl.find expr_table "mapcont"$ >>
        with Not_found ->
            <:expr< ~mapcont:[| new TwbCont.map match_schema |] >>
    in
    let strategy =
        try <:expr< ~strategy:$Hashtbl.find expr_table "strategy"$ >>
        with Not_found -> failwith "Strategy not specified"
    in
    let inputparser = <:expr< ~inputparser:TwbParser.buildParser >> in
    let exitfun =
        try <:expr< ~exitfun:$Hashtbl.find expr_table "exitfun"$ >>
        with Not_found ->
            let (var,_,_) =
                try Hashtbl.find vars_table "status"
                with Not_found -> failwith ("status not declared")
            in
            let pel = 
                let e = <:patt< `$uid:var$ s >>,None,<:expr< s >> in
                if Hashtbl.length vars_table > 1 then
                    [e;(<:patt< _ >>, None, <:expr< failwith "exitfun" >>)]
                else [e]
            in
            let ex = <:expr< fun [node -> 
                match UserRule.status node with [ $list:pel$ ] ] >>
            in <:expr< ~exitfun:$ex$ >>
    in
    let ex =
        List.fold_left (fun acc e -> <:expr< $acc$ $e$>>)
        <:expr< TwbMain.main >>
        [histlist;varlist;neg;pp;mapcont;inputparser;strategy;exitfun]
    in <:str_item< $exp:ex$ >>


let expand_exit ex_expr =
    let (id,ex) = expand_ex_expr `Obj ex_expr in
    let e = <:expr< fun node ->
        let (_,_,varhist) =  (UserRule.unbox_tree node)#get in
        let s = new Substitution.sbl in
        let h = new Hmap.map in
        let $lid:id$ = $ex$ in $lid:id$ s h [varhist] >> in
    Hashtbl.add expr_table "exitfun" e ; 
    <:str_item< "" >>

let expand_strategy e = Hashtbl.add expr_table "strategy" e ; <:str_item< "" >>
let expand_preproc e  = Hashtbl.add expr_table "pp" e ; <:str_item< "" >>
let expand_negation e = Hashtbl.add expr_table "neg" e ; <:str_item< "" >>
let expand_simplification s = failwith "expand_simplification"
let expand_options s = failwith "expand_options"

let expand_source m =
    let (symbollist,gramms) = ExtGramm.readgramm m in
    ExtGramm.update_gramm_table gramms;
    List.iter (fun c -> Hashtbl.add symbol_table c ()) symbollist;
    ExtGramm.extgramm (ExtGramm.remove_node_entry gramms);
    ExtGramm.extend_node_type (ExtGramm.select_node_entry gramms);
    let ty = ExtGramm.expand_grammar_type_list gramms in
    let pr = ExtGramm.expand_printer gramms in
    let ast = ExtGramm.expand_ast2input gramms in
    let sty = List.map (fun t -> <:str_item< type $list:t$ >>) ty in
    <:str_item< declare $list:sty@[pr;ast]$ end >>

