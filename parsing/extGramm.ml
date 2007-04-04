(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

module PcamlGramm = Entrylib.Make(struct let gram = Pcaml.gram end)
open Parselib
open Genlex 
open PcamlGramm

let _loc = Token.dummy_loc
let create_gramm = PcamlGramm.create_gramm
let create_obj = PcamlGramm.create_obj

module ExprEntry = EntryMake(struct type t = MLast.expr let ttype = TExpr end) 
module PattEntry = EntryMake(struct type t = MLast.patt let ttype = TPatt end) 
module ExprSchemaEntry = EntryMake(struct type t = Ast.ex_term let ttype = TExprSchema end) 
module PattSchemaEntry = EntryMake(struct type t = Ast.pa_term let ttype = TPattSchema end) 

let formula_expr = ExprEntry.add_entry "formula" ; ExprEntry.get_entry "formula"
let formula_patt = PattEntry.add_entry "formula" ; PattEntry.get_entry "formula"
let formula_expr_schema =
    ExprSchemaEntry.add_entry "formula" ;
    ExprSchemaEntry.get_entry "formula"
let formula_patt_schema =
    PattSchemaEntry.add_entry "formula" ;
    PattSchemaEntry.get_entry "formula"

let expr_expr = ExprEntry.add_entry "expr" ; ExprEntry.get_entry "expr"
let expr_patt = PattEntry.add_entry "expr" ; PattEntry.get_entry "expr"
let expr_expr_schema = create_gramm "expr_expr_schema"
let expr_patt_schema = create_gramm "expr_patt_schema"

let make_token ttype self = function
    |Lid("") -> 
            begin match ttype with
            |TExpr | TPatt -> Gramext.Stoken ("LIDENT", "")
            |TExprSchema | TPattSchema -> Gramext.Snterm (create_obj test_uid)
            end
    |Lid(s) when self = s -> Gramext.Sself 
    |Lid(s) -> 
            begin match ttype with
            |TExpr -> Gramext.Snterm (create_obj (ExprEntry.get_entry s))
            |TPatt -> Gramext.Snterm (create_obj (PattEntry.get_entry s))
            |TExprSchema -> Gramext.Snterm (create_obj (ExprSchemaEntry.get_entry s))
            |TPattSchema -> Gramext.Snterm (create_obj (PattSchemaEntry.get_entry s))
            end
    |Type(_) ->
            begin match ttype with
            |TExpr | TExprSchema -> Gramext.Snterm (create_obj Pcaml.expr)
            |TPatt | TPattSchema -> Gramext.Snterm (create_obj Pcaml.patt)
            end
    |List(s) ->
            begin match ttype with
            |TExpr -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (ExprEntry.get_entry s)),
                        Gramext.Stoken ("", ";"))
            |TPatt -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (PattEntry.get_entry s)),
                        Gramext.Stoken ("", ";"))
            |TExprSchema -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (ExprSchemaEntry.get_entry s)),
                        Gramext.Stoken ("", ";"))
            |TPattSchema -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (PattSchemaEntry.get_entry s)),
                        Gramext.Stoken ("", ";"))
            end
    |Symbol(s) -> Gramext.Stoken ("", s)
    |Const(s) ->  Gramext.Stoken ("", s) 
    |Expr -> 
            begin match ttype with
            |TExpr -> Gramext.Snterm (create_obj Pcaml.expr)
            |_-> failwith "make_token Expr"
            end
    |Patt -> 
            begin match ttype with
            |TPatt -> Gramext.Stoken ("", "_")
            |_-> failwith "make_token Patt"
            end
    |Atom -> 
            begin match ttype with
            |TExpr | TPatt -> Gramext.Snterm (create_obj test_uid)
            |TExprSchema | TPattSchema -> Gramext.Stoken ("LIDENT", "")
            end

let conntab = Hashtbl.create 17 
let new_conn l =
    try Hashtbl.find conntab l
    with Not_found ->
        let e = new_co "Conn" in
        let _ = Hashtbl.add conntab l e
        in e

let make_entry_patt self token_list =
    let gen_action tl =
        match tl with
        |[Atom] -> fun l ->      <:patt< `Atom($List.hd l$) >>
        |[Const(s)] -> fun l ->  <:patt< `$uid:s$ >>
        |[Lid(_)] -> fun l ->    <:patt< $List.hd l$ >>
        |[Type(_)] -> fun l ->   <:patt< $List.hd l$ >>
        |[Patt] -> fun l ->      <:patt< _ >>
        |[Expr] -> fun l ->      failwith "make_entry_patt"
        |Type(_) :: Symbol(":") :: _ -> fun l -> <:patt< ($list:l$) >>
        |Symbol("(")::_ -> fun l -> <:patt< $List.hd l$ >>
        |_ -> let id = new_conn tl in fun l -> <:patt< `$uid:id$($list:l$) >>
    in
    let actiontbl = Hashtbl.create 17 in
    let args : MLast.patt list ref = ref [] in
    let el = List.map (make_token TPatt self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->          args := <:patt< $lid:String.lowercase (Obj.magic x)$ >> :: !args
            |Const(_) ->      args := <:patt< `$uid:(Obj.magic x)$ >> :: !args
            (* |Lid("int") ->    args := <:patt< $int:(Obj.magic x)$ >> :: !args 
            |Lid("string") -> args := <:patt< $str:(Obj.magic x)$ >> :: !args *)
            |List(_) ->       args := <:patt< $lid:(Obj.magic x)$ >> :: !args 
            |Lid(_) ->        args := <:patt< $lid:(Obj.magic x)$ >> :: !args 
            |Patt ->          args := <:patt< $(Obj.magic x)$ >> :: !args 
            |Type(_) | Expr -> failwith "make_entry_patt"
        else args := (Obj.magic x) :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> failwith "action")
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_expr self token_list =
    let token_list = token_list in
    let gen_action tl =
        match tl with
        |[Atom] -> fun l ->     <:expr< `Atom($List.hd l$) >>
        |[Const(s)] -> fun l -> <:expr< `$uid:s$ >>
        |[Lid(_)] -> fun l ->   <:expr< $List.hd l$ >>
        |[Type(_)] -> fun l ->  <:expr< $List.hd l$ >>
        |Type(_) :: Symbol(":") :: _ -> fun l -> <:expr< ($list:l$) >>
        |Symbol("(")::_ -> fun l -> <:expr< $List.hd l$ >>
        |Symbol("{")::_ -> fun l -> <:expr< $List.hd l$ >>
        |_ -> let id = new_conn tl in fun l -> <:expr< `$uid:id$($list:l$) >>
    in
    let actiontbl = Hashtbl.create 17 in
    let args : MLast.expr list ref = ref [] in
    let el = List.map (make_token TExpr self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->          args := <:expr< $str:(Obj.magic x)$ >> :: !args
            |Const(_) ->      args := <:expr< $str:(Obj.magic x)$ >> :: !args
            |Lid("int") ->    args := <:expr< $int:(Obj.magic x)$ >> :: !args 
            |Lid("string") -> args := <:expr< $str:(Obj.magic x)$ >> :: !args 
            |List(_) ->       args := <:expr< $lid:(Obj.magic x)$ >> :: !args 
            |Lid(_) ->        args := <:expr< $lid:(Obj.magic x)$ >> :: !args 
            |Expr ->          args := <:expr< $lid:(Obj.magic x)$ >> :: !args 
            |Type(_) | Patt -> failwith "make_entry_expr"
        else args := (Obj.magic x) :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> failwith "action")
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_expr_schema self token_list =
    let gen_action tl =
        match tl with
        |[Atom] |[Const(_)] |[Lid(_)] |Symbol("(")::_ -> fun l -> List.hd l
        |_ -> let id = new_conn tl in fun l -> Ast.ExConn(id,l)
    in
    let actiontbl = Hashtbl.create 17 in
    let args : Ast.ex_term list ref = ref [] in
    let el = List.map (make_token TExprSchema self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        let x' = Obj.magic x in
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->            args := Ast.ExAtom(x') :: !args
            |Const(_) ->        args := Ast.ExCons(x') :: !args
            |Lid(_) |List(_) -> args := Ast.ExVar(x') :: !args 
            |Type(_) | Expr | Patt -> failwith "make_entry_expr_schema"
        else args := x' :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> failwith "action")
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_patt_schema self token_list =
    let gen_action tl =
        match tl with
        |[Atom] |[Const(_)] |[Lid(_)] |Symbol("(")::_ -> fun l -> List.hd l
        |_ -> let id = new_conn tl in fun l -> Ast.PaConn(id,l)
    in
    let actiontbl = Hashtbl.create 17 in
    let args : Ast.pa_term list ref = ref [] in
    let el = List.map (make_token TPattSchema self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        let x' = Obj.magic x in
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->            args := Ast.PaAtom(x') :: !args
            |Const(_) ->        args := Ast.PaCons(x') :: !args
            |Lid(_) |List(_) -> args := Ast.PaVar(x') :: !args 
            |Type(_) |Expr |Patt -> failwith "make_entry_patt_schema"
        else args := x' :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> failwith "action")
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let extend_schema = 
    let aux1 sep =
        EXTEND
        expr_expr: [
            [ex = Pcaml.expr; $sep$; sc = formula_expr -> <:expr< ($ex$,$sc$) >>]];
        expr_patt: [
            [pa = Pcaml.patt; $sep$; sc = formula_patt -> <:patt< ($pa$,$sc$) >>]];

        expr_expr_schema: [
                [ex = Pcaml.expr; $sep$; sc = formula_expr_schema -> Ast.ExLabt(ex,sc)]];
        expr_patt_schema: [
                [pa = Pcaml.patt; $sep$; sc = formula_patt_schema -> Ast.PaLabt(pa,sc)]];
        END
    in
    let aux2 () =
        EXTEND
        expr_expr: [[sc = formula_expr -> sc]];
        expr_patt: [[sc = formula_patt -> sc]];

        expr_expr_schema: [[sc = formula_expr_schema -> Ast.ExTerm(sc)]];
        expr_patt_schema: [[sc = formula_patt_schema -> Ast.PaTerm(sc)]];
        END
    in function
        |[Type(_) :: Symbol(sep) :: _] -> aux1 sep
        |_ -> aux2 ()

let extend_entry label entrylist =
    Grammar.extend
    [
        (create_obj (ExprEntry.get_entry label), 
        None, [None, None, (List.map (make_entry_expr label)
        (entrylist@[[Symbol("{");Expr;Symbol("}")]])) ]);
        (create_obj (PattEntry.get_entry label), 
        None, [None, None, (List.map (make_entry_patt label) (entrylist@[[Patt]])) ]);
        (create_obj (ExprSchemaEntry.get_entry label), 
        None, [None, None, (List.map (make_entry_expr_schema label) entrylist) ]);
        (create_obj (PattSchemaEntry.get_entry label), 
        None, [None, None, (List.map (make_entry_patt_schema label) entrylist) ]);
    ]

let extgramm gramms =
    (* we write a file with the marshalled representation of the grammar
     * to be then reused in other modules.
     * see the directive : source Modulename *)
    (* XXX: 4 is not fool proof !! *)
    let tmp_dir =
        let str = "/tmp/twb" ^ Unix.getlogin () in
        let _ =
            try ignore(Unix.stat str) with
            |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
        in str ^ "/"
    in
    let str =
        let s = (String.lowercase Sys.argv.(5)) in
        let re = Str.regexp "\\([a-z]+\\)\\.ml" in
        Str.replace_first re "\\1" s
    in
    let ch = open_out (tmp_dir^str^".gramm") in
    let _ = Marshal.to_channel ch gramms [] in
    let _ = close_out ch in
    List.iter (function
        |("expr",rules) -> extend_schema rules
        |(id,rules) ->
                PattEntry.add_entry id;
                ExprEntry.add_entry id;
                ExprSchemaEntry.add_entry id; 
                PattSchemaEntry.add_entry id; 
                extend_entry id rules;
    ) gramms 

let symbtab = Hashtbl.create 17 ;;

let lid strm =
    match Stream.peek strm with
    |Some(_,"formula") -> Stream.junk strm; "formula"
    |Some("LIDENT",s) when not(s = "expr") -> Stream.junk strm; s
    |_ -> raise Stream.Failure
;;
let lid = Grammar.Entry.of_parser Pcaml.gram "lid" lid ;;

let exprid strm =
    match Stream.peek strm with
    |Some(_,"expr") -> Stream.junk strm; "expr"
    |_ -> raise Stream.Failure
;;
let exprid = Grammar.Entry.of_parser Pcaml.gram "exprid" exprid ;;

let formulaid strm =
    match Stream.peek strm with
    |Some(_,"formula") -> Stream.junk strm; "formula"
    |_ -> raise Stream.Failure
;;
let formulaid = Grammar.Entry.of_parser Pcaml.gram "formulaid" formulaid ;;

let connective strm =
    let s =
        match Stream.peek strm with
        |Some("STRING",s) when not(List.mem s ["|";";";"(";")";"_"]) -> s
        |Some("STRING",s) when List.mem s ["|";";";"(";")";"_"] ->
                failwith (s^" is an illegal connective")
        |_ -> raise Stream.Failure
    in
    try Stream.junk strm; Hashtbl.add symbtab s () ; Symbol(s)
    with Stream.Failure -> raise Stream.Failure

let connective = Grammar.Entry.of_parser Pcaml.gram "connective" connective 

let symbol strm =
    let s = match Stream.peek strm with
        (* |Some("","|") | Some("",";")
        |Some("","(") | Some("",")") -> raise Stream.Failure
        *)
        |Some("",s) when (Hashtbl.mem symbtab s) -> s
        |Some("LIDENT",s)
        |Some("UIDENT",s) when (Hashtbl.mem symbtab s) -> s 
        |_ -> raise Stream.Failure
    in
    try Stream.junk strm; Symbol(s)
    with Stream.Failure -> raise Stream.Failure

let symbol = Grammar.Entry.of_parser Pcaml.gram "symbol" symbol 

let expand_grammar_type (id,rules) =
    let exptype = function
        |Lid(s) ->   <:ctyp< $lid:s$ >>
        |List(s) ->  <:ctyp< $lid:s$ list >>
        |Atom ->     <:ctyp< string >>
        |Const(s) -> <:ctyp< [= `$uid:s$ ] >>
        |_ -> failwith "exptype"
    in
    let aux = function
        |[Lid(s)] -> None
        |[Type(t);Symbol(":");Lid(s)]  -> Some("",[<:ctyp< ($exptype t$ * $lid:s$) >>])
        |[Atom] -> Some("Atom",[<:ctyp< string >>])
        |[Const(s)] -> Some(s,[])
        |Symbol("(") :: _ -> None
        |l ->
                let args = filter_map (function
                    |Symbol(_) -> None
                    |Type(_) -> None
                    |t -> Some(exptype t)
                    ) l
                in
                Some(new_conn l,List.rev args)
    in
    let fields = 
        match List.rev (filter_map aux rules) with
        (id, args)::tl ->
            let aux = function
                |("", [t]) -> t
                |(id, []) -> <:ctyp< [= `$uid:id$ ] >>
                |(id, args) -> <:ctyp< [= `$uid:id$ of ($list:args$) ] >>
            in
            List.fold_left (fun acc (id,args) ->
                let c = (aux (id, args))
                in <:ctyp< [= $acc$ | $c$ ] >>
            ) (aux (id, args)) tl
        |[] -> failwith "expand_grammar_type"
    in 
    ((_loc,id),[],fields,[])

let rec expand_grammar_expr_type = function
    |[[Lid(s)]] ->   <:ctyp< $lid:s$ >>
    |[[Atom]] ->     <:ctyp< string >>
    |[[Const(s)]] -> <:ctyp< [= `$uid:s$ ] >>
    |[[List(s)]] ->  <:ctyp< $lid:s$ list>>
    |[[Type(t);Symbol(":");r]]  -> 
            <:ctyp< ($expand_grammar_expr_type [[t]]$ *
            $expand_grammar_expr_type [[r]]$) >>
    |_ -> failwith "expand_grammar_expr_type"
    
let expand_grammar_type_list gramms =
        List.map (function
            |("expr",rules) -> 
                    ((_loc,"expr"),[], expand_grammar_expr_type rules ,[])
            |(id,rules) -> expand_grammar_type (id,rules)
        ) gramms

let expand_printer gramm =
    let aux (name,rules) = 
        let gen_pel = function
            |[Atom] ->
                    Some(<:patt< `Atom( a ) >>,None,
                    <:expr< Printf.sprintf $str:"%s"$ a >>)
            |[Const(s)] ->
                    Some(<:patt< `$uid:s$ >>,None,
                    <:expr< Printf.sprintf $str:s$  >>)
            |[Lid("")] |[Type(_)] |[Patt] |[Expr] 
            |Symbol("("):: _ -> None
            |[Lid(id)] ->
                    Some(<:patt< f >>,None,
                     <:expr< $lid:id^"_printer"$ f >>)
            |Type(_) :: Symbol(":") :: Lid(id) :: _ ->
                    Some(<:patt< (_,f) >>,None,
                     <:expr< $lid:id^"_printer"$ f >>)

            |tl ->
                    let f =
                        List.fold_left (fun s i -> s^i) ""
                        (List.map (function |Symbol(s) -> " "^s |_ -> " %s") tl) 
                    in
                    let (l,_) =
                        List.fold_left (fun (acc,i) s -> 
                            match s with
                            |Symbol(_) -> (acc,i)
                            |Lid(id) -> (("c"^string_of_int i,id)::acc,i+1)
                            |_ -> failwith "printer"
                        ) ([],0) tl
                    in
                    let exl =
                        List.map (fun (e,id) ->
                            <:expr< $lid:id^"_printer"$ $lid:e$ >>
                        ) (List.rev l)
                    in 
                    let pal = List.map (fun (e,_) -> 
                            <:patt< $lid:e$ >>
                        ) (List.rev l)
                    in 
                    let id = new_conn tl in
                    Some(
                        <:patt< `$uid:id$($list:pal$) >>,None,
                        List.fold_left (fun a e ->
                            <:expr< $a$ $e$ >>
                        ) <:expr< Printf.sprintf $str:f$  >> exl
                        )
        in
        <:str_item<
        value rec $lid:name^"_printer"$ = 
            fun [ $list:filter_map gen_pel rules$ ]
        >>
    in <:str_item< declare $list:List.map aux gramm$ end >>

let expand_ast2input gramm = 
    let rec aux (name,rules) =
        let gen_pel = function
            |[Atom] -> Some(<:patt< Ast.ExAtom(a) >>,None,<:expr< `Atom a>>)
            |[Const(s)] -> Some(<:patt< Ast.ExCons($str:s$) >>,None,<:expr< `$uid:s$>>)
            |[Lid(_)] |[Type(_)] |[Patt] |[Expr] 
            |Type(_) :: Symbol(":") :: _
            |Symbol("("):: _ -> None
            |tl ->
                    let (l,_) =
                        List.fold_left (fun (acc,i) s -> 
                            match s with
                            |Symbol(_) -> (acc,i)
                            |Lid(id) -> (
                                <:expr<
                                $lid:id^"_ast2input"$ (List.nth l $int:string_of_int i$)
                                >>::acc,i+1)
                            |_ -> failwith "ast2input"
                        ) ([],0) tl
                    in
                    let id = new_conn tl in
                    Some(
                        <:patt< Ast.ExConn($str:id$,l) >>,None,
                        <:expr< `$uid:id$($list:List.rev l$) >>
                        )
        in
        let def = <:patt< _ >>, None, <:expr< failwith "ast2input" >> in
        <:str_item<
        value rec $lid:name^"_ast2input"$ = 
            fun [ $list:(filter_map gen_pel rules)@[def]$ ]
        >>
    in <:str_item< declare $list:List.map aux gramm$ end >>

EXTEND
GLOBAL: Pcaml.str_item; 

Pcaml.str_item: [[
    "CONNECTIVES"; "["; l = LIST1 connective SEP ";"; "]" ->
            <:str_item< "" >>

    |"GRAMMAR"; gramms = LIST1 gramm; "END" ->
        extgramm gramms ;
        let ty = expand_grammar_type_list gramms in
        let pr = expand_printer gramms in
        let ast = expand_ast2input gramms in
        let sty = <:str_item< type $list:ty$ >> in
        <:str_item< declare $list:[sty;pr;ast]$ end >>
]];

gramm: [
    [ exprid ; ":=" ; t = ptype ;  e = OPT [ ":" ; p = plid -> p ]; ";" ->
          begin match e with
          |None -> ("expr", [[t]])
          |Some(l) -> ("expr",[Type(t)::[Symbol(":");Lid(l)]])
          end
(*  
    | nodeid ; ":="; l = LIST1 [ p = plid -> p | "=>" -> Symbol("=>") ]; ";" -> 
*)        
    | p = lid; ":="; rules = LIST1 rule SEP "|" ; ";" ->
        (p,rules@[[Lid("")]]@[[Symbol("(");Lid(p);Symbol(")")]]) 
]];

rule: [[ psl = LIST1 psymbol -> psl ]];

psymbol: [
    [ "Atom"  -> Atom
    | e = symbol -> e
    | e = ptype -> e
    | e = const -> e
]];

const: [[ u = UIDENT -> Hashtbl.add const_table u () ; Const(u) ]];

ptype: [
    [ t = plid ; "list" -> List(t) 
(*    | l = LIST1 plid SEP "*" -> Tuple(l) *)
    | t = plid -> Lid(t)
]];

plid: [
    [ 
        (* u = UIDENT ; "."; i = LIDENT -> u^"."^i *)
    i = LIDENT -> i 
]];

Pcaml.expr: LEVEL "simple" [
    [ formulaid; "("; e = formula_expr; ")" -> <:expr< ( $e$ : formula ) >>
    | exprid;    "("; e = expr_expr; ")"    -> <:expr< ( $e$ : expr ) >>
]];

Pcaml.patt: [
    [ formulaid; "("; "_"; ")" -> <:patt< #formula >>
    | exprid;    "("; "_"; ")" -> <:patt< _ >>
    | formulaid; "("; e = formula_patt; ")" -> <:patt< $e$ >>
    | exprid;    "("; e = expr_patt;    ")" -> <:patt< $e$ >>
]];

(*
(* A{s/t} is the formula A with all occurrences of t substituted by s *) 
(* FIXME: the substitution should be possible inside a term... this require
 * to change the ast and re-write the expand_expression_expr function *)
ocaml_expr_term: [
  [x = LIDENT; "{"; s = ocaml_expr_term; "/"; t = ocaml_expr_term; "}" ->
          Ast.Apply("__substitute",[Ast.Term(Ast.Var x);s;t])
  |t = formula_expr -> Ast.Term(t)
]];

ocaml_patt_term: [
  [t = formula_patt -> Ast.Term(t)]
];

ocaml_expr:   
[["["; e = Pcaml.expr LEVEL "simple"; "]" -> Ast.Expr e
  |x = test_constant -> Ast.Const x
  |x = test_uid -> Ast.Atom x
  |x = LIDENT; "("; e = Pcaml.expr; ")" -> Ast.FAtom(x,e)
  |x = LIDENT -> Ast.Var x
  |"("; p = formula_expr; ")" -> p
  ] 
];

ocaml_patt:
[["Constant" -> Ast.Const ""
  |"Atom" -> Ast.Atom ""
  |x = test_constant -> Ast.Const x
  |x = test_uid -> Ast.Atom x
  |x = LIDENT -> Ast.Var x
  |"("; p = formula_patt; ")" -> p
  ]
];
*)
END
;;
