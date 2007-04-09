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
let blanumseq : Ast.numcont array Grammar.Entry.e = create_gramm "blanumseq"
let bladenseq : Ast.dencont array Grammar.Entry.e = create_gramm "bladenseq"
let numseq = create_gramm "numseq"
let denseq = create_gramm "denseq"
let node : (Ast.numerator * Ast.ruletype * (Ast.denominator list * Ast.branchcond)) Grammar.Entry.e = create_gramm "node"
let num = create_gramm "num"
let denlist = create_gramm "denlist"

let conn_table = Hashtbl.create 17
let new_conn = function
    |[] -> failwith "new_conn empty list"
    |l ->
        try Hashtbl.find conn_table l
        with Not_found ->
            let e = new_co "Conn" in
            let _ = Hashtbl.add conn_table l e
            in e

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
            |_-> assert(false)
            end
    |Patt -> 
            begin match ttype with
            |TPatt -> Gramext.Stoken ("", "_")
            |_-> assert(false)
            end
    |Atom -> 
            begin match ttype with
            |TExpr | TPatt -> Gramext.Snterm (create_obj test_uid)
            |TExprSchema | TPattSchema -> Gramext.Stoken ("LIDENT", "")
            end

let make_entry_patt self token_list =
    let gen_action = function
        |[Atom] -> fun l ->      <:patt< `Atom($List.hd l$) >>
        |[Const(s)] -> fun l ->  <:patt< `$uid:s$ >>
        |[Lid(_)] -> fun l ->    <:patt< $List.hd l$ >>
        |[Type(_)] -> fun l ->   <:patt< $List.hd l$ >>
        |[Patt] -> fun l ->      <:patt< _ >>
        |[Expr] -> fun l ->      assert(false)
        |Type(_) :: Symbol(":") :: _ -> fun l -> <:patt< ($list:l$) >>
        |Symbol("(")::_ -> fun l -> <:patt< $List.hd l$ >>
        |tl -> let id = new_conn tl in fun l -> <:patt< `$uid:id$($list:l$) >>
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
            |Type(_) | Expr -> assert(false)
        else args := (Obj.magic x) :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> assert(false))
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_expr self token_list =
    let token_list = token_list in
    let gen_action = function
        |[Atom] -> fun l ->     <:expr< `Atom($List.hd l$) >>
        |[Const(s)] -> fun l -> <:expr< `$uid:s$ >>
        |[Lid(_)] -> fun l ->   <:expr< $List.hd l$ >>
        |[Type(_)] -> fun l ->  <:expr< $List.hd l$ >>
        |Type(_) :: Symbol(":") :: _ -> fun l -> <:expr< ($list:l$) >>
        |Symbol("(")::_ -> fun l -> <:expr< $List.hd l$ >>
        |Symbol("{")::_ -> fun l -> <:expr< $List.hd l$ >>
        |tl -> let id = new_conn tl in fun l -> <:expr< `$uid:id$($list:l$) >>
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
            |Type(_) | Patt -> assert(false)
        else args := (Obj.magic x) :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found ->  assert(false))
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
            |Type(_) | Expr | Patt -> assert(false) 
        else args := x' :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found ->  assert(false))
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_patt_schema self token_list =
    let gen_action = function
        |[Atom] |[Const(_)] |[Lid(_)] |Symbol("(")::_ -> fun l -> List.hd l
        |tl -> let id = new_conn tl in fun l -> Ast.PaConn(id,l)
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
            |Type(_) |Expr |Patt -> assert(false)
        else args := x' :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> assert(false))
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

let extend_sequent_node (_,l) =
    let extend_seq cont token_list =
        let gen_action _ = fun l -> Array.of_list l in
        let actiontbl = Hashtbl.create 17 in
        let args = ref [] in
        let el = 
            filter_map (function
                |Type(_) -> Some(Gramext.Snterm (create_obj cont))
                |Symbol(s) -> Some(Gramext.Stoken ("", s))
                |_ -> None
            ) token_list
        in
        let _ = 
            if Hashtbl.mem actiontbl token_list then ()
            else Hashtbl.add actiontbl token_list (gen_action token_list)
        in
        let build_action t x =
            let x' = Obj.magic x in
            match t with
            |Symbol(_) -> ()
            |Type(_) -> args := x' :: !args
            |_ -> assert(false)
        in
        let action =
          List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
          (Obj.magic (fun _loc ->
              let l = !args in
              args := [] ;
              try (Hashtbl.find actiontbl token_list) l
              with Not_found -> assert(false))
          ) token_list
        in
        (el,Gramext.action (Obj.repr action))
    in
    EXTEND node: [[ dl = denlist; t = test_sep; n = num -> (n,t,dl) ]]; END; 
    Grammar.extend
    [ (create_obj blanumseq, None, [None, None, List.map (extend_seq numseq) l ]);
      (create_obj bladenseq, None, [None, None, List.map (extend_seq denseq) l ]) 
    ]

let extend_tableau_node () =
    EXTEND
      node: [[ n = num; t = test_sep; dl = denlist -> (n,t,dl) ]];
      bladenseq: [[d = denseq -> [|d|] ]];
      blanumseq: [[n = numseq -> [|n|] ]];
    END

let extend_node_type = function
    |[] -> extend_tableau_node ()
    |[l] -> extend_sequent_node l
    |_ -> assert(false)

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

let writegramm gramms =
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
        let re = Str.regexp "\\([a-zA-z0-9]+\\)\\.ml" in
        Str.replace_first re "\\1" s
    in
    (* write the grammar definition to a file *)
    let ch = open_out (tmp_dir^str^".gramm") in
    let constlist = Hashtbl.fold (fun k _ acc -> k :: acc) const_table [] in
    let connlist = Hashtbl.fold (fun k _ acc -> k :: acc) symbol_table [] in
    Marshal.to_channel ch (constlist,connlist,gramms) [];
    close_out ch

(*
let readgramm extmodule gramms = 
    match extmodule with None -> gramms
    |Some(m) ->
        let tmp_dir =
            let str = "/tmp/twb" ^ Unix.getlogin () in
            let _ =
                try ignore(Unix.stat str) with
                |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
            in str ^ "/"
        in
        let ch = open_in (tmp_dir^String.lowercase m^".gramm") in
        let (_,_,gl) = Marshal.from_channel ch in
        let _ = close_in ch in
        let merge l1 l2 =
            let tab = Hashtbl.create 17 in
            let _ =
                List.iter (function
                    ("expr",r1) -> Hashtbl.replace tab "expr" r1
                    |(id,r1) ->
                        try let r2 = Hashtbl.find tab id in
                            Hashtbl.replace tab id (unique (r1@r2))
                        with Not_found -> Hashtbl.add tab id r1
                ) (l1@l2)
            in Hashtbl.fold (fun k v acc -> (k,v)::acc) tab []
        in List.rev (merge gramms (List.rev gl))
*)

let readgramm m = 
    let tmp_dir =
        let str = "/tmp/twb" ^ Unix.getlogin () in
        let _ =
            try ignore(Unix.stat str) with
            |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
        in str ^ "/"
    in
    let ch = open_in (tmp_dir^String.lowercase m^".gramm") in
    let (constlist,symbollist,gramms) = Marshal.from_channel ch in
    let _ = close_in ch in
    (constlist,symbollist,gramms)

let extgramm gramms =
    List.iter (function
        |("expr",rules) -> extend_schema rules
        |(id,rules) ->
                PattEntry.add_entry id;
                ExprEntry.add_entry id;
                ExprSchemaEntry.add_entry id; 
                PattSchemaEntry.add_entry id; 
                extend_entry id rules;
    ) gramms 

let lid strm =
    match Stream.peek strm with
    |Some(_,"formula") -> Stream.junk strm; "formula"
    |Some("LIDENT",s) when not(s = "expr") -> Stream.junk strm; s
    |_ -> raise Stream.Failure
let lid = Grammar.Entry.of_parser Pcaml.gram "lid" lid

let exprid strm =
    match Stream.peek strm with
    |Some(_,"expr") -> Stream.junk strm; "expr"
    |_ -> raise Stream.Failure
let exprid = Grammar.Entry.of_parser Pcaml.gram "exprid" exprid 

let nodeid strm =
    match Stream.peek strm with
    |Some(_,"node") -> Stream.junk strm; "node"
    |_ -> raise Stream.Failure
let nodeid = Grammar.Entry.of_parser Pcaml.gram "nodeid" nodeid 

let formulaid strm =
    match Stream.peek strm with
    |Some(_,"formula") -> Stream.junk strm; "formula"
    |_ -> raise Stream.Failure
let formulaid = Grammar.Entry.of_parser Pcaml.gram "formulaid" formulaid 

let connective strm =
    let s =
        match Stream.peek strm with
        |Some("STRING",s) when not(List.mem s ["|";";";"(";")";"_"]) -> s
        |Some("STRING",s) when List.mem s ["|";";";"(";")";"_"] ->
                failwith (s^" is an illegal connective")
        |_ -> raise Stream.Failure
    in
    try Stream.junk strm; Hashtbl.add symbol_table s () ; Symbol(s)
    with Stream.Failure -> raise Stream.Failure

let connective = Grammar.Entry.of_parser Pcaml.gram "connective" connective 

let symbol strm =
    let s = match Stream.peek strm with
        (* |Some("","|") | Some("",";")
        |Some("","(") | Some("",")") -> raise Stream.Failure
        *)
        |Some("",s) when (Hashtbl.mem symbol_table s) -> s
        |Some("LIDENT",s)
        |Some("UIDENT",s) when (Hashtbl.mem symbol_table s) -> s 
        |_ -> raise Stream.Failure
    in
    try Stream.junk strm; Symbol(s)
    with Stream.Failure -> raise Stream.Failure

let symbol = Grammar.Entry.of_parser Pcaml.gram "symbol" symbol 

let expand_grammar_type (id,rules) =
    let typevars = ref [(id,(true,true))] in
    let exptype = function
        |Lid(s) when s = id -> <:ctyp< '$lid:s$ >>
        |List(s) when s = id ->  <:ctyp< '$lid:s$ list >>
        |Lid(s) -> typevars := (s,(true,true))::!typevars ; <:ctyp< '$lid:s$ >>
        |List(s) -> typevars := (s,(true,true))::!typevars ; <:ctyp< '$lid:s$ list >>
        |Atom ->     <:ctyp< string >>
        |Const(s) -> <:ctyp< [= `$uid:s$ ] >>
        |_ -> assert(false)
    in
    let aux = function
        |[Lid(s)] -> None
        |[Type(t);Symbol(":");Lid(s)]  -> Some("",[<:ctyp< ($exptype t$ * '$lid:s$) >>])
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
        |[] -> assert(false)
    in
    let closedtype =
        let tvl = List.map(fun (t,_) -> <:ctyp< '$lid:t$ >>) !typevars in
        <:ctyp< $lid:id^"_open"$ ($list:tvl$) as '$lid:id$ >>
    in
    [((_loc,id^"_open"),!typevars,fields,[]);((_loc,id),[],closedtype,[])]

let rec expand_grammar_expr_type = function
    |[[Lid(s)]] ->   <:ctyp< $lid:s$ >>
    |[[Atom]] ->     <:ctyp< string >>
    |[[Const(s)]] -> <:ctyp< [= `$uid:s$ ] >>
    |[[List(s)]] ->  <:ctyp< $lid:s$ list>>
    |[[Type(t);Symbol(":");r]]  -> 
            <:ctyp< ($expand_grammar_expr_type [[t]]$ *
            $expand_grammar_expr_type [[r]]$) >>
    |_ -> assert(false)
    
let expand_grammar_type_list gramms =
        List.flatten (
            List.map (function
                |("expr",rules) -> 
                        [((_loc,"expr"),[], expand_grammar_expr_type rules ,[])]
                |(id,rules) -> expand_grammar_type (id,rules)
            ) gramms
        )

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
                            |_ -> assert(false)
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
        value rec $lid:name^"_printer"$ = fun [ $list:filter_map gen_pel rules$ ]
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
                            |_ -> assert(false) 
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

let remove_node_entry = List.filter (fun (l,_) -> not(l = "node"))
let select_node_entry = List.filter (fun (l,_) -> l = "node")

EXTEND
GLOBAL: Pcaml.str_item; 

Pcaml.str_item: [[
    "CONNECTIVES"; "["; l = LIST1 connective SEP ";"; "]" ->
            <:str_item< "" >>

    |"GRAMMAR"; gramms = LIST1 gramm; "END" ->
            let _ = writegramm gramms in
            let _ = extgramm (remove_node_entry gramms) in
            let _ = extend_node_type (select_node_entry gramms) in 
            let ty = expand_grammar_type_list (remove_node_entry gramms) in
            let pr = expand_printer (remove_node_entry gramms) in
            let ast = expand_ast2input (remove_node_entry gramms) in
            let sty = <:str_item< type $list:ty$ >> in
            <:str_item< declare $list:[sty;pr;ast]$ end >>
]];

gramm: [
    [ exprid ; ":=" ; t = ptype ;  e = OPT [ ":" ; p = plid -> p ]; ";" ->
          begin match e with
          |None -> ("expr", [[t]])
          |Some(l) -> ("expr",[Type(t)::[Symbol(":");Lid(l)]])
          end
  
    | nodeid ; ":="; c = cont ; l = LIST0 [ s = symbol; c = cont -> [s;c] ] ; ";" ->
            ("node",[c::(List.flatten l)])
        
    | p = lid; ":="; rules = LIST1 rule SEP "|" ; ";" ->
        (p,rules@[[Lid("")]]@[[Symbol("(");Lid(p);Symbol(")")]]) 
]];

cont: [
    [ "set" -> Type(Lid "set")
    | "mset" -> Type(Lid "mset")
    | "singleton" -> Type(Lid "singleton") 
]];

rule: [[ psl = LIST1 psymbol -> psl ]];

psymbol: [
    [ "Atom"  -> Atom
    (* | "extend"; m = UIDENT -> Extend(m) *)
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

*)
END
;;
