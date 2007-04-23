(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

module Make(T: sig type t val ast2input : Ast.ex_term -> t end) = 
struct

    module PcamlGramm = Entrylib.Make(struct
        let gram = Grammar.gcreate (Plexer.gmake ()) end
    )
    open PcamlGramm

    module ExprEntry = EntryMake(
        struct 
            type t = Ast.ex_term 
            let ttype = TExprSchema 
    end)

    let formula_expr_schema =
        ExprEntry.add_entry "formula" ;
        ExprEntry.get_entry "formula"

    let expr_expr_schema = create_gramm "expr_expr_schema"
    let expr_expr_seq = create_gramm "expr_expr_seq"

    let filter_map f l =
        let rec aux acc f = function
            |[] -> acc
            |h::t ->
                    begin match f h with
                    |None -> aux acc f t
                    |Some(x) -> aux (x::acc) f t
                    end
        in aux [] f l

    let new_co =
      let counter = ref 0 in
      fun s ->
          incr counter;
          s ^ string_of_int !counter

    let conn_table = Hashtbl.create 17
    let new_conn l =
    try Hashtbl.find conn_table l
    with Not_found -> 
        let e = new_co "Conn" in
        let _ = Hashtbl.add conn_table l e
        in e

    let make_token self = function
        |Atom -> Gramext.Stoken ("LIDENT", "")
        |Lid(s) when self = s -> Gramext.Sself
        |Lid(s) -> Gramext.Snterm (create_obj (ExprEntry.get_entry s))
        |List(s) -> Gramext.Slist1sep (
            Gramext.Snterm (create_obj (ExprEntry.get_entry s)),
            Gramext.Stoken ("", ";"))
        |Symbol(s) -> Gramext.Stoken ("", s)
        |Const(s) ->  Gramext.Stoken ("", s)
        |_ -> failwith "make_token input"

    let make_entry_input self token_list =
        let gen_action tl =
            match tl with 
            |[Atom] |[Const(_)] |[Lid(_)] |Symbol("(")::_ -> fun l -> List.hd l
            |_ -> let id = new_conn tl in fun l -> Ast.ExConn("",id,l)
        in
        let actiontbl = Hashtbl.create 17 in
        let args : Ast.ex_term list ref = ref [] in
        let el = List.map (make_token self) token_list in
        let _ =  
            if Hashtbl.mem actiontbl token_list then ()
            else Hashtbl.add actiontbl token_list (gen_action token_list)
        in
        let build_action t x =
            let x' = Obj.magic x in
            if Obj.tag x = Obj.string_tag then
                match t with
                |Symbol(_) -> ()
                |Atom ->            args := Ast.ExAtom("",x') :: !args
                |Const(_) ->        args := Ast.ExCons("",x') :: !args
                |Lid(_) |List(_) (*  -> args := Ast.ExVar(x') :: !args *)
                |Type(_) | Expr | Patt -> failwith "make_entry_input"
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

    let extend_schema () =  
        EXTEND
            expr_expr_schema: [[sc = formula_expr_schema -> Ast.ExTerm(sc)]];
        END

    let extend_entry label entrylist =
        let el =
            List.filter (function [Lid("")] -> false | _ -> true ) entrylist
        in
        Grammar.extend
        [ (create_obj (ExprEntry.get_entry label),
            None, [None, None, (List.map (make_entry_input label) el) ])
        ]

    let make_expr_node token_list =
        let gen_action _ = fun l -> l in
        let actiontbl = Hashtbl.create 17 in
        let args = ref [] in
        let el =
            filter_map (function
                |Type(_) -> Some(Gramext.Slist0sep (
                        Gramext.Snterm (create_obj formula_expr_schema),
                        Gramext.Stoken ("", ";"))
                        )
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

    let extend_node rules = 
        Grammar.extend
        [ (create_obj expr_expr_seq, None, [None, None, 
        List.map make_expr_node rules ]) ]

    let extend_node_type = function
        |[] -> EXTEND expr_expr_seq: [[d = formula_expr_schema -> [[d]] ]]; END
        |[("node",l)] -> extend_node l
        |_ -> assert(false)

    let extgramm () =
        let tmp_dir =
            let str = "/tmp/twb" ^ Sys.getenv("LOGNAME") in
            let _ =
                try ignore(Unix.stat str)
                with Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
            in str ^ "/"
        in
        let str =
            let s = (String.lowercase Sys.argv.(0)) in
            let re = Str.regexp
            "\\(/?[a-z0-9][a-zA-Z0-9]*/\\)*\\(\\./\\)*\\([a-zA-Z0-9]+\\)\\.twb" in
            if Str.string_match re s 0 then Str.matched_group 3 s
            else (print_endline s ; assert false)
        in
        let ch =
            try open_in (tmp_dir^str^".gramm")
            with Sys_error _ ->
                failwith (Printf.sprintf
                "Dependency error: compile the file %s.ml first" str)
        in
        let (_,gramms) = Marshal.from_channel ch in
        let _ = close_in ch in
        let remove_node_entry = List.filter (fun (l,_) -> not(l = "node")) in
        let select_node_entry = List.filter (fun (l,_) -> l = "node") in
        extend_node_type (select_node_entry gramms);
        List.iter (function
            |("expr",rules) -> extend_schema ()
            |(id,rules) ->
                    ExprEntry.add_entry id;
                    extend_entry id rules;
        ) (remove_node_entry gramms)

    let initParser = extgramm 

    let buildParser s =
        let parse s = Grammar.Entry.parse expr_expr_seq (Stream.of_string s) 
        in List.map (List.map T.ast2input) (parse s)

end
