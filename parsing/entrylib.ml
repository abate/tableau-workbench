
module Make(T : sig val gram : Grammar.g end) = struct

    type ttype = TExpr | TPatt | TExprSchema | TPattSchema

    let create_gramm l = Grammar.Entry.create T.gram l
    let create_obj l = Grammar.Entry.obj l

    type stype =
        | Atom
        | Const of string
        | Symbol of string
        | Lid of string
        | List of string
        | Type of stype
        | Patt
        | Expr

    let stype_list_to_string l =
        let rec aux = function
            |Atom -> "Atom"
            |Const(s) -> "Const("^s^")"
            |Lid(s) -> "Lid("^s^")"
            |Symbol(s) -> "Symbol("^s^")"
            |List(s) -> "List("^s^")"
            |Type(s) -> ("Type"^(aux s))
            |Expr -> "Expr"
            |Patt -> "Patt"
        in
        Printf.sprintf "[%s]\n"
        (List.fold_left (fun s x -> (s ^ (aux x) ^ ";")) "" l)

    module EntryMake(T : sig type t val ttype : ttype end) =
        struct
            let ttype = T.ttype

            let entrytab : (string, T.t Grammar.Entry.e) Hashtbl.t = Hashtbl.create 17
            let label s = match ttype with
                |TPatt -> s^"_patt"
                |TExpr  -> s^"_expr"
                |TExprSchema -> s^"_expr_schema" 
                |TPattSchema -> s^"_patt_schema" 
                
            let mem_entry s = Hashtbl.mem entrytab (label s)
            let add_entry s =
                if mem_entry s then ()
                else begin
                    Hashtbl.add entrytab (label s) (create_gramm (label s))
                end
            let get_entry s =
                try Hashtbl.find entrytab (label s)
                with Not_found ->
                    failwith (Printf.sprintf "The Grammar Entry '%s' is used but not declared" s)
                
            let entries_to_string () =
                Hashtbl.fold (fun k v s ->
                    Grammar.print_entry Format.str_formatter (create_obj v);
                    Format.sprintf "%s%s: @\n@[%s@]@\n@\n" s k (Format.flush_str_formatter ())
                ) entrytab ""

        end

end
