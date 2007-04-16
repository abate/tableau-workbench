(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

let _loc = Token.dummy_loc

let hist_table  : (string, string * MLast.ctyp * MLast.expr) Hashtbl.t = Hashtbl.create 50
let vars_table  : (string, string * MLast.ctyp * MLast.expr) Hashtbl.t = Hashtbl.create 50
let const_table : (string, string) Hashtbl.t = Hashtbl.create 50
let tactic_table : (string, unit) Hashtbl.t = Hashtbl.create 50
let expr_table : (string, MLast.expr) Hashtbl.t = Hashtbl.create 50
let symbol_table : (string, unit) Hashtbl.t = Hashtbl.create 17
let gramm_table : (string, unit) Hashtbl.t = Hashtbl.create 17

let (=~) s re = Str.string_match (Str.regexp re) s 0
let get_match i s = Str.matched_group i s

let rec unique = function
    |[] -> []
    |h::t -> h:: unique (List.filter (fun x -> not(x = h)) t)

let filter_map f l =
    let rec aux acc f = function
        |[] -> acc
        |h::t ->
                begin match f h with
                |None -> aux acc f t
                |Some(x) -> aux (x::acc) f t
                end
    in aux [] f l

let list_to_exprlist l =
    List.fold_right (
        fun x l -> <:expr< [ $x$ :: $l$ ] >>
    ) l <:expr< [] >>

let pa_expr_is_var = function
    |Ast.PaTerm(Ast.PaVar(_)) -> true
    |Ast.PaLabt(_,Ast.PaVar(_)) -> true
    |_ -> false

let new_id =
  let counter = ref 0 in
  fun s ->
      incr counter;
      "__" ^s^ string_of_int !counter

let new_co =
  let counter = ref 0 in
  fun s ->
      incr counter;
      s ^ string_of_int !counter

let test_muvar strm =
    match Stream.peek strm with
    | Some("UIDENT",s) when Hashtbl.mem tactic_table s -> Stream.junk strm; Ast.TaMVar(s)
    | Some("UIDENT",s) -> Stream.junk strm; Ast.TaBasic(s)
    | _ -> raise Stream.Failure
;;
let test_muvar = Grammar.Entry.of_parser Pcaml.gram "test_muvar" test_muvar ;;

let muvar strm =
    match Stream.peek strm with
    | Some("UIDENT",s) -> Stream.junk strm; Hashtbl.replace tactic_table s (); s
    | _ -> raise Stream.Failure 
;;
let muvar = Grammar.Entry.of_parser Pcaml.gram "muvar" muvar ;;

let test_sep strm =
    match Stream.peek strm with
    | Some(_,s) when s =~ "==+" -> Stream.junk strm; Ast.Explicit
    | Some(_,s) when s =~ "--+" -> Stream.junk strm; Ast.Implicit
    | _ -> raise Stream.Failure
;;
let test_sep = Grammar.Entry.of_parser Pcaml.gram "test_sep" test_sep ;;

let test_uid strm =
    match Stream.peek strm with
    | Some (("UIDENT", s)) when not(Hashtbl.mem const_table s) -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_uid = Grammar.Entry.of_parser Pcaml.gram "test_uid" test_uid ;;

let test_history strm =
    match Stream.peek strm with
    | Some (("UIDENT", s)) when Hashtbl.mem hist_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_history = Grammar.Entry.of_parser Pcaml.gram "test_history" test_history ;;

let test_constant strm =
    match Stream.peek strm with
    | Some (("UIDENT", s)) when Hashtbl.mem const_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_constant = Grammar.Entry.of_parser Pcaml.gram "test_constant" test_constant ;;

let test_variable strm =
    match Stream.peek strm with
    | Some (("LIDENT", s)) when Hashtbl.mem vars_table s -> Stream.junk strm; s
    | _ -> raise Stream.Failure
;;
let test_variable = Grammar.Entry.of_parser Pcaml.gram "test_variable" test_variable ;;

(* FIXME: to be moved *)
module Option = struct
    let get = function Some x -> x | None -> failwith "Option.get"
    let optlist = function Some l -> l | None -> []
    let optarray = function Some l -> l | None -> [||]
    let is_none = function Some _ -> false | None -> true
end
