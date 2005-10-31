(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Basictype
open Genlex

Grammar.warning_verbose := false ;;
Grammar.error_verbose := true ;;

let gram = Grammar.gcreate (Plexer.gmake ());;
let expr_term = Grammar.Entry.create gram "expr_term";;
let input_line = Grammar.Entry.create gram "input_line";;

let add_uconn op co =
    EXTEND
      expr_term: LEVEL "Simple"
      [[ $op$; x = expr_term -> co x ]];
    END
;;

let add_biconn lev op co =
    EXTEND
      expr_term: LEVEL $lev$
      [[ x = expr_term; $op$; y = expr_term -> co (x,y) ]];
    END
;;

let add_muconn op1 op2 co =
    EXTEND
      expr_term: LEVEL "Simple"
      [[ $op1$; i = INT; $op2$; x = expr_term -> co (int_of_string i,x) ]];
    END
;;

let add_const name =
    EXTEND
      expr_term: LEVEL "Simple"
      [[ $name$ -> Constant (Basictype.newcore 1 [|0|],name) ]];
    END
;;


EXTEND
GLOBAL : expr_term input_line;

  input_head: [[ r = LIST1 expr_term SEP ";" -> (r,r,r) ]];

  input_line: [[ id = LIDENT; ":"; i = input_head -> i ]];
 
  expr_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
    [ x = LIDENT -> Atom(Basictype.newcore 1 [|0|],x)
      | "("; p = expr_term; ")" -> p ]
    ];

END

let buildParser table s =
    let parse s =
        Grammar.Entry.parse expr_term (Stream.of_string s)
    in
    let _ =
        List.iter(function
            |"Const",[name],`Const -> add_const name
            |"Simple",[op],`Uconn(co) -> add_uconn op co
            |"Simple",[op1;op2],`Muconn(co) -> add_muconn op1 op2 co
            |lev,[op],`Biconn(co) -> add_biconn lev op co
            |_ -> failwith "buildParser"
        ) table
(*    in let _ = Grammar.Entry.print expr_term *)
    in [`Formula(parse s)]
;;

