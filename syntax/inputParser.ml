(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Basictype
open Genlex

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


EXTEND
GLOBAL : expr_term input_line;

  input_head: [[ r = LIST1 expr_term SEP ";" -> (r,r,r) ]];

  input_line: [[ id = LIDENT; ":"; i = input_head -> i ]];
 
  expr_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ x = LIDENT -> Atom(Basictype.nc,x)
      | "("; p = expr_term; ")" -> p ]
    ];

END

let buildParser table s =
    let parse s =
        Grammar.Entry.parse input_line (Stream.of_string s)
    in
    let _ =
        List.iter(function
             "Simple",[op],`Uconn(co) -> add_uconn op co
            |lev,[op],`Biconn(co) -> add_biconn lev op co
            |"Simple",[op1;op2],`Muconn(co) -> add_muconn op1 op2 co
            |_ -> failwith "buildParser"
        ) table
    in parse s
;;

