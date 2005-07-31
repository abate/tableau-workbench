(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Basictype
open Genlex

let gram = Grammar.gcreate (Plexer.gmake ());;
let expr_term = Grammar.Entry.create gram "expr_term";;

let add_uconn op co =
    EXTEND
      expr_term: LEVEL "Simple"
      [[ $op$; x = expr_term -> co Basictype.nc [x] ]];
    END
;;

let add_biconn lev op co =
    EXTEND
      expr_term: LEVEL $lev$
      [[ x = expr_term; $op$; y = expr_term -> co Basictype.nc [x;y] ]];
    END
;;

EXTEND
GLOBAL : expr_term;
  expr_term:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Simple" NONA
      [ x = LIDENT -> Atom(Basictype.nc,x)
      | "("; p = expr_term; ")" -> p
      ]
    ];

END

let buildParser table =
    List.iter(function
    |"Simple",op,co -> add_uconn op co
    |lev,op,co -> add_biconn lev op co
    ) table;
    fun s ->
        Grammar.Entry.parse expr_term (Stream.of_string s)
;;

