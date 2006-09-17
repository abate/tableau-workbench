(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Tablib
open ExtCommon

EXTEND
GLOBAL : numformula denformula expr_term patt_term;

  numformula: [[
       nc = numcond -> nc
  ]];

  numcond: [[
       "{"; t = patt_term; "}" -> Ast.Filter("__single",[Ast.Term t])
      |"("; t = patt_term; ")" -> Ast.Filter("__empty",[Ast.Term t])
      |t = patt_term -> Ast.Term t
  ]];
  
  denformula: [
      [v = test_variable; "@"; i = INT ->
          Ast.Term ( Ast.Variable (v, Ast.Int (int_of_string i)))
      |f = LIDENT; "("; l = LIST0 denformula SEP ","; ")" ->
              Ast.Apply(f,l) 
      |t = expr_term; sl = LIST0 simplification ->
              if sl = [] then Ast.Term t
              else Ast.Apply("__simpl",(Ast.Term t)::sl)
      ]
  ];

  simplification: [[
       "["; t = denformula; "]" -> Ast.Apply("__simplarg",[t])
  ]];
 
  expr_term:
    ["One" LEFTA [ ]
    |"Two" RIGHTA [ ]
    |"Zero" NONA
      [x = test_variable; "@"; i = INT ->
          Ast.Variable (x, Ast.Int (int_of_string i))
      |x = test_constant -> Ast.Const x
      |x = test_history -> Ast.History x
      |x = test_uid -> Ast.Atom x
      |x = LIDENT -> Ast.Var x
      |"("; p = expr_term; ")" -> p
      ] 
    ];

  patt_term:
    ["One" LEFTA [ ]
    |"Two" RIGHTA [ ]
    |"Zero" NONA
      [x = test_constant -> Ast.Const x 
      |x = test_uid -> Ast.Atom x
      |x = LIDENT -> Ast.Var x
      |"("; p = patt_term; ")" -> p
      ] 
    ];

END
