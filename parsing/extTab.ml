(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Tablib

EXTEND
GLOBAL: ExtCommon.den ExtCommon.num;

  ExtCommon.den: [
      [al = LIST1 denformula SEP ";" -> Ast.Denominator (Ast.Set al)
      |s = "Close" -> Ast.Status(s)
      |s = "Open" -> Ast.Status(s)
      |s = "Stop" -> Ast.Status(s)
      ]
  ];

  ExtCommon.num: [[ pl = LIST1 numformula SEP ";" -> Ast.Numerator (Ast.Set pl) ]];

  numformula: [[
       nc = numcond -> nc
  ]];

  numcond: [[
       "{"; t = rule_patt; "}" -> Ast.Filter("__single",[Ast.Term t])
      |"("; t = rule_patt; ")" -> Ast.Filter("__empty",[Ast.Term t])
      |t = rule_patt -> Ast.Term t
  ]];
  
  denformula: [
      [v = test_variable; "@"; i = INT ->
          Ast.Term ( Ast.Variable (v, Ast.Int (int_of_string i)))
      |f = LIDENT; "("; l = LIST0 args SEP ","; ")" ->
              Ast.Apply(f,l) 
      |t = rule_expr; sl = LIST0 simplification ->
              if sl = [] then Ast.Term t
              else Ast.Apply("__simpl",(Ast.Term t)::sl)
      ]
  ];

  args: [
      [f = denformula -> f
      |"["; l = LIST0 denformula SEP ";"; "]" -> Ast.List (l)
      |e = Pcaml.expr -> Ast.Term(Ast.Expr e)
      ]
  ];

  simplification: [[
       "["; t = denformula; "]" -> Ast.Apply("__simplarg",[t])
  ]];

  rule_expr: [
      [x = test_variable; "@"; i = INT ->
          Ast.Variable (x, Ast.Int (int_of_string i))
      |x = test_constant -> Ast.Const x
      |x = test_history -> Ast.History x
      |x = test_uid -> Ast.Atom x
      |x = LIDENT -> Ast.Var x
      |"("; p = rule_expr; ")" -> p
  ]];

  rule_patt: [
      [ x = test_constant -> Ast.Const x
      | x = test_uid -> Ast.Atom x
      | x = LIDENT -> Ast.Var x
      | "("; p = rule_patt; ")" -> p
  ]]; 
END
