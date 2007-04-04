(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Tablib

EXTEND
GLOBAL: ExtCommon.den ExtCommon.num ;

  ExtCommon.den: [
      [d = LIST1 denseq SEP "=>" -> Ast.Denominator (Array.of_list d)
      |s = "Close" -> Ast.Status(s)
      |s = "Open"  -> Ast.Status(s)
      |s = "Stop"  -> Ast.Status(s)
      ]
  ];

  ExtCommon.num: [[ d = LIST1 numseq SEP "=>" -> Ast.Numerator (Array.of_list d) ]];

  denseq: [[ d = LIST1 denformula SEP ";" -> d ]];
  numseq: [[ d = LIST1 numformula SEP ";" -> d ]];
  
  numformula: [
      [ "{"; t = ExtGramm.expr_patt_schema; "}" -> (Ast.Single,t)
      | "("; t = ExtGramm.expr_patt_schema; ")" -> (Ast.Empty,t)
      | t = ExtGramm.expr_patt_schema -> (Ast.Set,t)
  ]];
  
  denformula: [
      [v = test_variable; "@"; i = INT ->
          Ast.ExTerm ( Ast.ExVari (v, Ast.Int (int_of_string i)))
      |v = test_history -> Ast.ExTerm(Ast.ExHist(v))
      |f = LIDENT; "("; l = LIST0 args SEP ","; ")" ->
              Ast.ExAppl(f,Ast.ExTupl(l))
      |t = ExtGramm.expr_expr_schema; sl = LIST0 simplification ->
              if sl = [] then t
              else Ast.ExAppl("__simpl",Ast.ExTupl(t::sl))
      ]
  ];

  args: [
      [f = denformula -> f
      |"["; l = LIST0 denformula SEP ";"; "]" -> Ast.ExTupl(l)
      |e = Pcaml.expr -> Ast.ExExpr(e)
      ]
  ];

  simplification: [[
       "["; t = denformula; "]" -> Ast.ExAppl("__simplarg",t)
  ]];

END
