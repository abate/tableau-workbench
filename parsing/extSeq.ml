(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Tablib

EXTEND
GLOBAL: 
ExtGramm.num ExtGramm.denlist
ExtGramm.denseq ExtGramm.numseq 
ExtGramm.bladenseq ExtGramm.blanumseq;


  ExtGramm.denlist: [[
       d = den; "|";  dl = den_forall -> ((d::dl),Ast.ForAll)
      |d = den; "||"; dl = den_exists -> ((d::dl),Ast.Exists)
      |d = den; "|||"; dl = den_exists -> ((d::dl),Ast.User)
      |d = den -> ([d],Ast.Linear)
  ]];

  den_forall: [[ dl = LIST1 den SEP "|" -> dl ]];
  den_exists: [[ dl = LIST1 den SEP "||" -> dl ]];

  den: [
      [d = ExtGramm.bladenseq -> Ast.Denominator d
      |s = "Close" -> Ast.Status(s)
      |s = "Open"  -> Ast.Status(s)
      |s = "Stop"  -> Ast.Status(s)
      ]
  ];
  ExtGramm.num: [[ d = ExtGramm.blanumseq -> Ast.Numerator d ]];

  ExtGramm.denseq: [[ d = LIST0 denformula SEP ";" -> d ]];
  ExtGramm.numseq: [[ d = LIST0 numformula SEP ";" -> d ]];
  
  numformula: [
      [ "{"; t = ExtGramm.expr_patt_schema; "}" -> (Ast.Single,t)
      | "("; t = ExtGramm.expr_patt_schema; ")" -> (Ast.Empty,t)
      | t = ExtGramm.expr_patt_schema -> (Ast.Set,t)
      ]
  ];
  
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
