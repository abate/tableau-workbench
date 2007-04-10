(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Tablib

EXTEND
GLOBAL : Pcaml.str_item Pcaml.patt Pcaml.expr;

  Pcaml.expr: LEVEL "simple" [
          [ "tactic"; "("; t = tactic; ")" -> expand_tactic t
  ]];

  Pcaml.str_item: [
      ["HISTORIES"; l = LIST1 [ "("; h = history; ")" -> h ] SEP ";"; "END" ->
          expand_histories (Ast.History l)

      |"VARIABLES"; l = LIST1 [ "("; h = variable; ")" -> h ] SEP ";"; "END" ->
          expand_histories (Ast.Variable l)

      |"TABLEAU"; l = LIST1 rule; "END" -> expand_tableau (Ast.Tableau l)
      |"SEQUENT"; l = LIST1 rule; "END" -> expand_tableau (Ast.Tableau l)
      |"STRATEGY"; OPT ":="; t = Pcaml.expr -> expand_strategy t
      |"MAIN" -> expand_main ()
      
      |"SIMPLIFICATION"; OPT ":="; e = Pcaml.expr -> expand_simplification e
      |"PP"; OPT ":="; e = Pcaml.expr -> expand_preproc e
      |"NEG"; OPT ":="; e = Pcaml.expr -> expand_negation e
      |"EXIT"; OPT ":="; f = userfunction -> expand_exit f 
      |"OPTIONS"; l = LIST1 options SEP ";"; "END" -> expand_options l
      |"source"; m = UIDENT -> expand_source m
  ]];

  options : [[
      OPT "(";
        s = STRING ; ",";
        e = Pcaml.expr LEVEL "simple"; ",";
        a = STRING; OPT ")" -> Ast.Options (s,e,a)
  ]];

  tactic:
  [ "One" LEFTA
      [ id = LIDENT -> Ast.TaVar(id)
      | t1 = tactic; ";"; t2 = tactic -> Ast.TaSeq(t1,t2)
      | t1 = tactic; "|"; t2 = tactic -> Ast.TaAlt(t1,t2)
      ]
  |
      [ "("; t = tactic; ")" -> t
      | "!"; t = tactic -> Ast.TaCut(t)
      | "Skip" -> Ast.TaSkip
      | "Fail" -> Ast.TaFail
      | "mu"; OPT "("; var = muvar; OPT ")"; "."; t = tactic -> Ast.TaMu(var,t)
      | "("; t = tactic; ")"; "*" ->
              let id = new_id "muvar" in
              Ast.TaMu(id,Ast.TaCut(Ast.TaAlt(Ast.TaSeq(t,Ast.TaMVar(id)),Ast.TaSkip)))
      | m = UIDENT; "."; r = UIDENT -> Ast.TaModule(m,r)
      | id = test_muvar -> id
      ]
  ];

  history: [[
      v = UIDENT; ":"; m = Pcaml.ctyp; ":="; d = Pcaml.expr LEVEL "simple" -> (v,m,d)
  ]];

  variable: [[
      v = LIDENT; ":"; m = Pcaml.ctyp; ":="; d = Pcaml.expr LEVEL "simple" -> (v,m,d)
  ]];

  rule: [[
      "RULE";
      id = UIDENT;
      (n,t,dl) = ExtGramm.node;
      cl = OPT condition;
      hl = OPT actionlist;
      bl = OPT branchlist; 
      bt = OPT backtracklist;
      he = OPT [ "HEURISTIC"; ":="; f = Pcaml.expr -> f ];
      ca = OPT [ "CACHE";     ":="; c = Pcaml.expr -> c ]; 
      "END" ->
          Ast.Rule (id,t,n,dl,
                    Option.optlist cl,
                    Option.optlist hl,
                    Option.optlist bl,
                    Option.optlist bt,
                    ca, he)
  ]];

  condition: [[
      "COND"; OPT "["; l = LIST1 userfunction SEP ";"; OPT "]" ->
          List.map (fun c -> Ast.Condition c ) l
  ]];

  actionlist: [[
      "ACTION"; OPT "["; l = LIST1 action SEP ";"; OPT "]" -> l
  ]];

  branchlist: [[
      "BRANCH"; OPT "["; l = LIST1 branch SEP ";"; OPT "]" -> l
  ]];

  backtracklist: [[
      "BACKTRACK"; OPT "["; l = LIST1 useract SEP ";"; OPT "]" -> l
  ]];

  branch: [[
      OPT "["; l = LIST0 userfunction SEP ";"; OPT "]" ->
          List.map (fun c -> Ast.Condition c ) l
  ]];

  action: [[
      OPT "["; l = LIST0 useract SEP ";"; OPT "]" -> l
  ]];
  
  useract: [
      [s = assign; ":="; f = userfunction -> Ast.Assign (s, f)
      |f = userfunction -> Ast.Function(f)
  ]];
  
  assign: [
      [s = test_history  -> Ast.ExHist s
      |s = test_variable -> Ast.ExVari(s, Ast.Null)
  ]];

  userfunction: [
      [x = test_variable; e = varindex -> Ast.ExTerm(Ast.ExVari(x, e))
      |s = test_history  -> Ast.ExTerm(Ast.ExHist s)
      |f = LIDENT; "("; args = LIST0 userfunction SEP ","; ")" ->
              Ast.ExAppl(f, Ast.ExTupl(args))
      |ex = ExtGramm.expr_expr_schema -> ex
      |t  = ExtGramm.formula_expr_schema -> Ast.ExTerm(t)
      |ex = Pcaml.expr -> Ast.ExExpr(ex)
  ]];

  varindex: [[
       "@"; "all" -> Ast.All
      |"@"; "last" -> Ast.Last
      |"@"; i = INT -> Ast.Int(int_of_string i)
  ]];

END
