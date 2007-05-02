(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Tablib

let source strm =
    match Stream.peek strm with
    |Some(_,"source") -> Stream.junk strm; "source"
    |_ -> raise Stream.Failure
let source = Grammar.Entry.of_parser Pcaml.gram "source" source

let mu strm =
    match Stream.peek strm with
    |Some(_,"mu") -> Stream.junk strm; "mu"
    |_ -> raise Stream.Failure
let mu = Grammar.Entry.of_parser Pcaml.gram "mu" mu

let all strm =
    match Stream.peek strm with
    |Some(_,"all") -> Stream.junk strm; "all"
    |_ -> raise Stream.Failure
let all = Grammar.Entry.of_parser Pcaml.gram "all" all

let last strm =
    match Stream.peek strm with
    |Some(_,"last") -> Stream.junk strm; "last"
    |_ -> raise Stream.Failure
let last = Grammar.Entry.of_parser Pcaml.gram "last" last

EXTEND
GLOBAL : Pcaml.str_item Pcaml.patt Pcaml.expr ExtGramm.num ExtGramm.denlist
ExtGramm.denseq ExtGramm.numseq ExtGramm.bladenseq ExtGramm.blanumseq;

  Pcaml.expr: LEVEL "simple" [
          [ "tactic"; "("; t = tactic; ")" -> expand_tactic t
  ]];

  Pcaml.str_item: [
      ["HISTORIES"; l = LIST1 history SEP ";"; "END" ->
          expand_histories (Ast.History l)
      |"VARIABLES"; l = LIST1 variable SEP ";"; "END" ->
          expand_histories (Ast.Variable l)
      |"TABLEAU"; l = LIST1 rule; "END" ->
              SyntaxChecker.check_tableau l;
              expand_tableau (Ast.Tableau l)
      |"SEQUENT"; l = LIST1 rule; "END" ->
              SyntaxChecker.check_tableau l;
              expand_tableau (Ast.Tableau l)
      |"STRATEGY"; OPT ":="; t = Pcaml.expr -> expand_strategy t
      |"MAIN" -> expand_main ()
      
      |"SIMPLIFICATION"; OPT ":="; e = Pcaml.expr -> expand_simplification e
      |"PP"; OPT ":="; e = Pcaml.expr -> expand_preproc e
      |"NEG"; OPT ":="; e = Pcaml.expr -> expand_negation e
      |"EXIT"; OPT ":="; f = userfunction -> expand_exit f 
      |"OPTIONS"; l = LIST1 options SEP ";"; "END" -> expand_options l
      |source; m = UIDENT -> expand_source m
  ]];

  history:  [[ name = UIDENT; (t,e) = def -> (name,t,e)]];
  variable: [[ name = LIDENT; (t,e) = def -> (name,t,e)]];
  def: [[ ":"; t = Pcaml.ctyp; ":="; e = Pcaml.expr LEVEL "simple" -> (t,e) ]];

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
      | t1 = tactic; "!"; t2 = tactic -> Ast.TaAltCut(t1,t2)
      | t1 = tactic; "|" ; t2 = tactic ->
              Ast.TaAlt(t1,t2,<:expr< tcond "Close" >>)
      | t1 = tactic; "||"; t2 = tactic ->
              Ast.TaAlt(t1,t2,<:expr< tcond "Open" >>)
      ]
  |
      [ "("; t = tactic; ")" -> t
(*      | "!"; t = tactic -> Ast.TaCut(t) *)
      | "Skip" -> Ast.TaSkip
      | "Fail" -> Ast.TaFail
      | mu; OPT "("; var = muvar; OPT ")"; "."; t = tactic -> Ast.TaMu(var,t)
      | "("; t = tactic; ")"; "*" ->
              let id = new_id "muvar" in
              Ast.TaMu(id,Ast.TaAltCut(Ast.TaSeq(t,Ast.TaMVar(id)),Ast.TaSkip))
(* Ast.TaMu(id,Ast.TaCut(Ast.TaAltCut(Ast.TaSeq(t,Ast.TaMVar(id)),Ast.TaSkip))) *)
      | m = UIDENT; "."; r = UIDENT -> Ast.TaModule(m,r)
      | id = test_muvar -> id
      ]
  ];

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
      [s = assign; ":="; f = assignfun -> Ast.Assign (s, f)
      |f = userfunction -> Ast.Function(f)
  ]];
  
  assign: [
      [s = test_history  -> Ast.ExHist s
      |s = test_variable -> Ast.ExVari(s, Ast.Null)
  ]];

  assignfun: [
      [f = funargs -> f
      |f = userfunction -> f
  ]];

  funargs: [
      [x = test_variable; e = varindex -> Ast.ExTerm(_loc,Ast.ExVari(x, e))
      |s = test_history  -> Ast.ExTerm(_loc,Ast.ExHist s)
   ]];

  userfunction: [
      [f  = LIDENT; "("; args = LIST0 assignfun SEP ","; ")" ->
              Ast.ExAppl(_loc,f, Ast.ExTupl(_loc,args))
      |t  = ExtGramm.formula_expr_schema -> Ast.ExTerm(_loc,t)
      |ex = ExtGramm.expr_expr_schema -> ex
      |ex = Pcaml.expr -> Ast.ExExpr(_loc,ex)
    ]];

  varindex: [[
       "@"; all -> Ast.All
      |"@"; last -> Ast.Last
      |"@"; i = INT -> Ast.Int(int_of_string i)
  ]];


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
          Ast.ExTerm (_loc, Ast.ExVari (v, Ast.Int (int_of_string i)))
      |v = test_history -> Ast.ExTerm(_loc, Ast.ExHist(v))
      |f = LIDENT; "("; l = LIST0 args SEP ","; ")" ->
              Ast.ExAppl(_loc, f,Ast.ExTupl(_loc,l))
      |t = ExtGramm.expr_expr_schema; sl = LIST0 simplification ->
              if sl = [] then t
              else Ast.ExAppl(_loc, "__simpl",Ast.ExTupl(_loc,t::sl))
      ]
  ];

  args: [
      [f = denformula -> f
      |"["; l = LIST0 denformula SEP ";"; "]" -> Ast.ExTupl(_loc,l)
      |e = Pcaml.expr -> Ast.ExExpr(_loc, e)
      ]
  ];

  simplification: [[
       "["; t = denformula; "]" -> Ast.ExAppl(_loc,"__simplarg",t)
  ]];

END
