(*pp camlp4o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Ast2code

Grammar.error_verbose := true ;;
let patt_term = Grammar.Entry.create Pcaml.gram "patt_term";;
let expr_term = Grammar.Entry.create Pcaml.gram "expr_term";;
let rewrite_patt = Grammar.Entry.create Pcaml.gram "rewrite_patt";;
let rewrite_expr = Grammar.Entry.create Pcaml.gram "rewrite_expr";;


(* extend the parser with tokens declared in the 
 * CONNECTIVES section. binary connectives *)
let add_biconn lev op co =
    EXTEND
      patt_term: LEVEL $lev$
        [[ x= patt_term; $op$; y = patt_term ->
            Ast.Bicon(co,x,y) ]];
      expr_term: LEVEL $lev$
        [[ x = expr_term; $op$; y = expr_term -> Ast.Bicon(co,x,y) ]];
      rewrite_expr: LEVEL $lev$
        [[ x = rewrite_expr; $op$; y = rewrite_expr -> Ast.Bicon(co,x,y) ]];
      rewrite_patt: LEVEL $lev$
        [[ x = rewrite_patt; $op$; y = rewrite_patt -> Ast.Bicon(co,x,y) ]];
    END
;;

(* extend the parser with the tokens declared in the 
 * CONNECTIVES part. unary connectives connectives *)
let add_uconn lev op co =
    EXTEND
      patt_term: LEVEL $lev$
        [[ $op$; x = patt_term -> Ast.Ucon(co,x) ]];
      expr_term: LEVEL $lev$
        [[ $op$; x = expr_term -> Ast.Ucon(co,x) ]];
      rewrite_expr: LEVEL $lev$
        [[ $op$; x = rewrite_expr -> Ast.Ucon(co,x) ]];
      rewrite_patt: LEVEL $lev$
        [[ $op$; x = rewrite_patt -> Ast.Ucon(co,x) ]];
    END
;;

EXTEND
GLOBAL : Pcaml.str_item Pcaml.patt Pcaml.expr patt_term expr_term
rewrite_expr rewrite_patt;

  Pcaml.expr: LEVEL "simple"
      [
          ["tactic"; "("; t = tactic; ")" -> expand_tactic _loc t
          |"term";  "("; e = rewrite_expr_term; ")" -> expand_rewrite_expr _loc e
  ]];

  Pcaml.patt: LEVEL "simple"
      [[ "term"; "("; p = rewrite_patt_term; ")"-> expand_rewrite_patt _loc p
  ]];

  Pcaml.str_item: [[
      "CONNECTIVES"; clist = LIST1 connective SEP ";"; "END" ->
         List.iter (function
              |Ast.Connective(v,s,l) when s =~ bi_re -> add_biconn l (get_match 1 s) v
              |Ast.Connective(v,s,l) when s =~ u_re -> add_uconn l (get_match 1 s) v
              |Ast.Connective(v,"Const",_) -> Hashtbl.replace const_table v ()
              |Ast.Connective(_,s,_) -> failwith (s^" is not a valid pattern")
          ) clist ;
          expand_connectives _loc clist
      |"HISTORIES"; hlist = LIST1 [ "("; h = history; ")" -> h ] SEP ";"; "END" ->
              expand_histories _loc (Ast.Histories hlist)
      |"TABLEAU"; l = LIST1 rule; "END" ->
              expand_tableau _loc (Ast.Tableau l)
      |"STRATEGY"; OPT ":="; t = tactic ->
              expand_strategy _loc (Ast.Strategy t)
      
      |"SIMPLIFICATION"; OPT ":="; e = Pcaml.expr -> expand_simplification _loc e
      |"PP"; OPT ":="; e = Pcaml.expr -> expand_preproc _loc e
      |"NEG"; OPT ":="; e = Pcaml.expr -> expand_negation _loc e
      |"EXIT"; OPT ":="; f = userfunction -> expand_exit _loc f
      |"OPTIONS"; olist = LIST1 options SEP ";"; "END" ->
              expand_options _loc olist
  ]];

  options : [[
      OPT "(";
        s = STRING ; ",";
        e = Pcaml.expr LEVEL "simple"; ",";
        a = STRING; OPT ")" -> Ast.Options (s,e,a)
  ]];

(*  
  connective: [[
      t = Mlast.cf_type; "//"; s = STRING; "//" -> (t,s) 
  ]];
*)

  tactic:
  [ "One" LEFTA
      [ id = LIDENT -> Ast.TVar(id)
      | t1 = tactic; ";"; t2 = tactic -> Ast.Seq(t1,t2)
      | t1 = tactic; "|"; t2 = tactic -> Ast.Alt(t1,t2)
      ]
  |
      [ "("; t = tactic; ")" -> t
      | "("; t = tactic; ")"; "*" -> Ast.Repeat(t)
      | id = UIDENT -> Ast.Basic(id)
      ]
  ];

  connective: [[ 
       v = UIDENT; ","; s = STRING; ","; r = UIDENT -> Ast.Connective (v,s,r)
      |v = UIDENT; ","; "Const" -> Ast.Connective (v,"Const","")
  ]];

  history: [
      [v = UIDENT; ":"; t = hist_type ; ":="; m = container; d = OPT default ->
          Ast.HDecl(v,t,m,d)
      |v = LIDENT; ":"; t = hist_type ; ":="; m = container; d = OPT default ->
          Ast.VDecl(v,t,m,d)
  ]];

  default: [[
      "default"; e = Pcaml.expr LEVEL "simple"-> e
  ]];

  container: [[
      e = Pcaml.expr LEVEL "simple" -> <:expr< $e$ >>
  ]];

  hist_type: [
      [tid = UIDENT; "of"; OPT "("; tl = LIST1 hist_type SEP "*"; OPT ")" ->
          Ast.Container(tid,tl)
      |t = UIDENT -> Ast.Type(t)
  ]];

  rule: [[
      "RULE";
      id = UIDENT;
      n = num;
      t = test_sep;
      dl = denlist; 
      cl = OPT condition;
      hl = OPT actionlist;
      bl = OPT branchlist; 
      bt = OPT backtracklist;
      "END" ->
          Ast.Rule (id,t,n,dl,
                    Option.optlist cl,
                    Option.optlist hl,
                    Option.optlist bl,
                    Option.optlist bt)
  ]];

  condition: [[
      "COND"; OPT "["; l = LIST1 userfunction SEP ";"; OPT "]" ->
          List.map (fun c -> Ast.CCondition c ) l
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
          List.map (fun c -> Ast.CCondition c ) l
  ]];

  action: [[
      OPT "["; l = LIST0 useract SEP ";"; OPT "]" -> l
  ]];
  
  useract: [[
       s = assign; ":="; f = userfunction -> Ast.AAssign (s, f)
  ]];
  
  assign: [[
     s = test_history  -> Ast.History s
    |s = test_variable -> Ast.Variable(s, Ast.Null)
  ]];

  userfunction: [[
       x = test_variable; e = varindex ->
           Ast.Term(Ast.Variable(x, e))
      |f = LIDENT; "("; args = LIST0 userfunction SEP ","; ")" ->
              Ast.Apply(f, args)
      |ex = expr_term -> Ast.Term (ex)
      |ex = Pcaml.expr -> Ast.Term(Ast.Expr ex) 

  ]];

  varindex: [[
       "@"; "all" -> Ast.All
      |"@"; "last" -> Ast.Last
      |"@"; i = INT -> Ast.Int(int_of_string i)
  ]];

  denlist: [[
       d = den; "|";  dl = den_forall ->
           ((d::dl),Ast.CCondition(Ast.Apply("forall",[])))
      |d = den; "||"; dl = den_exists ->
              ((d::dl),Ast.CCondition(Ast.Apply("exists",[])))
      |d = den; "|||"; dl = den_exists ->
              ((d::dl),Ast.CCondition(Ast.Apply("user",[])))
      |d = den -> ([d],Ast.CCondition(Ast.Apply("linear",[])))
  ]];

  den_forall: [[ dl = LIST1 den SEP "|" -> dl ]];
  den_exists: [[ dl = LIST1 den SEP "||" -> dl ]];
  
  den: [
      [al = LIST1 denformula SEP ";" -> Ast.Denominator al
      |s = "Close" -> Ast.Status(s)
      |s = "Open" -> Ast.Status(s)
      |s = "Stop" -> Ast.Status(s) 
      ]
  ];

  num: [[ pl = LIST1 numformula SEP ";" -> Ast.Numerator pl ]]; 
  
  numformula: [[
       nc = numcond -> nc
(*      |c = LIDENT; "("; p = LIST0 numcond SEP ","; ")" -> Ast.Filter(c,p)  *)
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
(*          Ast.Apply(f,List.map (fun t -> Ast.Term t) l) *)
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

  rewrite_expr_term: [
      [x = LIDENT; "{"; t = rewrite_expr_term; "/"; s = rewrite_expr_term; "}" ->
              Ast.Apply("__substitute",[Ast.Term(Ast.Var x);t;s])
      |t = rewrite_expr -> Ast.Term(t)
    ]];

  rewrite_patt_term: [
      [t = rewrite_patt -> Ast.Term(t)]
  ];

  rewrite_expr: 
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Zero" NONA
      ["["; e = Pcaml.expr LEVEL "simple"; "]" -> Ast.Expr e
      |x = test_constant -> Ast.Const x
      |x = test_uid -> Ast.Atom x
      |x = LIDENT; "("; e = Pcaml.expr; ")" -> Ast.FAtom(x,e)
      |x = LIDENT -> Ast.Var x
      |"("; p = rewrite_expr; ")" -> p
      ] 
  ];

  rewrite_patt:
    [ "One" LEFTA [ ]
    | "Two" RIGHTA [ ]
    | "Zero" NONA
      ["Constant" -> Ast.Const ""
      |"Atom" -> Ast.Atom ""
      |x = test_constant -> Ast.Const x
      |x = test_uid -> Ast.Atom x
      |x = LIDENT -> Ast.Var x
      |"("; p = rewrite_patt; ")" -> p
      ]
    ];

END
