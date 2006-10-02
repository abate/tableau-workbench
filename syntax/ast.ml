
type connectives = connective list
and connective = Connective of (string * string * string)
type histories = Histories of history list
and history =
    |VDecl of (string * histtype * MLast.expr * MLast.expr option) 
    |HDecl of (string * histtype * MLast.expr * MLast.expr option)
and histtype =
    |Container of string * histtype list
    |Type of string

type strategy = Strategy of tactic
and tactic =
    |Basic of string
    |Seq of tactic * tactic
    |Alt of tactic * tactic
    |Repeat of tactic
    |TVar of string

type options = Options of (string * MLast.expr * string )

type tableau = Tableau of rule list
and rule = Rule of
    (string *
    ruletype *
    numerator *
    (denominator list * condition) *
    condition list *
    action list list *
    condition list list *
    backtrack list *
    bool option)
and ruletype    = Invertible | NotInvertible
and numerator   = Numerator of expression list
and denominator =
    |Denominator of expression list
    |Status of string
and expression  =
    |Apply    of string * expression list
    |Filter   of string * expression list
    |Term     of term
    |List     of expression list
and term =
    |Bicon of string * term * term
    |Ucon  of string * term
    |Const of string
    |Atom  of string
    |FAtom  of string * MLast.expr
    |Var   of string
    |History  of string
    |Variable of (string * varindex)
    |Expr of MLast.expr
and varindex  = Int of int | All | Last | Null
and condition = CCondition of expression
and action    =
    |AAssign of term * expression
    |AFunction of expression
and backtrack = action


