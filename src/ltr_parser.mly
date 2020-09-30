%{
    open Ltr
%}

%token EOF
%token <string> STR
%token <string> NAME
%token <int> NUM
%token MOD
%token GRAMMARASSIGN
%token WILDCARD
%token TURNSTYLE
%token SUBTYPE
%token STEP
%token MID
%token COMMA
%token CONS
%token COLON
%token DOT
%token TICK
%token EXCL
%token CARET
%token SEMI
%token DASH
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE RBRACE LANGLE RANGLE
%token FSLASH
%token MAPSTO
%token EQ
%token QMEMBER QNOTHING QSOMETHING QEMPTY QVAR QSTR QCONSTRUCTOR QBINDING QSUBST QLIST QMAP QTUPLE QVARKIND QOPKIND QSYNTAX
%token FRESHVAR SUBSTITUTE VAROVERLAP NTH HEAD TAIL LAST DIFF ASSOC APPEND REV DEDUP CONCAT VARS UNBIND BOUND NOTHING SOMETHING GET IF THEN ELSE LET REC UPPERCASE LOWERCASE INTSTR SELF UNIQUIFY REMOVESYNTAX METAVAR SYNTAX RULENAME PREMISES CONCLUSION RULES ADDRULE SETRULES HINT AND OR
%token NIL DOM RANGE MEMBER NOT UNION MAPUNION SUBSET ZIP FRESH
%token LAN RULE FORMULA TERM STRING BOOL INT TUPLE OPTION LIST
%token TRUE FALSE

%start ltr
%type <Ltr.Exp.t> ltr

%%

ltr:
  | exp EOF { $1 }

exp:
  | SELF
    { Exp.Self }
  | NAME
    { Exp.Var $1 }
  | STR
    { Exp.Str $1 }
  | exp CARET exp
    { Exp.Str_concat ($1, $3) }
  | UPPERCASE LPAREN exp RPAREN
    { Exp.Uppercase $3 }
  | LOWERCASE LPAREN exp RPAREN
    { Exp.Lowercase $3 }
  | NUM
    { Exp.Int $1 }
  | INTSTR LPAREN exp RPAREN
    { Exp.Int_str $3 }
  | TRUE
    { Exp.Bool true }
  | FALSE
    { Exp.Bool false }
  | boolean
    { Exp.Bool_exp $1 }

boolean:
  | NOT LPAREN boolean RPAREN
    { Exp.Not $3 }
  | AND LPAREN boolean COMMA boolean RPAREN
    { Exp.And ($3, $5) }
  | OR LPAREN boolean COMMA boolean RPAREN
    { Exp.And ($3, $5) }
  | exp EQ exp
    { Exp.Eq ($1, $3) }
  | NAME
    { Exp.Var_bool $1 }
  | QMEMBER LPAREN exp COMMA exp RPAREN
    { Exp.Is_member ($3, $5) }
  | QNOTHING LPAREN exp RPAREN
    { Exp.Is_nothing $3 }
  | QSOMETHING LPAREN exp RPAREN
    { Exp.Is_something $3 }
  | QEMPTY LPAREN exp RPAREN
    { Exp.Is_empty $3 }
  | QVAR LPAREN exp RPAREN
    { Exp.Is_var $3 }
  | QSTR LPAREN exp RPAREN
    { Exp.Is_str $3 }
  | QCONSTRUCTOR LPAREN exp RPAREN
    { Exp.Is_constructor $3 }
  | QBINDING LPAREN exp RPAREN
    { Exp.Is_binding $3 }
  | QSUBST LPAREN exp RPAREN
    { Exp.Is_subst $3 }
  | QLIST LPAREN exp RPAREN
    { Exp.Is_list $3 }
  | QMAP LPAREN exp RPAREN
    { Exp.Is_map $3 }
  | QTUPLE LPAREN exp RPAREN
    { Exp.Is_tuple $3 }
  | QVARKIND LPAREN exp COMMA name = STR RPAREN
    {
      let open Core_kernel in
      if String.(equal name (capitalize name)) then
        Exp.Is_var_kind ($3, name)
      else
        invalid_arg
          (Printf.sprintf
             "invalid category name %s, must be capitalized"
             name)
    }
  | QOPKIND LPAREN exp COMMA name = STR RPAREN
    {
      let open Core_kernel in
      if String.(equal name (capitalize name)) then
        Exp.Is_op_kind ($3, name)
      else
        invalid_arg
          (Printf.sprintf
             "invalid category name %s, must be capitalized"
             name)
    }
  | QSYNTAX LPAREN name = STR RPAREN
    {
      let open Core_kernel in
      if String.(equal name (capitalize name)) then
        Exp.Has_syntax name
      else
        invalid_arg
          (Printf.sprintf
             "invalid category name %s, must be capitalized"
             name)
    }
