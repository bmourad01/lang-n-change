%{
    open Ltr
%}

%token EOF
%token <string> STR
%token <string> CAPNAME
%token <string> NAME
%token <string> ANYNAME
%token <int> NUM
%token MOD
%token HASH
%token DOLLAR
%token AT
%token AMPERSAND
%token GRAMMARASSIGN
%token TURNSTYLE
%token SUBTYPE
%token STEP
%token ARROW
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
%token FRESHVAR SUBSTITUTE VAROVERLAP NTH HEAD TAIL LAST DIFF ASSOC APPEND REV DEDUP CONCAT VARS UNBIND BOUND NOTHING SOMETHING GET IF THEN ELSE LET REC IN UPPERCASE LOWERCASE INTSTR SELF UNIQUIFY REMOVESYNTAX METAVAR SYNTAX RULENAME PREMISES CONCLUSION RULES ADDRULE SETRULES HINT AND OR
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
  | boolean
    { Exp.Bool_exp $1 }
  | LET REC name = NAME args = list(let_arg) COLON rec_type = typ EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = Some rec_type;
          name;
          args;
          exp;
          body;
        }
    }
  | LET name = NAME args = list(let_arg)EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = None;
          name;
          args = [];
          exp;
          body;
        }
    }
  | exp LPAREN separated_nonempty_list(COMMA, exp) RPAREN
    { Exp.Apply ($1, $3) }
  | IF exp THEN exp ELSE exp
    { Exp.Ite ($2, $4, $6) }
  | exp SEMI exp
    { Exp.Seq ($1, $3) }
  | field = exp LSQUARE pattern = exp RSQUARE COLON LBRACE body = exp RBRACE
    { Exp.Select {keep = false; field; pattern; body} }
  | field = exp EXCL LSQUARE pattern = exp RSQUARE COLON LBRACE body = exp RBRACE
    { Exp.Select {keep = true; field; pattern; body} }
  | LPAREN exp COMMA exp RPAREN
    { Exp.Tuple [$2; $4] }
  | LPAREN exp COMMA exp COMMA separated_nonempty_list(COMMA, exp) RPAREN
    { Exp.Tuple ($2 :: $4 :: $6) }
  | LSQUARE separated_list(COMMA, exp) RSQUARE
    { Exp.List $2 }
  | HEAD LPAREN exp RPAREN
    { Exp.Head $3 }
  | TAIL LPAREN exp RPAREN
    { Exp.Tail $3 }
  | LAST LPAREN exp RPAREN
    { Exp.Last $3 }
  | NTH LPAREN exp COMMA exp RPAREN
    { Exp.Nth ($3, $5) }
  | CONCAT LPAREN exp RPAREN
    { Exp.List_concat $3 }
  | REV LPAREN exp RPAREN
    { Exp.Rev $3 }
  | DEDUP LPAREN exp RPAREN
    { Exp.Dedup $3 }
  | APPEND LPAREN exp COMMA exp RPAREN
    { Exp.Append ($3, $5) }
  | exp AT exp
    { Exp.Append ($1, $3) }
  | DIFF LPAREN exp COMMA exp RPAREN
    { Exp.Diff ($3, $5) }
  | ZIP LPAREN exp COMMA exp RPAREN
    { Exp.Zip ($3, $5) }
  | ASSOC LPAREN exp COMMA exp RPAREN
    { Exp.Assoc ($3, $5) }
  | NOTHING
    { Exp.Nothing }
  | SOMETHING LPAREN exp RPAREN
    { Exp.Something $3 }
  | GET LPAREN exp RPAREN
    { Exp.Option_get $3 }
  | term
    { Exp.New_term $1 }
  | VARS LPAREN exp RPAREN
    { Exp.Vars_of $3 }
  | FRESHVAR LPAREN NAME RPAREN
    { Exp.Fresh_var $3 }
  | UNBIND LPAREN exp RPAREN
    { Exp.Unbind $3 }
  | BOUND LPAREN exp RPAREN
    { Exp.Bound_of $3 }
  | SUBSTITUTE LPAREN exp COMMA exp RPAREN
    { Exp.Substitute ($3, $5) }
  | VAROVERLAP LPAREN exp COMMA exp RPAREN
    { Exp.Var_overlap ($3, $5) }
  | exp TICK
    { Exp.Ticked $1 }
  | exp TICK MID exp
    { Exp.Ticked_restricted ($1, $4) }
  | name = CAPNAME meta_var = ANYNAME GRAMMARASSIGN DOT DOT DOT MID terms = separated_nonempty_list(MID, exp)
    {
      Exp.New_syntax {
          extend = true;
          name;
          meta_var;
          terms;
        }
    }
  | name = CAPNAME meta_var = ANYNAME GRAMMARASSIGN terms = separated_nonempty_list(MID, exp)
    {
      Exp.New_syntax {
          extend = false;
          name;
          meta_var;
          terms;
        }
    }
  | REMOVESYNTAX LPAREN name = CAPNAME RPAREN
    { Exp.Remove_syntax name }
  | METAVAR LPAREN name = CAPNAME RPAREN
    { Exp.Meta_var_of name }
  | SYNTAX LPAREN name = CAPNAME RPAREN
    { Exp.Syntax_terms_of name }
  | MOD relation
    { $2 }
  | formula
    { Exp.New_formula $1 }
  | UNIQUIFY LPAREN formulae = exp COMMA hint_map = exp COMMA hint_var = STR RPAREN
    { Exp.Uniquify_formulae {formulae; hint_map; hint_var} }
  | LSQUARE name = exp RSQUARE LBRACE premises = separated_list(COMMA, exp) nonempty_list(DASH) conclusion = exp RBRACE
    { Exp.New_rule {name; premises; conclusion} }
  | RULENAME LPAREN exp RPAREN
    { Exp.Rule_name $3 }
  | PREMISES LPAREN exp RPAREN
    { Exp.Rule_premises $3 }
  | CONCLUSION LPAREN exp RPAREN
    { Exp.Rule_conclusion $3 }
  | RULES
    { Exp.Rules_of }
  | ADDRULE LPAREN exp RPAREN
    { Exp.Add_rule $3 }
  | SETRULES LPAREN exp RPAREN
    { Exp.Set_rules $3 }
  | HASH name = NAME COLON DOT DOT DOT MID elements = separated_nonempty_list(MID, hint_element)
    {
      Exp.New_hint {
          extend = true;
          name;
          elements;
        }
    }
  | HASH name = NAME COLON elements = separated_nonempty_list(MID, hint_element)
    {
      Exp.New_hint {
          extend = true;
          name;
          elements;
        }
    }
  | HINT LPAREN STR RPAREN
    { Exp.Lookup_hint $3 }

typ:
  | LAN
    { Type.Lan }
  | SYNTAX
    { Type.Syntax }
  | RULE
    { Type.Rule }
  | FORMULA
    { Type.Formula }
  | TERM
    { Type.Term }
  | STRING
    { Type.String }
  | BOOL
    { Type.Bool }
  | INT
    { Type.Int }
  | LPAREN typ COMMA typ RPAREN TUPLE
    { Type.Tuple [$2; $4] }
  | LPAREN typ COMMA typ COMMA separated_nonempty_list(COMMA, typ) RPAREN TUPLE
    { Type.Tuple ($2 :: $4 :: $6) }
  | typ OPTION
    { Type.Option $1 }
  | typ LIST
    { Type.List $1 }
  | LPAREN typ ARROW typ RPAREN
    { Type.Arrow [$2; $4] }
  | LPAREN typ ARROW typ ARROW separated_nonempty_list(ARROW, typ) RPAREN
    { Type.Arrow ($2 :: $4 :: $6) }

let_arg:
  | LPAREN name = NAME COLON typ RPAREN
    { (name, $4) }

hint_element:
  | NAME MAPSTO nonempty_list(NAME)
    { ($1, $3) }
  | NAME
    { ($1, []) }

sugared_relation:
  | exp TURNSTYLE exp COLON exp
    { Exp.New_relation (Language.Predicate.Builtin.typeof, [$1; $3; $5]) }
  | exp STEP exp
    { Exp.New_relation (Language.Predicate.Builtin.step, [$1; $3]) }
  | exp SUBTYPE exp
    { Exp.New_relation (Language.Predicate.Builtin.subtype, [$1; $3]) }
  | exp TURNSTYLE exp SUBTYPE exp
    { Exp.New_relation (Language.Predicate.Builtin.subtype, [$1; $3; $5]) }

relation:
  | sugared_relation
    { $1 }
  | NAME nonempty_list(exp)
    { Exp.New_relation ($1, $2) }

boolean:
  | TRUE
    { Exp.Bool true }
  | FALSE
    { Exp.Bool false }
  | NOT LPAREN exp RPAREN
    { Exp.Not $3 }
  | AND LPAREN exp COMMA exp RPAREN
    { Exp.And ($3, $5) }
  | OR LPAREN exp COMMA exp RPAREN
    { Exp.And ($3, $5) }
  | exp EQ exp
    { Exp.Eq ($1, $3) }
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
  | QVARKIND LPAREN exp COMMA name = CAPNAME RPAREN
    { Exp.Is_var_kind ($3, name) }
  | QOPKIND LPAREN exp COMMA name = CAPNAME RPAREN
    { Exp.Is_op_kind ($3, name) }
  | QSYNTAX LPAREN name = CAPNAME RPAREN
    { Exp.Has_syntax name }

subst:
  | exp FSLASH NAME
    { Exp.Subst_pair ($1, $3) }
  | NAME COLON k = CAPNAME
    { Exp.Subst_var ($1, k) }

term:
  | DOLLAR NIL
    { Exp.Term_nil }
  | DOLLAR ANYNAME
    { Exp.Term_var $2 }
  | DOLLAR STR
    { Exp.Term_str $2 }
  | LPAREN exp exp RPAREN
    { Exp.Term_constructor ($2, $3) }
  | LPAREN exp RPAREN exp
    { Exp.Term_binding ($2, $4) }
  | exp LSQUARE separated_nonempty_list(COMMA, subst) RSQUARE
    { Exp.Term_subst ($1, $3) }
  | LSQUARE exp MAPSTO exp RSQUARE exp
    { Exp.Term_map_update ($2, $4, $6) }
  | DOLLAR DOM LPAREN exp RPAREN
    { Exp.Term_map_domain $4 }
  | DOLLAR RANGE LPAREN exp RPAREN
    { Exp.Term_map_range $4 }
  | LPAREN exp CONS exp RPAREN
    { Exp.Term_cons ($2, $4) }
  | LSQUARE exp DOT DOT DOT RSQUARE
    { Exp.Term_list $2 }
  | LBRACE NAME MAPSTO exp RBRACE
    { Exp.Term_map ($2, $4) }
  | LANGLE exp COMMA exp RANGLE
    { Exp.Term_tuple [$2; $4] }
  | LANGLE exp COMMA exp COMMA separated_nonempty_list(COMMA, exp) RANGLE
    { Exp.Term_tuple ($2 :: $4 :: $6) }
  | DOLLAR UNION LPAREN separated_nonempty_list(COMMA, exp) RPAREN
    { Exp.Term_union $4 }
  | DOLLAR MAPUNION LPAREN separated_nonempty_list(COMMA, exp) RPAREN
    { Exp.Term_map_union $4 }
  | DOLLAR ZIP LPAREN exp COMMA exp RPAREN
    { Exp.Term_zip ($4, $4) }
  | DOLLAR FRESH LPAREN exp RPAREN
    { Exp.Term_fresh $4 }

sugared_formula:
  | exp TURNSTYLE exp COLON exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.typeof in
      let args = Exp.List [$1; $3; $5] in
      Exp.Formula_prop (predicate, args)
    }
  | exp STEP exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.step in
      let args = Exp.List [$1; $3] in
      Exp.Formula_prop (predicate, args)
    }
  | exp SUBTYPE exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.subtype in
      let args = Exp.List [$1; $3] in
      Exp.Formula_prop (predicate, args)
    }
  | exp TURNSTYLE exp SUBTYPE exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.subtype in
      let args = Exp.List [$1; $3; $5] in
      Exp.Formula_prop (predicate, args)
    }

formula:
  | sugared_formula
    { $1 }
  | AMPERSAND NOT LPAREN exp RPAREN
    { Exp.Formula_not $4 }
  | AMPERSAND LPAREN exp EQ exp RPAREN
    { Exp.Formula_eq ($3, $5) }
  | AMPERSAND LPAREN exp exp RPAREN
    { Exp.Formula_prop ($3, $4) }
  | AMPERSAND MEMBER exp exp
    { Exp.Formula_member ($3, $4) }
  | AMPERSAND SUBSET exp exp
    { Exp.Formula_subset ($3, $4) }
