%{
    open Ltr
%}

%token EOF
%token <string> STR
%token <string> CAPNAME
%token <string> NAME
%token <int> NUM
%token AND OR
%token HASH
%token DOLLAR
%token AT
%token AMPERSAND
%token WILDCARD
%token GRAMMARASSIGN
%token TURNSTILE
%token SUBTYPE
%token TILDE
%token BACKTICK
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
%token BIGARROW
%token MAPSTO
%token EQ
%token QLESS QGREATER QMEMBER QASSOC QNOTHING QSOMETHING QEMPTY QVAR QCONSTVAR QSTR QCONSTRUCTOR QBINDING QSUBST QLIST QTUPLE QVARKIND QOPKIND QSYNTAX QSTARTSWITH QENDSWITH
%token LIFT TO KEEP SKIP MATCH WITH WHEN FRESHVAR SUBSTITUTE VAROVERLAP NTH HEAD TAIL LAST DIFF INTERSECT GETASSOC ASSOC KEYS LENGTH APPEND REV DEDUP CONCAT VARS UNBIND BOUND NOTHING SOMETHING GET IF THEN ELSE LET REC IN UPPERCASE LOWERCASE STRINT INTSTR SELF UNIFYNORMALIZE UNIFY UNIQUIFY REMOVESYNTAX METAVAR CATEGORIES SYNTAX OPKIND VARKIND ADDRELATION RELATIONS SETRELATIONS REMOVERELATION RULENAME PREMISES PREMISESELF CONCLUSION SETCONCLUSION RULES CAPRULE ADDRULES ADDRULE SETRULES HINT HINTLIST REMOVEHINT
%token NIL DOM RANGE MEMBER NOT UNION MAPUNION MAPUNIONUNIQ SUBSET ZIP UNZIP FRESH
%token LAN RULE FORMULA TERM STRING BOOL INT TUPLE OPTION LIST
%token TRUE FALSE

%left AND OR
%left CARET
%right CONS SEMI

%start ltr
%type <Ltr.Exp.t> ltr

%%

ltr:
  | exp EOF { $1 }

meta_var:
  | CAPNAME
    { $1 }
  | NAME
    { $1 }

let_name:
  | WILDCARD
    { "_" }
  | NAME
    { $1 }

exp:
  | LPAREN exp RPAREN
    { $2 }
  | SELF
    { Exp.Self }
  | UNIFYNORMALIZE LPAREN rules = exp COMMA term_subs = exp COMMA formula_subs = exp COMMA candidates = exp COMMA proven = exp RPAREN
    { Exp.Unify {normalize = true; rules; term_subs; formula_subs; candidates; proven} }
  | UNIFY LPAREN rules = exp COMMA term_subs = exp COMMA formula_subs = exp COMMA candidates = exp COMMA proven = exp RPAREN
    { Exp.Unify {normalize = false; rules; term_subs; formula_subs; candidates; proven} }
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
  | STRINT LPAREN exp RPAREN
    { Exp.Str_int $3 }
  | NUM
    { Exp.Int $1 }
  | INTSTR LPAREN exp RPAREN
    { Exp.Int_str $3 }
  | boolean
    { Exp.Bool_exp $1 }
  | LET REC name = NAME args = nonempty_list(let_arg) COLON ret = typ EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = true;
          names = [name];
          args;
          ret = Some ret;
          exp;
          body;
        }
    }
  | LET name = NAME args = nonempty_list(let_arg) COLON ret = typ EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = false;
          names = [name];
          args;
          ret = Some ret;
          exp;
          body;
        }
    }
  | LET name = NAME args = nonempty_list(let_arg) EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = false;
          names = [name];
          args;
          ret = None;
          exp;
          body;
        }
    }
  | LET name = NAME COLON ret = typ EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = false;
          names = [name];
          args = [];
          ret = Some ret;
          exp;
          body;
        }
    }
  | LET name = NAME EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = false;
          names = [name];
          args = [];
          ret = None;
          exp;
          body;
        }
    }
  | LET LPAREN name1 = let_name COMMA name2 = let_name RPAREN EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = false;
          names = [name1; name2];
          args = [];
          ret = None;
          exp;
          body;
        }
    }
  | LET LPAREN name1 = let_name COMMA name2 = let_name COMMA names = separated_nonempty_list(COMMA, let_name) RPAREN EQ exp = exp IN body = exp
    {
      Exp.Let {
          recursive = false;
          names = name1 :: name2 :: names;
          args = [];
          ret = None;
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
  | SKIP
    { Exp.Skip }
  | LIFT pattern TO exp DOT
    { Exp.Lift ($2, $4) }
  | LIFT pattern TO exp IN exp
    { Exp.Lift_in_rule ($2, $4, $6) }
  | field = exp LSQUARE BACKTICK pattern = pattern BACKTICK WHEN when_ = exp RSQUARE COLON body = exp
    { Exp.Select {keep = false; field; pattern; when_ = Some when_; body} }
  | field = exp LSQUARE BACKTICK pattern = pattern BACKTICK RSQUARE COLON body = exp
    { Exp.Select {keep = false; field; pattern; when_ = None; body} }
  | field = exp LPAREN KEEP RPAREN LSQUARE BACKTICK pattern = pattern BACKTICK WHEN when_ = exp RSQUARE COLON body = exp
    { Exp.Select {keep = true; field; pattern; when_ = Some when_; body} }
  | field = exp LPAREN KEEP RPAREN LSQUARE BACKTICK pattern = pattern BACKTICK RSQUARE COLON body = exp
    { Exp.Select {keep = true; field; pattern; when_ = None; body} }
  | MATCH exp = exp WITH MID cases = separated_nonempty_list(MID, match_case)
    { Exp.Match {exp; cases} }
  | MATCH exp = exp WITH cases = separated_nonempty_list(MID, match_case)
    { Exp.Match {exp; cases} }
  | LPAREN exp COMMA exp RPAREN
    { Exp.Tuple [$2; $4] }
  | LPAREN exp COMMA exp COMMA separated_nonempty_list(COMMA, exp) RPAREN
    { Exp.Tuple ($2 :: $4 :: $6) }
  | LSQUARE exp DOT RSQUARE
    { Exp.List [$2] }
  | LSQUARE separated_list(COMMA, exp) RSQUARE
    { Exp.List $2 }
  | exp CONS exp
    { Exp.Cons ($1, $3) }
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
  | INTERSECT LPAREN exp COMMA exp RPAREN
    { Exp.Intersect ($3, $5) }
  | ZIP LPAREN exp COMMA exp RPAREN
    { Exp.Zip ($3, $5) }
  | UNZIP LPAREN exp RPAREN
    { Exp.Unzip ($3) }
  | GETASSOC LPAREN exp COMMA exp RPAREN
    { Exp.(Option_get (Assoc ($3, $5))) }
  | ASSOC LPAREN exp COMMA exp RPAREN
    { Exp.Assoc ($3, $5) }
  | KEYS LPAREN exp RPAREN
    { Exp.Keys_of $3 }
  | LENGTH LPAREN exp RPAREN
    { Exp.Length $3 }
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
  | VARS EXCL LPAREN exp RPAREN
    { Exp.Vars_dup_of $4 }
  | FRESHVAR LPAREN exp RPAREN
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
  | CATEGORIES
    { Exp.Categories_of }
  | name = CAPNAME meta_var = meta_var GRAMMARASSIGN DOT DOT DOT MID terms = separated_nonempty_list(MID, exp) DOT
    {
      Exp.New_syntax {
          extend = true;
          name;
          meta_var;
          terms;
        }
    }
  | name = CAPNAME meta_var = meta_var GRAMMARASSIGN terms = separated_nonempty_list(MID, exp) DOT
    {
      Exp.New_syntax {
          extend = false;
          name;
          meta_var;
          terms;
        }
    }
  | name = CAPNAME meta_var = meta_var GRAMMARASSIGN LBRACE terms = exp RBRACE
    {
      Exp.New_syntax_of_exp {
          name;
          meta_var;
          terms;
        }
    }
  | REMOVESYNTAX LPAREN exp RPAREN
    { Exp.Remove_syntax $3 }
  | METAVAR LPAREN exp RPAREN
    { Exp.Meta_var_of $3 }
  | SYNTAX LPAREN exp RPAREN
    { Exp.Syntax_terms_of $3 }
  | CAPNAME
    { Exp.(Syntax_terms_of (Str $1)) }
  | OPKIND LPAREN exp RPAREN
    { Exp.Kind_of_op $3 }
  | VARKIND LPAREN exp RPAREN
    { Exp.Kind_of_var $3 }
  | ADDRELATION LPAREN relation RPAREN
    { $3 }
  | RELATIONS
    { Exp.Relations_of }
  | SETRELATIONS LPAREN exp RPAREN
    { Exp.Set_relations $3 }
  | REMOVERELATION LPAREN exp RPAREN
    { Exp.Remove_relation $3 }
  | formula
    { Exp.New_formula $1 }
  | UNIQUIFY LPAREN formulae = exp COMMA ignored_formulae = exp COMMA hint_map = exp COMMA hint_var = exp COMMA prev_vars = exp RPAREN
    { Exp.Uniquify_formulae {formulae; ignored_formulae; hint_map; hint_var; prev_vars = Some prev_vars} }
  | UNIQUIFY LPAREN formulae = exp COMMA ignored_formulae = exp COMMA hint_map = exp COMMA hint_var = exp RPAREN
    { Exp.Uniquify_formulae {formulae; ignored_formulae; hint_map; hint_var; prev_vars = None} }
  | LSQUARE name = exp RSQUARE LBRACE premises = separated_list(COMMA, exp) nonempty_list(DASH) conclusion = exp RBRACE
    { Exp.New_rule {name; premises; conclusion} }
  | RULENAME LPAREN exp RPAREN
    { Exp.Rule_name $3 }
  | PREMISES LPAREN exp RPAREN
    { Exp.Rule_premises $3 }
  | PREMISESELF
    { Exp.Rule_premises_self }
  | CONCLUSION LPAREN exp RPAREN
    { Exp.Rule_conclusion $3 }
  | CONCLUSION
    { Exp.Rule_conclusion_self }
  | SETCONCLUSION LPAREN exp COMMA exp RPAREN
    { Exp.Set_conclusion ($3, $5) }
  | RULES
    { Exp.Rules_of }
  | CAPRULE
    { Exp.Rules_of }
  | ADDRULES LPAREN exp RPAREN
    { Exp.Add_rules $3 }
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
  | HINT LPAREN exp RPAREN
    { Exp.Lookup_hint $3 }
  | HINTLIST LPAREN exp RPAREN
    { Exp.Lookup_hint_list $3 }
  | REMOVEHINT LPAREN exp RPAREN
    { Exp.Remove_hint $3 }
  | REMOVEHINT LPAREN exp COMMA exp RPAREN
    { Exp.Remove_hint_key ($3, $5) }

match_case:
  | pattern ARROW exp
    { ($1, None, $3) }
  | pattern WHEN exp ARROW exp
    { ($1, Some $3, $5) }

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
  | exp TURNSTILE exp COLON exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.typeof, Exp.List [$1; $3; $5]) }
  | exp TURNSTILE exp COLON exp BIGARROW exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.typeof_match, Exp.List [$1; $3; $5; $7]) }
  | exp TURNSTILE exp BIGARROW exp COLON exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.typeof_cc, Exp.List [$1; $3; $5; $7]) }
  | exp STEP exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.step, Exp.List [$1; $3]) }
  | exp SUBTYPE exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.subtype, Exp.List [$1; $3]) }
  | exp SUBTYPE exp BIGARROW exp exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.subtype_flow, Exp.List [$1; $3; $5; $6]) }
  | exp TURNSTILE exp SUBTYPE exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.subtype, Exp.List [$1; $3; $5]) }
  | exp TILDE exp
    { Exp.New_relation (Exp.Str Language.Predicate.Builtin.consistent, Exp.List [$1; $3]) }

relation:
  | sugared_relation
    { $1 }
  | exp COMMA exp
    { Exp.New_relation ($1, $3) }

boolean:
  | TRUE
    { Exp.Bool true }
  | FALSE
    { Exp.Bool false }
  | NOT LPAREN exp RPAREN
    { Exp.Not $3 }
  | exp AND exp
    { Exp.And ($1, $3) }
  | exp OR exp
    { Exp.Or ($1, $3) }
  | exp EQ exp
    { Exp.Eq ($1, $3) }
  | QLESS LPAREN exp COMMA exp RPAREN
    { Exp.Lt ($3, $5) }
  | QGREATER LPAREN exp COMMA exp RPAREN
    { Exp.Gt ($3, $5) }
  | QMEMBER LPAREN exp COMMA exp RPAREN
    { Exp.Is_member ($3, $5) }
  | QASSOC LPAREN exp COMMA exp RPAREN
    { Exp.Is_assoc ($3, $5) }
  | QNOTHING LPAREN exp RPAREN
    { Exp.Is_nothing $3 }
  | QSOMETHING LPAREN exp RPAREN
    { Exp.Is_something $3 }
  | QEMPTY LPAREN exp RPAREN
    { Exp.Is_empty $3 }
  | QVAR LPAREN exp RPAREN
    { Exp.Is_var $3 }
  | QCONSTVAR LPAREN exp RPAREN
    { Exp.Is_const_var $3 }
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
  | QTUPLE LPAREN exp RPAREN
    { Exp.Is_tuple $3 }
  | QVARKIND LPAREN exp COMMA exp RPAREN
    { Exp.Is_var_kind ($3, $5) }
  | QOPKIND LPAREN exp COMMA exp RPAREN
    { Exp.Is_op_kind ($3, $5) }
  | QSYNTAX LPAREN name = CAPNAME RPAREN
    { Exp.Has_syntax name }
  | QSTARTSWITH LPAREN exp COMMA exp RPAREN
    { Exp.Starts_with ($3, $5) }
  | QENDSWITH LPAREN exp COMMA exp RPAREN
    { Exp.Ends_with ($3, $5) }

subst:
  | exp FSLASH NAME
    { Exp.Subst_pair ($1, $3) }
  | meta_var COLON k = CAPNAME
    { Exp.Subst_var ($1, k) }

term:
  | DOLLAR NIL
    { Exp.Term_nil }
  | DOLLAR meta_var
    { Exp.Term_var $2 }
  | DOLLAR EXCL exp
    { Exp.Term_var_exp $3 }
  | DOLLAR STR
    { Exp.Term_str $2 }
  | LPAREN exp exp RPAREN
    { Exp.Term_constructor ($2, $3) }
  | DOLLAR LPAREN exp RPAREN exp
    { Exp.Term_binding ($3, $5) }
  | exp LBRACE subst RBRACE
    { Exp.Term_subst ($1, $3) }
  | LSQUARE exp MAPSTO exp RSQUARE exp
    { Exp.Term_map_update ($2, $4, $6) }
  | DOLLAR DOM LPAREN exp RPAREN
    { Exp.Term_map_domain $4 }
  | DOLLAR RANGE LPAREN exp RPAREN
    { Exp.Term_map_range $4 }
  | DOLLAR LPAREN exp CONS exp RPAREN
    { Exp.Term_cons ($3, $5) }
  | LSQUARE exp DOT DOT DOT RSQUARE
    { Exp.Term_list $2 }
  | LANGLE exp RANGLE
    { Exp.Term_tuple $2 }
  | DOLLAR UNION LPAREN exp RPAREN
    { Exp.Term_union $4 }
  | DOLLAR MAPUNION LPAREN exp RPAREN
    { Exp.Term_map_union $4 }
  | DOLLAR MAPUNIONUNIQ LPAREN exp RPAREN
    { Exp.Term_map_union_uniq $4 }
  | DOLLAR ZIP LPAREN exp COMMA exp RPAREN
    { Exp.Term_zip ($4, $4) }
  | DOLLAR FRESH LPAREN exp RPAREN
    { Exp.Term_fresh $4 }

sugared_formula:
  | exp TURNSTILE exp COLON exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.typeof in
      let args = Exp.List [$1; $3; $5] in
      Exp.Formula_prop (predicate, args)
    }
  | exp TURNSTILE exp COLON exp BIGARROW exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.typeof_match in
      let args = Exp.List [$1; $3; $5; $7] in
      Exp.Formula_prop (predicate, args)
    }
  | exp TURNSTILE exp BIGARROW exp COLON exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.typeof_cc in
      let args = Exp.List [$1; $3; $5; $7] in
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
  | exp SUBTYPE exp BIGARROW exp exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.subtype_flow in
      let args = Exp.List [$1; $3; $5; $6] in
      Exp.Formula_prop (predicate, args)
    }
  | exp TURNSTILE exp SUBTYPE exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.subtype in
      let args = Exp.List [$1; $3; $5] in
      Exp.Formula_prop (predicate, args)
    }
  | exp TILDE exp
    {
      let predicate = Exp.Str Language.Predicate.Builtin.consistent in
      let args = Exp.List [$1; $3] in
      Exp.Formula_prop (predicate, args)
    }

formula:
  | sugared_formula
    { $1 }
  | AMPERSAND NOT LPAREN exp RPAREN
    { Exp.Formula_not $4 }
  | AMPERSAND LPAREN exp EQ exp RPAREN
    { Exp.Formula_eq ($3, $5) }
  | AMPERSAND LPAREN exp EQ FSLASH EQ exp RPAREN
    { Exp.(Formula_not (New_formula (Formula_eq ($3, $7)))) }
  | AMPERSAND LPAREN exp exp RPAREN
    { Exp.Formula_prop ($3, $4) }
  | AMPERSAND MEMBER exp exp
    { Exp.Formula_member ($3, $4) }
  | AMPERSAND SUBSET exp exp
    { Exp.Formula_subset ($3, $4) }

pattern:
  | LPAREN pattern RPAREN
    { $2 }
  | WILDCARD
    { Exp.Pattern.Wildcard }
  | NAME
    { Exp.Pattern.Var $1 }
  | STR
    { Exp.Pattern.Str $1 }
  | pattern_term
    { Exp.Pattern.Term $1 }
  | pattern_formula
    { Exp.Pattern.Formula $1 }
  | LSQUARE separated_list(COMMA, pattern) RSQUARE
    { Exp.Pattern.List $2 }
  | pattern CONS pattern
    { Exp.Pattern.Cons ($1, $3) }
  | LPAREN pattern COMMA pattern RPAREN
    { Exp.Pattern.Tuple [$2; $4] }
  | LPAREN pattern COMMA pattern COMMA separated_nonempty_list(COMMA, pattern) RPAREN
    { Exp.Pattern.Tuple ($2 :: $4 :: $6) }
  | NOTHING
    { Exp.Pattern.Nothing }
  | SOMETHING LPAREN pattern RPAREN
    { Exp.Pattern.Something $3 }

pattern_subst:
  | pattern FSLASH NAME
    { Exp.Pattern.Subst_pair ($1, $3) }
  | NAME
    { Exp.Pattern.Subst_var $1 }

pattern_term:
  | DOLLAR NIL
    { Exp.Pattern.Term_nil }
  | DOLLAR meta_var
    { Exp.Pattern.Term_var $2 }
  | DOLLAR EXCL pattern
    { Exp.Pattern.Term_var_pat $3 }
  | DOLLAR STR
    { Exp.Pattern.Term_str $2 }
  | LPAREN pattern pattern RPAREN
    { Exp.Pattern.Term_constructor ($2, $3) }
  | DOLLAR LPAREN pattern RPAREN pattern
    { Exp.Pattern.Term_binding ($3, $5) }
  | pattern LBRACE pattern_subst RBRACE
    { Exp.Pattern.Term_subst ($1, $3) }
  | LSQUARE pattern MAPSTO pattern RSQUARE pattern
    { Exp.Pattern.Term_map_update ($2, $4, $6) }
  | DOLLAR DOM LPAREN pattern RPAREN
    { Exp.Pattern.Term_map_domain $4 }
  | DOLLAR RANGE LPAREN pattern RPAREN
    { Exp.Pattern.Term_map_range $4 }
  | DOLLAR LPAREN pattern CONS pattern RPAREN
    { Exp.Pattern.Term_cons ($3, $5) }
  | LSQUARE pattern DOT DOT DOT RSQUARE
    { Exp.Pattern.Term_list $2 }
  | LANGLE pattern RANGLE
    { Exp.Pattern.Term_tuple $2 }
  | DOLLAR UNION LPAREN pattern RPAREN
    { Exp.Pattern.Term_union $4 }
  | DOLLAR MAPUNION LPAREN pattern RPAREN
    { Exp.Pattern.Term_map_union $4 }
  | DOLLAR MAPUNIONUNIQ LPAREN pattern RPAREN
    { Exp.Pattern.Term_map_union_uniq $4 }
  | DOLLAR ZIP LPAREN pattern COMMA pattern RPAREN
    { Exp.Pattern.Term_zip ($4, $4) }
  | DOLLAR FRESH LPAREN pattern RPAREN
    { Exp.Pattern.Term_fresh $4 }

sugared_pattern_formula:
  | pattern TURNSTILE pattern COLON pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.typeof in
      let args = Exp.Pattern.List [$1; $3; $5] in
      Exp.Pattern.Formula_prop (predicate, args)
    }
  | pattern TURNSTILE pattern COLON pattern BIGARROW pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.typeof_match in
      let args = Exp.Pattern.List [$1; $3; $5; $7] in
      Exp.Pattern.Formula_prop (predicate, args)
    }
  | pattern TURNSTILE pattern BIGARROW pattern COLON pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.typeof_cc in
      let args = Exp.Pattern.List [$1; $3; $5; $7] in
      Exp.Pattern.Formula_prop (predicate, args)
    }
  | pattern STEP pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.step in
      let args = Exp.Pattern.List [$1; $3] in
      Exp.Pattern.Formula_prop (predicate, args)
    }
  | pattern SUBTYPE pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.subtype in
      let args = Exp.Pattern.List [$1; $3] in
      Exp.Pattern.Formula_prop (predicate, args)
    }
  | pattern SUBTYPE pattern BIGARROW pattern pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.subtype_flow in
      let args = Exp.Pattern.List [$1; $3; $5; $6] in
      Exp.Pattern.Formula_prop (predicate, args)
    }
  | pattern TURNSTILE pattern SUBTYPE pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.subtype in
      let args = Exp.Pattern.List [$1; $3; $5] in
      Exp.Pattern.Formula_prop (predicate, args)
    }
  | pattern TILDE pattern
    {
      let predicate = Exp.Pattern.Str Language.Predicate.Builtin.consistent in
      let args = Exp.Pattern.List [$1; $3] in
      Exp.Pattern.Formula_prop (predicate, args)
    }

pattern_formula:
  | sugared_pattern_formula
    { $1 }
  | AMPERSAND NOT LPAREN pattern RPAREN
    { Exp.Pattern.Formula_not $4 }
  | AMPERSAND LPAREN pattern EQ pattern RPAREN
    { Exp.Pattern.Formula_eq ($3, $5) }
  | AMPERSAND LPAREN pattern pattern RPAREN
    { Exp.Pattern.Formula_prop ($3, $4) }
  | AMPERSAND MEMBER pattern pattern
    { Exp.Pattern.Formula_member ($3, $4) }
  | AMPERSAND SUBSET pattern pattern
    { Exp.Pattern.Formula_subset ($3, $4) }
