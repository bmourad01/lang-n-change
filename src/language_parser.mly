%{
  open Language
%}

%token EOF
%token <string> NAME
%token <int> INT
%token MOD
%token GRAMMARASSIGN
%token MID
%token COMMA
%token DOT
%token DASH
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE RBRACE LANGLE RANGLE
%token FSLASH
%token MAPSTO
%token EQ
%token QUOTE
%token IN FORALL FIND WHERE WITH DOM RANGE MEMBER

%start lan
%type <Language.t> lan

%%

lan:
  | EOF
    {
      let open Core_kernel in
      let grammar = Grammar.{categories = String.Map.empty} in
      let rules = String.Map.empty in
      Language.{grammar; rules}
    }
  | language EOF { $1 }

language:
  | categories = nonempty_list(grammar_category) MOD rules = nonempty_list(rule)
    {
      let open Core_kernel in
      let categories =
        List.fold categories ~init:String.Map.empty ~f:(fun m c ->
          Map.set m Grammar.Category.(c.name) c)
      in
      let grammar = Grammar.{categories} in
      let rules =
        List.fold rules ~init:String.Map.empty ~f:(fun m r ->
          Map.set m r.name r)
      in {grammar; rules}
    }

grammar_category:
  | name = NAME meta_var = NAME GRAMMARASSIGN terms = separated_list(MID, term)
    {
      let open Core_kernel in
      let terms = List.fold terms ~init:Term_set.empty ~f:Set.add in
      Grammar.Category.{name; meta_var; terms}
    }

rule:
  | LSQUARE name = NAME RSQUARE premises = separated_list(COMMA, premise) nonempty_list(DASH) conclusion = formula
    { Rule.{name; premises; conclusion} }

forall_result:
  | NAME EQ term
    { ($1, $3) }

premise:
  | FORALL element = term IN collection = term COMMA formulae = separated_nonempty_list(COMMA, formula) WITH result = separated_nonempty_list(COMMA, forall_result)
    { Premise.Forall {element; collection; formulae; result} }
  | FORALL element = term IN collection = term COMMA formulae = separated_nonempty_list(COMMA, formula)
    { Premise.Forall {element; collection; formulae; result = []} }
  | FIND element = term IN collection = term WHERE formulae = separated_nonempty_list(COMMA, formula)
    { Premise.Find {element; collection; formulae} }
  | formula
    { Premise.Proposition $1 }

formula:
  | MEMBER LPAREN element = term COMMA collection = term RPAREN
    { Formula.Member {element; collection} }
  | predicate = NAME LPAREN args = separated_list(COMMA, term) RPAREN
    { Formula.Default {predicate; args} }

term:
  | DOM LPAREN m = NAME RPAREN
    { Term.Map_domain m }
  | RANGE LPAREN m = NAME RPAREN
    { Term.Map_range m }
  | QUOTE NAME QUOTE
    { Term.Str $2 }
  | LPAREN name = NAME DOT RPAREN
    { Term.Constructor {name; args = []} }
  | LPAREN name = NAME args = list(term) RPAREN
    { Term.Constructor {name; args} }
  | NAME
    { Term.Var $1 }
  | INT
    { Term.Num $1 }
  | LPAREN var = NAME RPAREN body = term
    { Term.Binding {var; body} }
  | body = term LSQUARE subst = term FSLASH var = NAME RSQUARE
    { Term.Subst {body; subst; var} }
  | LSQUARE key = NAME MAPSTO value = term RSQUARE map = NAME
    { Term.Map_update {map; key; value} }
  | LBRACE term RBRACE
    { Term.Seq $2 }
  | LBRACE key = NAME MAPSTO value = term RBRACE
    { Term.Map {key; value} }
  | LANGLE t1 = term COMMA t2 = term RANGLE
    { Term.Tuple ([t1; t2]) }
  | LANGLE t1 = term COMMA t2 = term COMMA rest = separated_list(COMMA, term) RANGLE
    { Term.Tuple (t1 :: t2 :: rest) }
