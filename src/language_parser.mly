%{
  open Language
%}

%token EOF
%token <string> ID
%token <int> INT
%token GRAMMAR_ASSIGN
%token MID
%token COMMA
%token DASH
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE RBRACE
%token FSLASH
%token MAPSTO
%token EQ
%token QUOTE
%token IN FORALL FIND WHERE WITH

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
  | categories = list(grammar_category) rules = list(rule)
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
  | name = ID meta_var = ID GRAMMAR_ASSIGN terms = separated_list(MID, term)
    {
      let open Core_kernel in
      let terms = List.fold terms ~init:Term_set.empty ~f:Set.add in
      Grammar.Category.{name; meta_var; terms}
    }

rule:
  | LSQUARE name = ID RSQUARE premises = separated_list(COMMA, premise) nonempty_list(DASH) conclusion = formula
    { Rule.{name; premises; conclusion} }

forall_result:
  | ID EQ term
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
  | predicate = ID args = list(term)
    { Formula.{predicate; args} }

term:
  | QUOTE ID QUOTE
    { Term.Str $2 }
  | LPAREN name = ID args = list(term) RPAREN
    { Term.Constructor {name; args} }
  | ID
    { Term.Var $1 }
  | INT
    { Term.Num $1 }
  | LPAREN var = ID RPAREN body = term
    { Term.Binding {var; body} }
  | body = term LSQUARE subst = term FSLASH var = ID RSQUARE
    { Term.Subst {body; subst; var} }
  | LBRACE term RBRACE
    { Term.Seq $2 }
  | LBRACE key = ID MAPSTO value = term RBRACE
    { Term.Map {key; value} }
  | LPAREN t1 = term COMMA t2 = term COMMA rest = separated_list(COMMA, term) RPAREN
    { Term.Tuple (t1 :: t2 :: rest) }
