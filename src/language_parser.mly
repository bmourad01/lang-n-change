%{
  open Language

  let create_lan ?(relations = []) ?(hints = []) categories rules =
    let open Core_kernel in
    let categories =
      List.fold categories ~init:String.Map.empty ~f:(fun m c ->
        Map.set m Grammar.Category.(c.name) c)
    in
    let grammar = Grammar.{categories} in
    let relations = match String.Map.of_alist relations with
      | `Ok r -> r
      | `Duplicate_key p ->
         failwith (Printf.sprintf "duplicate relation signature for %s" p)
    in
    let rules =
      List.fold rules ~init:String.Map.empty ~f:(fun m r ->
        Map.set m Rule.(r.name) r)
    in
    let hints =
      List.fold hints ~init:String.Map.empty ~f:(fun m h ->
        match Map.add m Hint.(h.name) h with
        | `Ok m -> m
        | `Duplicate ->
           failwith (Printf.sprintf "duplicate hint %s" Hint.(h.name)))
    in {grammar; relations; rules; hints}
%}

%token EOF
%token <string> NAME
%token <int> INT
%token MOD
%token GRAMMARASSIGN
%token WILDCARD
%token MID
%token COMMA
%token COLON
%token DOT
%token DASH
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE RBRACE LANGLE RANGLE
%token FSLASH
%token MAPSTO
%token EQ
%token QUOTE
%token IN FORALL FIND WHERE WITH DOM RANGE MEMBER NOT UNION ZIP

%start lan
%type <Language.t> lan

%%

lan:
  | language EOF { $1 }

language:
  | categories = nonempty_list(grammar_category) MOD rules = nonempty_list(rule) MOD hints = nonempty_list(hint)
    { create_lan categories rules ~hints }
  | categories = nonempty_list(grammar_category) MOD rules = nonempty_list(rule)
    { create_lan categories rules }
  | categories = nonempty_list(grammar_category) MOD relations = nonempty_list(relation) MOD rules = nonempty_list(rule) MOD hints = nonempty_list(hint)
    { create_lan categories rules ~relations ~hints }
  | categories = nonempty_list(grammar_category) MOD relations = nonempty_list(relation) MOD rules = nonempty_list(rule)
    { create_lan categories rules ~relations }

hint_element:
  | NAME MAPSTO nonempty_list(NAME)
    {
      let open Core_kernel in
      String.Map.singleton $1 $3
    }
  | NAME
    {
      let open Core_kernel in
      String.Map.singleton $1 []
    }

hint:
  | name = NAME COLON elements = separated_nonempty_list(MID, hint_element) DOT
    {
      let open Core_kernel in
      let elements =
        List.fold elements ~init:String.Map.empty ~f:(fun m m' ->
          Map.merge_skewed m m' ~combine:(fun ~key _ v -> v))
      in Hint.{name; elements}
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

relation:
  | name = NAME LPAREN terms = separated_nonempty_list(COMMA, term) RPAREN
    { (name, terms) }

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
    { Premise.Prop $1 }

formula:
  | NOT LPAREN f = formula RPAREN
    { Formula.Not f }
  | term EQ term
    { Formula.Eq ($1, $3) }
  | MEMBER LPAREN element = term COMMA collection = term RPAREN
    { Formula.Member {element; collection} }
  | predicate = NAME LPAREN args = separated_list(COMMA, term) RPAREN
    { Formula.Default {predicate; args} }

subst:
  | term = term FSLASH var = NAME
    { Term.Subst_pair {term; var} }
  | NAME
    { Term.Subst_var $1 }

term:
  | DOM LPAREN term RPAREN
    { Term.Map_domain $3 }
  | RANGE LPAREN term RPAREN
    { Term.Map_range $3 }
  | UNION LPAREN t1 = term COMMA t2 = term RPAREN
    { Term.Union [t1; t2] }
  | UNION LPAREN t1 = term COMMA t2 = term COMMA rest = separated_list(COMMA, term) RPAREN
    { Term.Union (t1 :: t2 :: rest) }
  | ZIP LPAREN t1 = term COMMA t2 = term RPAREN
    { Term.Zip (t1, t2) }
  | QUOTE NAME QUOTE
    { Term.Str $2 }
  | LPAREN name = NAME DOT RPAREN
    { Term.Constructor {name; args = []} }
  | LPAREN name = NAME args = list(term) RPAREN
    { Term.Constructor {name; args} }
  | WILDCARD
    { Term.Wildcard }
  | NAME
    { Term.Var $1 }
  | INT
    { Term.Num $1 }
  | LPAREN var = NAME RPAREN body = term
    { Term.Binding {var; body} }
  | body = term LSQUARE substs = separated_nonempty_list(COMMA, subst) RSQUARE
    { Term.Subst {body; substs} }
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
