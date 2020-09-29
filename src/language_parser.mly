%{
  open Language

  let create_lan ?(relations = []) ?(hints = []) grammar rules =
    let open Core_kernel in
    let grammar =
      List.fold grammar ~init:String.Map.empty ~f:(fun m c ->
        Map.set m Grammar.Category.(c.name) c)
    in
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
%token MOD
%token GRAMMARASSIGN
%token WILDCARD
%token TURNSTYLE
%token STEP
%token MID
%token COMMA
%token CONS
%token COLON
%token DOT
%token DASH
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE RBRACE LANGLE RANGLE
%token FSLASH
%token MAPSTO
%token EQ
%token QUOTE
%token NIL DOM RANGE MEMBER NOT UNION MAPUNION SUBSET ZIP FRESH

%start lan
%type <Language.t> lan

%%

lan:
  | language EOF { $1 }

language:
  | grammar = nonempty_list(grammar_category) MOD rules = nonempty_list(rule) MOD hints = nonempty_list(hint)
    { create_lan grammar rules ~hints }
  | grammar = nonempty_list(grammar_category) MOD rules = nonempty_list(rule)
    { create_lan grammar rules }
  | grammar = nonempty_list(grammar_category) MOD relations = nonempty_list(relation) MOD rules = nonempty_list(rule) MOD hints = nonempty_list(hint)
    { create_lan grammar rules ~relations ~hints }
  | grammar = nonempty_list(grammar_category) MOD relations = nonempty_list(relation) MOD rules = nonempty_list(rule)
    { create_lan grammar rules ~relations }

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
      if String.(equal name (capitalize name)) then
        let terms = List.fold terms ~init:Term_set.empty ~f:Set.add in
        Grammar.Category.{name; meta_var; terms}
      else
        invalid_arg
          (Printf.sprintf
             "bad grammar category name %s, must be capitalized"
             name)
    }

rule:
  | LSQUARE name = NAME RSQUARE premises = separated_list(COMMA, formula) nonempty_list(DASH) conclusion = formula DOT
    { Rule.{name; premises; conclusion} }

sugared_relation:
  | term TURNSTYLE term COLON term DOT
    { (Predicate.Builtin.typeof, [$1; $3; $5]) }
  | term STEP term DOT
    { (Predicate.Builtin.step, [$1; $3]) }

relation:
  | sugared_relation
    { $1 }
  | NAME nonempty_list(term) DOT
    { ($1, $2) }

sugared_formula:
  | term TURNSTYLE term COLON term
    {
      let predicate = Predicate.Builtin.typeof in
      let args = [$1; $3; $5] in
      Formula.Prop {predicate; args}
    }
  | term STEP term
    {
      let predicate = Predicate.Builtin.step in
      let args = [$1; $3] in
      Formula.Prop {predicate; args}
    }

formula:
  | sugared_formula
    { $1 }
  | NOT LPAREN f = formula RPAREN
    { Formula.Not f }
  | term EQ term
    { Formula.Eq ($1, $3) }
  | MEMBER element = term collection = term
    { Formula.Member {element; collection} }
  | SUBSET sub = term super = term
    { Formula.Subset {sub; super} }
  | predicate = NAME args = nonempty_list(term)
    { Formula.Prop {predicate; args} }

subst:
  | term FSLASH NAME
    { Term.Subst_pair ($1, $3) }
  | NAME COLON NAME
    { Term.Subst_var ($1, $3) }

term:
  | DOM LPAREN term RPAREN
    { Term.Map_domain $3 }
  | RANGE LPAREN term RPAREN
    { Term.Map_range $3 }
  | UNION LPAREN t1 = term COMMA t2 = term RPAREN
    { Term.Union [t1; t2] }
  | UNION LPAREN t1 = term COMMA t2 = term COMMA rest = separated_list(COMMA, term) RPAREN
    { Term.Union (t1 :: t2 :: rest) }
  | MAPUNION LPAREN t1 = term COMMA t2 = term RPAREN
    { Term.Map_union [t1; t2] }
  | MAPUNION LPAREN t1 = term COMMA t2 = term COMMA rest = separated_list(COMMA, term) RPAREN
    { Term.Map_union (t1 :: t2 :: rest) }
  | ZIP LPAREN t1 = term COMMA t2 = term RPAREN
    { Term.Zip (t1, t2) }
  | FRESH LPAREN term RPAREN
    { Term.Fresh $3 }
  | QUOTE NAME QUOTE
    { Term.Str $2 }
  | LPAREN name = NAME DOT RPAREN
    {
      let open Core_kernel in
      if String.(equal name (uncapitalize name)) then
        Term.Constructor {name; args = []}
      else
        invalid_arg
          (Printf.sprintf
             "bad constructor name %s, cannot be capitalized"
             name)
    }
  | LPAREN name = NAME args = list(term) RPAREN
    { Term.Constructor {name; args} }
  | WILDCARD
    { Term.Wildcard }
  | NAME
    { Term.Var $1 }
  | LPAREN var = NAME RPAREN body = term
    { Term.Binding {var; body} }
  | body = term LSQUARE substs = separated_nonempty_list(COMMA, subst) RSQUARE
    { Term.Subst {body; substs} }
  | LSQUARE key = term MAPSTO value = term RSQUARE map = term
    { Term.Map_update {map; key; value} }
  | NIL
    { Term.Nil }
  | LSQUARE term DOT DOT DOT RSQUARE
    { Term.List $2 }
  | LBRACE key = NAME MAPSTO value = term RBRACE
    { Term.Map {key; value} }
  | LPAREN term CONS term RPAREN
    { Term.Cons ($2, $4) }
  | LANGLE t1 = term COMMA t2 = term RANGLE
    { Term.Tuple ([t1; t2]) }
  | LANGLE t1 = term COMMA t2 = term COMMA rest = separated_list(COMMA, term) RANGLE
    { Term.Tuple (t1 :: t2 :: rest) }
