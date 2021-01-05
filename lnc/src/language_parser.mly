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
         invalid_arg (Printf.sprintf "duplicate relation signature for %s" p)
    in
    let rules =
      let check_undefined_relations (r : Rule.t) =
        let rec collect_props = function
          | Formula.Not f -> collect_props f
          | Formula.Eq _ -> []
          | Formula.Prop _ as p -> [p]
          | Formula.Member _ -> []
          | Formula.Subset _ -> []
        in
        List.fold (r.conclusion :: r.premises) ~init:[] ~f:(fun acc f ->
          acc @ (collect_props f))
        |> List.iter ~f:(function
             | Formula.Prop {predicate} -> (
                match Map.find relations predicate with
                | Some _ -> ()
                | None ->
                   invalid_arg
                     (Printf.sprintf "use of undefined relation %s in rule %s"
                        predicate r.name) )
             | _ -> ()) 
      in
      List.fold rules ~init:String.Map.empty ~f:(fun m r ->
        check_undefined_relations r; 
        match Map.add m Rule.(r.name) r with
        | `Ok m -> m
        | `Duplicate ->
           invalid_arg (Printf.sprintf "duplicate rule name %s" Rule.(r.name)))
    in
    let hints =
      List.fold hints ~init:String.Map.empty ~f:(fun m h ->
        match Map.add m Hint.(h.name) h with
        | `Ok m -> m
        | `Duplicate ->
           invalid_arg (Printf.sprintf "duplicate hint %s" Hint.(h.name)))
    in {grammar; relations; rules; hints}
%}

%token EOF
%token <string> STRING
%token <string> NAME
%token <int> NUM
%token MOD
%token GRAMMARASSIGN
%token WILDCARD
%token TILDE
%token TURNSTILE
%token SUBTYPE
%token STEP
%token MID
%token COMMA
%token CONS
%token COLON
%token DOT
%token DASH
%token LSQUARE RSQUARE LBRACE RBRACE LPAREN RPAREN LANGLE RANGLE
%token FSLASH
%token BIGARROW
%token MAPSTO
%token EQ
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

hint_value:
  | NAME
    { $1 }
  | NUM
    { Int.to_string $1 }

hint_element_list:
  | LSQUARE separated_nonempty_list(COMMA, hint_value) RSQUARE
    { Hint.Strs $2 }

hint_element:
  | NAME MAPSTO elems = nonempty_list(hint_value)
    {
      let open Core_kernel in
      let elems = List.map elems ~f:(fun e -> Hint.Str e) in
      String.Map.singleton $1 elems
    }
  | NAME MAPSTO nonempty_list(hint_element_list)
    {
      let open Core_kernel in
      String.Map.singleton $1 $3
    }
  | NAME
    {
      let open Core_kernel in
      String.Map.singleton $1 []
    }
  | NUM
    {
      let open Core_kernel in
      String.Map.singleton (Int.to_string $1) []
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
  | term TURNSTILE term COLON term DOT
    { (Predicate.Builtin.typeof, [$1; $3; $5]) }
  | term TURNSTILE term COLON term BIGARROW term DOT
    { (Predicate.Builtin.typeof_match, [$1; $3; $5; $7]) }
  | term STEP term DOT
    { (Predicate.Builtin.step, [$1; $3]) }
  | term SUBTYPE term DOT
    { (Predicate.Builtin.subtype, [$1; $3]) }
  | term TURNSTILE term SUBTYPE term BIGARROW term DOT
    { (Predicate.Builtin.subtype_flow, [$1; $3; $5]) }
  | term TURNSTILE term SUBTYPE term DOT
    { (Predicate.Builtin.subtype, [$1; $3; $5]) }
  | term TILDE term DOT
    { (Predicate.Builtin.consistent, [$1; $3]) }

relation:
  | sugared_relation
    { $1 }
  | NAME nonempty_list(term) DOT
    { ($1, $2) }

sugared_formula:
  | term TURNSTILE term COLON term
    {
      let predicate = Predicate.Builtin.typeof in
      let args = [$1; $3; $5] in
      Formula.Prop {predicate; args}
    }
  | term TURNSTILE term COLON term BIGARROW term
    {
      let predicate = Predicate.Builtin.typeof_match in
      let args = [$1; $3; $5; $7] in
      Formula.Prop {predicate; args}
    }
  | term STEP term
    {
      let predicate = Predicate.Builtin.step in
      let args = [$1; $3] in
      Formula.Prop {predicate; args}
    }
  | term SUBTYPE term
    {
      let predicate = Predicate.Builtin.subtype in
      let args = [$1; $3] in
      Formula.Prop {predicate; args}
    }
  | term SUBTYPE term BIGARROW term
    {
      let predicate = Predicate.Builtin.subtype_flow in
      let args = [$1; $3; $5] in
      Formula.Prop {predicate; args}
    }
  | term TURNSTILE term SUBTYPE term
    {
      let predicate = Predicate.Builtin.subtype in
      let args = [$1; $3; $5] in
      Formula.Prop {predicate; args}
    }
  | term TILDE term
    {
      let predicate = Predicate.Builtin.consistent in
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
  | term EQ FSLASH EQ term
    { Formula.(Not (Eq ($1, $5))) }
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
  | STRING
    { Term.Str $1 }
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
  | body = term LBRACE subst = subst RBRACE
    { Term.Subst {body; subst} }
  | LSQUARE key = term MAPSTO value = term RSQUARE map = term
    { Term.Map_update {map; key; value} }
  | NIL
    { Term.Nil }
  | LSQUARE term DOT DOT DOT RSQUARE
    { Term.List $2 }
  | LPAREN term CONS term RPAREN
    { Term.Cons ($2, $4) }
  | LANGLE t1 = term COMMA t2 = term RANGLE
    { Term.Tuple ([t1; t2]) }
  | LANGLE t1 = term COMMA t2 = term COMMA rest = separated_list(COMMA, term) RANGLE
    { Term.Tuple (t1 :: t2 :: rest) }
