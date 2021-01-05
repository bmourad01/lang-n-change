open Core_kernel

module Term : sig
  type t =
    | Wildcard
    | Nil
    | Var of string
    | Str of string
    | Constructor of {name: string; args: t list}
    | Binding of {var: string; body: t}
    | Subst of {body: t; subst: subst}
    | Map_update of {key: t; value: t; map: t}
    | Map_domain of t
    | Map_range of t
    | Map_union of t list
    | Cons of t * t
    | List of t
    | Tuple of t list
    | Union of t list
    | Zip of t * t
    | Fresh of t

  and subst = Subst_pair of t * string | Subst_var of string * string
  [@@deriving equal, compare, sexp]

  type subs = (t, t) List.Assoc.t

  type uniquify_map = (t, t list) List.Assoc.t

  val to_string : t -> string

  val is_var : t -> bool

  val is_str : t -> bool

  val is_constructor : t -> bool

  val is_binding : t -> bool

  val is_subst : t -> bool

  val is_subst_pair : subst -> bool

  val is_subst_var : subst -> bool

  val is_map_update : t -> bool

  val is_map_domain : t -> bool

  val is_map_range : t -> bool

  val is_map_union : t -> bool

  val is_nil : t -> bool

  val is_cons : t -> bool

  val is_list : t -> bool

  val is_tuple : t -> bool

  val is_union : t -> bool

  val is_zip : t -> bool

  val is_fresh : t -> bool

  val unbind : t -> t

  val unbind_rec : t -> t

  val vars_dup : ?include_bindings:bool -> t -> t list

  val vars : ?include_bindings:bool -> t -> t list

  val var_overlap : t -> t -> t list

  val ticked : t -> t

  val unticked : t -> t

  val ticked_restricted : t -> t list -> t

  val substitute : t -> subs -> t

  val uniquify :
    ?include_bindings:bool -> ?underscore:bool -> ?min:int -> t -> t
end

module Term_comparable : sig
  type t = Term.t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val sexp_of_t : t -> Sexp.t

  val t_of_sexp : Sexp.t -> t
end

module Term_set : module type of Set.Make (Term_comparable)

module Predicate : sig
  type t = string

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val sexp_of_t : t -> Sexp.t

  val t_of_sexp : Sexp.t -> t

  module Builtin : sig
    val typeof : t

    val typeof_match : t

    val step : t

    val subtype : t

    val subtype_flow : t

    val consistent : t
  end
end

module Formula : sig
  type t =
    | Not of t
    | Eq of Term.t * Term.t
    | Prop of {predicate: Predicate.t; args: Term.t list}
    | Member of {element: Term.t; collection: Term.t}
    | Subset of {sub: Term.t; super: Term.t}
  [@@deriving equal, compare, sexp]

  val to_string : t -> string

  val is_not : t -> bool

  val is_eq : t -> bool

  val is_default : t -> bool

  val is_member : t -> bool

  val is_subset : t -> bool

  val vars : t -> Term.t list

  val substitute : t -> Term.subs -> t
end

module Formula_comparable : sig
  type t = Formula.t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val sexp_of_t : t -> Sexp.t

  val t_of_sexp : Sexp.t -> t
end

module Formula_set : module type of Set.Make (Formula_comparable)

module Hint : sig
  type elem = Str of string | Strs of string list
  [@@deriving equal, compare]

  type t = {name: string; elements: elem list String.Map.t}
  [@@deriving equal, compare]

  val to_string : t -> string
end

val uniquify_formulae :
     ?minimum:int
  -> ?prev_vars:Term.t list
  -> ?underscore:bool
  -> ?ignored:Formula.t list
  -> Formula.t list
  -> hint_map:(string, string list) List.Assoc.t
  -> hint_var:string
  -> Formula.t list * Term.uniquify_map

module Rule : sig
  type t = {name: string; premises: Formula.t list; conclusion: Formula.t}
  [@@deriving equal, compare, sexp]

  val to_string : t -> string

  val is_reduction_rule : t -> bool

  val is_typing_rule : t -> bool

  val has_typing_premises : t -> bool

  val vars : t -> Term.t list

  val substitute : t -> Term.subs -> t

  val normalize_vars : t -> t
end

module Grammar : sig
  module Category : sig
    type t = {name: string; meta_var: string; terms: Term_set.t}
    [@@deriving equal, compare]

    val to_string : t -> string

    val term_vars_of : t -> string list

    val deuniquify_terms : t -> t
  end

  type t = Category.t String.Map.t [@@deriving equal, compare]

  val to_string : t -> string
end

type t =
  { grammar: Grammar.t
  ; relations: Term.t list String.Map.t
  ; rules: Rule.t String.Map.t
  ; hints: Hint.t String.Map.t }
[@@deriving equal, compare]

val to_string : t -> string

val kind_of_var : t -> string -> string option

val kind_of_op : t -> string -> string option

val is_var_kind : t -> string -> string -> bool

val is_meta_var_of : t -> string -> string -> bool

val is_const_var : t -> string -> bool

val is_op_kind : t -> string -> string -> bool

val reduction_rules_of : t -> Rule.t list

val typing_rules_of : t -> Rule.t list

val subset_categories : t -> string String.Map.t
