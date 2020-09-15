open Core_kernel

module Term: sig
  type t =
    | Wildcard
    | Var of string
    | Str of string
    | Constructor of {name: string; args: t list}
    | Binding of {var: string; body: t}
    | Subst of {body: t; substs: subst list}
    | Map_update of {key: string; value: t; map: string}
    | Map_domain of t
    | Map_range of t
    | Seq of t
    | Map of {key: string; value: t}
    | Tuple of t list
    | Union of t list
    | Zip of t * t
  and subst =
    | Subst_pair of {term: t; var: string}
    | Subst_var of string [@@deriving eq, compare, sexp]

  val to_string: t -> string
  val is_var: t -> bool
  val is_str: t -> bool
  val is_constructor: t -> bool
  val is_binding: t -> bool
  val is_subst: t -> bool
  val is_map_update: t -> bool
  val is_map_domain: t -> bool
  val is_map_range: t -> bool
  val is_seq: t -> bool
  val is_map: t -> bool
  val is_tuple: t -> bool
  val is_union: t -> bool
  val is_zip: t -> bool
  val unbind: t -> t
  val unbind_rec: t -> t
  val vars_dup: t -> t list
  val vars: t -> t list
  val var_overlap: t -> t -> t list
  val ticked: t -> t
  val unticked: t -> t
  val ticked_restricted: t -> t list -> t
  val substitute: t -> (t * t) list -> t 
end

module Term_comparable: sig
  type t = Term.t

  val compare: t -> t -> int
  val equal: t -> t -> bool
  val sexp_of_t: t -> Sexp.t
  val t_of_sexp: Sexp.t -> t
end

module Term_set: module type of Set.Make(Term_comparable)

module Predicate: sig
  type t = string

  val compare: t -> t -> int
  val equal: t -> t -> bool
  val sexp_of_t: t -> Sexp.t
  val t_of_sexp: Sexp.t -> t

  module Builtin: sig
    val typeof: t
    val step: t
    val subtype: t
  end
end

module Formula: sig
  type t =
    | Not of t
    | Eq of Term.t * Term.t
    | Default of {
        predicate: Predicate.t;
        args: Term.t list
      }
    | Member of {
        element: Term.t;
        collection: Term.t;
      } [@@deriving eq, compare, sexp]

  val to_string: t -> string
  val is_not: t -> bool
  val is_eq: t -> bool
  val is_default: t -> bool
  val is_member: t -> bool
  val vars: t -> Term.t list
  val substitute: t -> (Term.t * Term.t) list -> t
  val args: t -> Term.t list
end

module Premise: sig
  type t =
    | Prop of Formula.t
    | Forall of {
        element: Term.t;
        collection: Term.t;
        formulae: Formula.t list;
        result: (string * Term.t) list;
      }
    | Find of {
        element: Term.t;
        collection: Term.t;
        formulae: Formula.t list;
      } [@@deriving eq, compare, sexp]

  val to_string: t -> string
  val is_prop: t -> bool
  val is_forall: t -> bool
  val is_find: t -> bool
  val vars: t -> Term.t list
  val substitute: t -> (Term.t * Term.t) list -> t
end

module Rule: sig
  type t = {
      name: string;
      premises: Premise.t list;
      conclusion: Formula.t;
    } [@@deriving eq, compare, sexp]

  val to_string: t -> string
  val is_reduction_rule: t -> bool
  val is_typing_rule: t -> bool
  val vars: t -> Term.t list
  val substitute: t -> (Term.t * Term.t) list -> t
end

module Grammar: sig
  module Category: sig
    type t = {
        name: string;
        meta_var: string;
        terms: Term_set.t;
      }

    val to_string: t -> string
    val term_vars_of: t -> string list
  end

  type t = Category.t String.Map.t

  val to_string: t -> string
end

module Hint: sig
  type t = {
      name: string;
      elements: (string list) String.Map.t;
    }

  val to_string: t -> string
end

type t = {
    grammar: Grammar.t;
    relations: Term.t list String.Map.t;
    rules: Rule.t String.Map.t;
    hints: Hint.t String.Map.t;
  }

val to_string: t -> string
val is_var_kind: t -> string -> string -> bool
val is_op_kind: t -> string -> string -> bool
val reduction_rules_of: t -> Rule.t list
val typing_rules_of: t -> Rule.t list
