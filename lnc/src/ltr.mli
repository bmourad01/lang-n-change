open Core_kernel

module Type: sig
  type t =
    | Var of string
    | Lan
    | Syntax
    | Rule
    | Formula
    | Term
    | String
    | Bool
    | Int
    | Tuple of t list
    | Option of t
    | List of t
    | Arrow of t list [@@deriving equal]

  val to_string: t -> string
end

module Exp: sig
  module Pattern: sig
    type t =
      | Wildcard
      | Var of string
      | Str of string
      | Term of term
      | Formula of formula
      | List of t list
      | Cons of t * t
      | Tuple of t list
      | Nothing
      | Something of t
    and term =
      | Term_nil
      | Term_var of string
      | Term_var_pat of t
      | Term_str of string
      | Term_constructor of t * t
      | Term_binding of t * t
      | Term_subst of t * subst list
      | Term_map_update of t * t * t
      | Term_map_domain of t
      | Term_map_range of t
      | Term_cons of t * t
      | Term_list of t
      | Term_map of string * t
      | Term_tuple of t 
      | Term_union of t
      | Term_map_union of t
      | Term_zip of t * t
      | Term_fresh of t
    and subst =
      | Subst_pair of t * string
      | Subst_var of string
    and formula =
      | Formula_not of t
      | Formula_eq of t * t
      | Formula_prop of t * t
      | Formula_member of t * t
      | Formula_subset of t * t

    val to_string: t -> string
    val string_of_term: term -> string
    val string_of_formula: formula -> string
  end
  
  type t =
    (* builtin *)
    | Self
    | Unify of {
        normalize: bool;
        term_subs: t;
        formula_subs: t;
        candidates: t;
        proven: t;
      }
    (* variable operations *)
    | Var of string
    (* string operations *)
    | Str of string
    | Str_concat of t * t
    | Uppercase of t
    | Lowercase of t
    (* integer operations *)
    | Int of int
    | Int_str of t
    (* boolean operations *)
    | Bool_exp of boolean
    (* control operations *)
    | Let of {
        recursive: bool;
        names: string list;
        args: (string * Type.t) list;
        ret: Type.t option;
        exp: t;
        body: t;
      }
    | Apply of t * t list
    | Ite of t * t * t
    | Seq of t * t
    | Select of {
        keep: bool;
        field: t;
        pattern: Pattern.t;
        body: t;
      }
    | Match of {
        exp: t;
        cases: (Pattern.t * t) list;
      }
    (* tuple operations *)
    | Tuple of t list
    (* list operations *)
    | List of t list
    | Cons of t * t
    | Head of t
    | Tail of t
    | Last of t
    | Nth of t * t
    | List_concat of t
    | Rev of t
    | Dedup of t
    | Append of t * t
    | Diff of t * t
    | Intersect of t * t
    | Zip of t * t
    | Assoc of t * t
    | Interleave_pairs of t
    | Length of t
    (* option operations *)
    | Nothing
    | Something of t
    | Option_get of t
    (* term operations *)
    | New_term of term
    | Vars_of of t
    | Fresh_var of string
    | Unbind of t
    | Bound_of of t
    | Substitute of t * t
    | Var_overlap of t * t
    | Ticked of t
    | Ticked_restricted of t * t
    (* grammar operations *)
    | New_syntax of {
        extend: bool;
        name: string;
        meta_var: string;
        terms: t list;
      }
    | Set_syntax_terms of {
        name: string;
        terms: t;
      }
    | Remove_syntax of string
    | Meta_var_of of string
    | Syntax_terms_of of string
    (* relation operations *)
    | New_relation of string * t
    | Relations_of
    | Set_relations of t
    | Remove_relation of string
    (* formula operations *)
    | New_formula of formula
    | Uniquify_formulae of {
        formulae: t;
        ignored_formulae: t;
        hint_map: t;
        hint_var: string;
      }
    (* rule operations *)
    | New_rule of {
        name: t;
        premises: t list;
        conclusion: t;
      }
    | Rule_name of t
    | Rule_premises of t
    | Rule_conclusion of t
    | Rules_of
    | Add_rule of t
    | Add_rules of t
    | Set_rules of t
    (* hint operations *)
    | New_hint of {
        extend: bool;
        name: string;
        elements: (string * string list) list;
      }
    | Lookup_hint of string
  and boolean =
    | Bool of bool
    | Not of t
    | And of t * t
    | Or of t * t
    | Eq of t * t
    | Lt of t * t
    | Gt of t * t
    | Is_member of t * t
    | Is_nothing of t
    | Is_something of t
    | Is_empty of t
    | Is_var of t
    | Is_const_var of t
    | Is_str of t
    | Is_constructor of t
    | Is_binding of t
    | Is_subst of t
    | Is_list of t
    | Is_map of t
    | Is_tuple of t
    | Is_var_kind of t * string
    | Is_op_kind of t * string
    | Has_syntax of string
    | Starts_with of t * t
    | Ends_with of t * t
  and term = 
    | Term_nil
    | Term_var of string
    | Term_var_exp of t
    | Term_str of string
    | Term_constructor of t * t
    | Term_binding of t * t
    | Term_subst of t * subst list
    | Term_map_update of t * t * t
    | Term_map_domain of t
    | Term_map_range of t
    | Term_cons of t * t
    | Term_list of t
    | Term_map of string * t
    | Term_tuple of t
    | Term_union of t
    | Term_map_union of t
    | Term_zip of t * t
    | Term_fresh of t
  and subst =
    | Subst_pair of t * string
    | Subst_var of string * string
  and formula =
    | Formula_not of t
    | Formula_eq of t * t
    | Formula_prop of t * t
    | Formula_member of t * t
    | Formula_subset of t * t

  val to_string: t -> string
  val string_of_boolean: boolean -> string
  val string_of_term: term -> string
  val string_of_subst: subst -> string
  val string_of_formula: formula -> string
end

val generate_caml: Exp.t -> string
