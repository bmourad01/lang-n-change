open Core_kernel

type t = Language.Formula_set.t

exception Incompatible_terms of Language.Term.t * Language.Term.t
exception Incompatible_formulae of Language.Formula.t * Language.Formula.t
exception Unprovable_formula of Language.Formula.t

val unify: t -> Language.t -> t
