open Core_kernel

module Solution: sig
  type t =
    | Term_sub of Language.Term.t * Language.Term.t
    | Formula_sub of Language.Formula.t * Language.Formula.t
    | Candidate of Language.Formula.t
    | Proven of Language.Formula.t [@@deriving equal, compare, sexp]

  val to_string: t -> string
  val is_term_sub: t -> bool
  val is_formula_sub: t -> bool
  val is_candidate: t -> bool
  val is_proven: t -> bool
end

module Solution_comparable: sig
  type t = Solution.t

  val compare: t -> t -> int
  val equal: t -> t -> bool
  val sexp_of_t: t -> Sexp.t
  val t_of_sexp: Sexp.t -> t
end

module Solution_set: module type of Set.Make(Solution_comparable)

type t = Solution_set.t

val create: Language.Formula_set.t -> t

exception Incompatible_terms of Language.Term.t * Language.Term.t
exception Incompatible_formulae of Language.Formula.t * Language.Formula.t
exception Unprovable_formula of Language.Formula.t

val run: ?normalize:bool -> t -> Language.t -> t
