open Core_kernel

module Term = struct
  type t =
    | Var of string
    | Str of string
    | Num of int
    | Constructor of {name: string; args: t list}
    | Binding of {var: string; body: t}
    | Subst of {body: t; subst: t; var: string}
    | Seq of t
    | Map of {key: string; value: t}
    | Tuple of t list [@@deriving eq, compare, sexp]

  let rec to_string = function
    | Var v -> v
    | Str s -> Printf.sprintf "\"%s\"" s
    | Num n -> Int.to_string n
    | Constructor {name; args} ->
       let args_str =
         List.map args ~f:to_string
         |> String.concat ~sep:" "
       in Printf.sprintf "(%s %s)" name args_str
    | Binding {var; body} ->
       Printf.sprintf "(%s)%s" var (to_string body)
    | Subst {body; subst; var} ->
       Printf.sprintf "%s[%s/%s]"
         (to_string body)
         (to_string subst)
         var
    | Seq t -> Printf.sprintf "{%s}" (to_string t)
    | Map {key; value} ->
       Printf.sprintf "{%s => %s}" key (to_string value)
    | Tuple ts ->
       Printf.sprintf "(%s)" 
         (List.map ts ~f:to_string
          |> String.concat ~sep:", ")
end

module Term_comparable = struct
  include Term
  include Comparable.Make(Term)
end

module Term_set = Set.Make(Term_comparable)

module Formula = struct
  type t = {
      predicate: string;
      args: Term.t list
    } [@@deriving eq, compare, sexp]

  let to_string f =
    let args_str =
      List.map f.args ~f:Term.to_string
      |> String.concat ~sep:" "
    in Printf.sprintf "%s %s" f.predicate args_str
end

module Formula_comparable = struct
  include Formula
  include Comparable.Make(Formula)
end

module Formula_set = Set.Make(Formula_comparable)

module Premise = struct
  type t =
    | Proposition of Formula.t
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

  let to_string = function
    | Proposition f -> Formula.to_string f
    | Forall {element; collection; formulae; result} ->
       let result_str = match result with
         | [] -> ""
         | result ->
            let s =
              List.map result ~f:(fun (v, t) ->
                  Printf.sprintf "%s = %s" v
                    (Term.to_string t))
              |> String.concat ~sep:", "
            in Printf.sprintf " with %s" s
       in Printf.sprintf "forall %s in %s, %s%s"
            (Term.to_string element)
            (Term.to_string collection)
            (List.map formulae ~f:Formula.to_string
             |> String.concat ~sep:", ")
            result_str
    | Find {element; collection; formulae} ->
       Printf.sprintf "find %s in %s where %s"
         (Term.to_string element)
         (Term.to_string collection)
         (List.map formulae ~f:Formula.to_string
          |> String.concat ~sep:", ")
end

module Premise_comparable = struct
  include Premise
  include Comparable.Make(Premise)
end

module Premise_set = Set.Make(Premise_comparable)

module Rule = struct
  type t = {
      name: string;
      premises: Premise.t list;
      conclusion: Formula.t;
    } [@@deriving eq, compare, sexp]

  let to_string r =
    Printf.sprintf
      "[%s]\n%s\n--------------------------------------\n%s"
      r.name
      (List.map r.premises ~f:Premise.to_string
       |> String.concat ~sep:",\n")
      (Formula.to_string r.conclusion)
end

module Rule_comparable = struct
  include Rule
  include Comparable.Make(Rule)
end

module Rule_set = Set.Make(Rule_comparable)

module Grammar = struct
  module Category = struct
    type t = {
        name: string;
        meta_var: string;
        terms: Term_set.t;
      } [@@deriving eq, compare, sexp]

    let to_string c =
      Printf.sprintf "%s %s ::= %s"
        c.name c.meta_var
        (Set.to_list c.terms
         |> List.map ~f:Term.to_string
         |> String.concat ~sep:" | ")
  end

  type t = {
      categories: Category.t String.Map.t;
    }

  let to_string g =
    Map.data g.categories
    |> List.map ~f:Category.to_string
    |> String.concat ~sep:"\n"
end

type t = {
    grammar: Grammar.t;
    rules: Rule.t String.Map.t;
  }

let to_string lan =
  Printf.sprintf "%s\n\n%s"
    (Grammar.to_string lan.grammar)
    (Map.data lan.rules
     |> List.map ~f:Rule.to_string
     |> String.concat ~sep:"\n\n")
