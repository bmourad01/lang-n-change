open Core_kernel

module Term = struct
  type t =
    | Wildcard
    | Var of string
    | Str of string
    | Num of int
    | Constructor of {name: string; args: t list}
    | Binding of {var: string; body: t}
    | Subst of {body: t; subst: t; var: string}
    | Map_update of {key: string; value: t; map: string}
    | Map_domain of string
    | Map_range of string
    | Seq of t
    | Map of {key: string; value: t}
    | Tuple of t list [@@deriving eq, compare, sexp]

  let rec to_string = function
    | Wildcard -> "_"
    | Var v -> v
    | Str s -> Printf.sprintf "\"%s\"" s
    | Num n -> Int.to_string n
    | Constructor {name; args} ->
       let args_str = match args with
         | [] -> "."
         | args ->
            List.map args ~f:to_string
            |> String.concat ~sep:" "
            |> (fun s -> " " ^ s)
       in Printf.sprintf "(%s%s)" name args_str
    | Binding {var; body} ->
       Printf.sprintf "(%s)%s" var (to_string body)
    | Subst {body; subst; var} ->
       Printf.sprintf "%s[%s/%s]"
         (to_string body)
         (to_string subst)
         var
    | Map_update {key; value; map} ->
       Printf.sprintf "[%s => %s]%s" key (to_string value) map
    | Map_domain m -> Printf.sprintf "dom(%s)" m
    | Map_range m -> Printf.sprintf "range(%s)" m
    | Seq t -> Printf.sprintf "{%s}" (to_string t)
    | Map {key; value} ->
       Printf.sprintf "{%s => %s}" key (to_string value)
    | Tuple ts ->
       Printf.sprintf "<%s>" 
         (List.map ts ~f:to_string
          |> String.concat ~sep:", ")
end

module Term_comparable = struct
  include Term
  include Comparable.Make(Term)
end

module Term_set = Set.Make(Term_comparable)

module Formula = struct
  type t =
    | Not of t
    | Equal of Term.t * Term.t
    | Default of {
        predicate: string;
        args: Term.t list
      }
    | Member of {
        element: Term.t;
        collection: Term.t;
      } [@@deriving eq, compare, sexp]

  let rec to_string = function
    | Not f -> Printf.sprintf "not (%s)" (to_string f)
    | Equal (t1, t2) ->
       Printf.sprintf "%s = %s"
         (Term.to_string t1)
         (Term.to_string t2)
    | Default {predicate; args} ->
       let args_str =
         List.map args ~f:Term.to_string
         |> String.concat ~sep:", "
       in Printf.sprintf "%s (%s)" predicate args_str
    | Member {element; collection} ->
       Printf.sprintf "member (%s, %s)"
         (Term.to_string element)
         (Term.to_string collection)
end

module Formula_comparable = struct
  include Formula
  include Comparable.Make(Formula)
end

module Formula_set = Set.Make(Formula_comparable)

module Premise = struct
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

  let to_string = function
    | Prop f -> Formula.to_string f
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
    let premises_str = match r.premises with
      | [] -> ""
      | premises ->
         List.map premises ~f:Premise.to_string
         |> String.concat ~sep:",\n"
         |> (fun s -> s ^ "\n")
    in Printf.sprintf
         "[%s]\n%s--------------------------------------\n%s"
         r.name premises_str
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
      }

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

module Hint = struct
  type t = {
      name: string;
      elements: (string list) String.Map.t;
    }

  let to_string h =
    Printf.sprintf "# %s: %s" h.name
      (Map.to_alist h.elements
       |> List.map ~f:(fun (k, v) ->
              Printf.sprintf "%s => %s" k
                (String.concat v ~sep:" "))
       |> String.concat ~sep:" | ")
end

type t = {
    grammar: Grammar.t;
    relations: Term.t list String.Map.t;
    rules: Rule.t String.Map.t;
    hints: Hint.t String.Map.t;
  }

let to_string lan =
  let relations_str =
    if Map.is_empty lan.relations then "" else
      Map.to_alist lan.relations
      |> List.map ~f:(fun (p, ts) ->
             Printf.sprintf "%s (%s)" p
               (List.map ts ~f:Term.to_string
                |> String.concat ~sep:", "))
      |> String.concat ~sep:"\n"
      |> (fun s -> "\n\n%\n\n" ^ s)
  in 
  let hints_str =
    if Map.is_empty lan.hints then "" else
      Map.data lan.hints
      |> List.map ~f:Hint.to_string
      |> String.concat ~sep:"\n"
      |> (fun s -> "\n\n%\n\n" ^ s)
  in Printf.sprintf "%s%s\n\n%%\n\n%s%s"
       (Grammar.to_string lan.grammar)
       relations_str
       (Map.data lan.rules
        |> List.map ~f:Rule.to_string
        |> String.concat ~sep:"\n\n")
       hints_str
