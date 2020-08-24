open Core_kernel

module Term = struct 
  type t =
    | Wildcard
    | Var of string
    | Str of string
    | Num of int
    | Constructor of {name: string; args: t list}
    | Binding of {var: string; body: t}
    | Subst of {body: t; substs: subst list}
    | Map_update of {key: string; value: t; map: string}
    | Map_domain of string
    | Map_range of string
    | Seq of t
    | Map of {key: string; value: t}
    | Tuple of t list
    | Union of t list
    | Zip of t * t
  and subst =
    | Subst_pair of {term: t; var: string}
    | Subst_var of string [@@deriving eq, compare, sexp]

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
    | Subst {body; substs} ->
       let substs_str =
         if List.is_empty substs then "" else
           Printf.sprintf "[%s]"
             (List.map substs ~f:(function
                  | Subst_pair {term; var} ->
                     Printf.sprintf "%s/%s"
                       (to_string term) var
                  | Subst_var v -> v)
              |> String.concat ~sep:", ")
       in Printf.sprintf "%s%s" (to_string body) substs_str
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
    | Union ts ->
       Printf.sprintf "union(%s)"
         (List.map ts ~f:to_string
          |> String.concat ~sep:", ")
    | Zip (t1, t2) ->
       Printf.sprintf "zip(%s, %s)"
         (to_string t1) (to_string t2)

  let is_var = function
    | Var _ -> true
    | _ -> false

  let is_string = function
    | Str _ -> true
    | _ -> false

  let is_constructor = function
    | Constructor _ -> true
    | _ -> false

  let is_binding = function
    | Binding _ -> true
    | _ -> false

  let is_subst = function
    | Subst _ -> true
    | _ -> false

  let is_map_update = function
    | Map_update _ -> true
    | _ -> false

  let is_map_domain = function
    | Map_domain _ -> true
    | _ -> false

  let is_map_range = function
    | Map_range _ -> true
    | _ -> false

  let is_seq = function
    | Seq _ -> true
    | _ -> false

  let is_map = function
    | Map _ -> true
    | _ -> false

  let is_tuple = function
    | Tuple _ -> true
    | _ -> false

  let is_union = function
    | Union _ -> true
    | _ -> false

  let is_zip = function
    | Zip _ -> true
    | _ -> false

  let unbind t = match t with
    | Binding {var; body} -> body
    | _ -> t

  let rec unbind_rec t = match t with
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f:unbind_rec}
    | Binding {var; body} -> unbind_rec body
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair {term; var} ->
                Subst_pair {term = unbind_rec term; var}
             | Subst_var v -> Subst_var v)
       in Subst {body = unbind_rec body; substs}
    | Map_update {key; value; map} ->
       Map_update {key; value = unbind_rec value; map}
    | Seq t -> Seq (unbind_rec t)
    | Map {key; value} -> Map {key; value = unbind_rec value}
    | Tuple ts -> Tuple (List.map ts ~f:unbind_rec)
    | Union ts -> Union (List.map ts ~f:unbind_rec)
    | Zip (t1, t2) -> Zip (unbind_rec t1, unbind_rec t2)
    | _ -> t

  let rec vars_dup t = match t with
    | Var _ -> [t]
    | Constructor {name; args} ->
       List.map args ~f:vars_dup |> List.concat
    | Binding {var; body} -> vars_dup body
    | Subst {body; substs} ->
       let substs_vars =
         List.map substs ~f:(function
             | Subst_pair {term; var} -> vars_dup term
             | Subst_var v -> [Var v])
         |> List.concat
       in vars_dup body @ substs_vars
    | Map_update {key; value; map} ->
       (Var key :: vars_dup value) @ [Var map]
    | Map_domain m | Map_range m -> [Var m]
    | Seq s -> vars_dup s
    | Map {key; value} -> vars_dup value
    | Tuple ts | Union ts ->
       List.map ts ~f:vars_dup |> List.concat
    | Zip (t1, t2) -> vars_dup t1 @ vars_dup t2
    | _ -> []

  let vars t =
    vars_dup t |> List.dedup_and_sort ~compare

  let var_overlap t1 t2 =
    let vs = vars t1 in
    List.filter (vars t2) ~f:(fun v -> List.mem vs v ~equal)

  let rec ticked t = match t with
    | Var v -> Var (v ^ "'")
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f:ticked}
    | Binding {var; body} ->
       Binding {var; body = ticked body}
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair {term; var} ->
                Subst_pair {term = ticked term; var}
             | Subst_var v -> Subst_var (v ^ "'"))
       in Subst {body = ticked body; substs}
    | Map_update {key; value; map} ->
       Map_update {
           key = key ^ "'";
           value = ticked value;
           map = map ^ "'";
         }
    | Map_domain m -> Map_domain (m ^ "'")
    | Map_range m -> Map_range (m ^ "'")
    | Seq s -> Seq (ticked s)
    | Map {key; value} -> Map {key; value = ticked value}
    | Tuple ts -> Tuple (List.map ts ~f:ticked)
    | Union ts -> Union (List.map ts ~f:ticked)
    | Zip (t1, t2) -> Zip (ticked t1, ticked t2)
    | _ -> t

  let rec ticked_restricted t ts =
    let f t = ticked_restricted t ts in
    match t with
    | Var v when List.mem ts t ~equal -> Var (v ^ "'")
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f}
    | Binding {var; body} ->
       Binding {var; body = f body}
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair {term; var} ->
                Subst_pair {term = f term; var}
             | Subst_var v ->
                if List.mem ts (Var v) ~equal
                then Subst_var (v ^ "'")
                else Subst_var v)
       in Subst {body = f body; substs}
    | Map_update {key; value; map} ->
       let key =
         if List.mem ts (Var key) ~equal
         then key ^ "'" else key
       in
       let map =
         if List.mem ts (Var map) ~equal
         then map ^ "'" else map
       in Map_update {key; value = f value; map}
    | Map_domain m when List.mem ts (Var m) ~equal ->
       Map_domain (m ^ "'")
    | Map_range m when List.mem ts (Var m) ~equal ->
       Map_range (m ^ "'")
    | Seq s -> Seq (f s)
    | Map {key; value} -> Map {key; value = f value}
    | Tuple ts -> Tuple (List.map ts ~f)
    | Union ts -> Union (List.map ts ~f)
    | Zip (t1, t2) -> Zip (f t1, f t2)
    | _ -> t

  let rec substitute t sub = match List.Assoc.find sub ~equal t with
    | Some t' -> t'
    | None ->
       let f t = substitute t sub in
       match t with
       | Constructor {name; args} ->
          Constructor {name; args = List.map args ~f}
       | Binding {var; body} ->
          Binding {var; body = f body}
       | Subst {body; substs} ->
          let substs =
            List.map substs ~f:(function
                | Subst_pair {term; var} ->
                   Subst_pair {term = f term; var}
                | Subst_var v ->
                   match List.Assoc.find sub ~equal (Var v) with
                   | Some (Var v') -> Subst_var v'
                   | _ -> Subst_var v)
          in Subst {body = f body; substs}
       | Map_update {key; value; map} ->
          let key = match List.Assoc.find sub ~equal (Var key) with
            | Some (Var key') -> key'
            | _ -> key
          in
          let map = match List.Assoc.find sub ~equal (Var map) with
            | Some (Var map') -> map'
            | _ -> map
          in Map_update {key; value = f value; map}
       | Map_domain m ->
          begin match List.Assoc.find sub ~equal (Var m) with
          | Some (Var m') -> Map_domain m'
          | _ -> t
          end
       | Map_range m ->
          begin match List.Assoc.find sub ~equal (Var m) with
          | Some (Var m') -> Map_range m'
          | _ -> t
          end
       | Seq s -> Seq (f s)
       | Map {key; value} -> Map {key; value = f value}
       | Tuple ts -> Tuple (List.map ts ~f)
       | Union ts -> Union (List.map ts ~f)
       | Zip (t1, t2) -> Zip (f t1, f t2)
       | _ -> t
end

module Term_comparable = struct
  include Term
  include Comparable.Make(Term)
end

module Term_set = Set.Make(Term_comparable)

module Formula = struct
  type t =
    | Not of t
    | Eq of Term.t * Term.t
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
    | Eq (t1, t2) ->
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

  let is_not = function
    | Not _ -> true
    | _ -> false

  let is_eq = function
    | Eq _ -> true
    | _ -> false

  let is_default = function
    | Default _ -> true
    | _ -> false

  let is_member = function
    | Member _ -> true
    | _ -> false

  let rec vars = function
    | Not f -> vars f
    | Eq (t1, t2) ->
       Term.vars t1 @ Term.vars t2
       |> List.dedup_and_sort ~compare:Term.compare
    | Default {predicate; args} ->
       List.map args ~f:Term.vars
       |> List.concat
       |> List.dedup_and_sort ~compare:Term.compare
    | Member {element; collection} ->
       Term.vars element @ Term.vars collection
       |> List.dedup_and_sort ~compare:Term.compare
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

  let is_prop = function
    | Prop _ -> true
    | _ -> false

  let is_forall = function
    | Forall _ -> true
    | _ -> false

  let is_find = function
    | Find _ -> true
    | _ -> false

  let vars = function
    | Prop f -> Formula.vars f
    | Forall {element; collection; formulae; result} ->
       List.map formulae ~f:Formula.vars
       |> List.concat
       |> List.dedup_and_sort ~compare:Term.compare
    | Find {element; collection; formulae} ->
       List.map formulae ~f:Formula.vars
       |> List.concat
       |> List.dedup_and_sort ~compare:Term.compare
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

  let vars r =
    List.map r.premises ~f:Premise.vars
    |> List.concat
    |> List.append (Formula.vars r.conclusion)
    |> List.dedup_and_sort ~compare:Term.compare
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
    Printf.sprintf "%s: %s" h.name
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
      |> (fun s -> Printf.sprintf "\n\n%%\n\n%s." s)
  in Printf.sprintf "%s%s\n\n%%\n\n%s%s"
       (Grammar.to_string lan.grammar)
       relations_str
       (Map.data lan.rules
        |> List.map ~f:Rule.to_string
        |> String.concat ~sep:"\n\n")
       hints_str
