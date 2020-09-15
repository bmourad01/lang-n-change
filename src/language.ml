open Core_kernel

module Term = struct 
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

  let rec to_string = function
    | Wildcard -> "_"
    | Var v -> v
    | Str s -> Printf.sprintf "\"%s\"" s
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
    | Map_domain m -> Printf.sprintf "dom(%s)" (to_string m)
    | Map_range m -> Printf.sprintf "range(%s)" (to_string m)
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

  let is_str = function
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
    | Map_domain m | Map_range m -> vars_dup m
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
    | Map_domain m -> Map_domain (ticked m)
    | Map_range m -> Map_range (ticked m)
    | Seq s -> Seq (ticked s)
    | Map {key; value} -> Map {key; value = ticked value}
    | Tuple ts -> Tuple (List.map ts ~f:ticked)
    | Union ts -> Union (List.map ts ~f:ticked)
    | Zip (t1, t2) -> Zip (ticked t1, ticked t2)
    | _ -> t

  let rec unticked t =
    let f v = match String.index v '\'' with
      | None -> v
      | Some len ->
         String.sub v ~pos:0 ~len
    in
    match t with
    | Var v -> Var (f v)
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f:unticked}
    | Binding {var; body} ->
       Binding {var; body = unticked body}
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair {term; var} ->
                Subst_pair {term = unticked term; var}
             | Subst_var v -> Subst_var (f v))
       in Subst {body = unticked body; substs}
    | Map_update {key; value; map} ->
       Map_update {
           key = f key;
           value = unticked value;
           map = f map;
         }
    | Map_domain m -> Map_domain (unticked m)
    | Map_range m -> Map_range (unticked m)
    | Seq s -> Seq (unticked s)
    | Map {key; value} -> Map {key; value = unticked value}
    | Tuple ts -> Tuple (List.map ts ~f:unticked)
    | Union ts -> Union (List.map ts ~f:unticked)
    | Zip (t1, t2) -> Zip (unticked t1, unticked t2)
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
    | Map_domain m ->
       Map_domain (ticked_restricted m ts)
    | Map_range m ->
       Map_range (ticked_restricted m ts)
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
       | Map_domain m -> Map_domain (f m)
       | Map_range m -> Map_range (f m)
       | Seq s -> Seq (f s)
       | Map {key; value} -> Map {key; value = f value}
       | Tuple ts -> Tuple (List.map ts ~f)
       | Union ts -> Union (List.map ts ~f)
       | Zip (t1, t2) -> Zip (f t1, f t2)
       | _ -> t

  let uniquify_map t =
    let vars = vars_dup t in
    let vars' =
      List.fold vars ~init:[] ~f:(fun vars t ->
          if List.mem vars t ~equal
          then vars else t :: vars)
      |> List.rev
    in
    let rec aux t n = function
      | [] -> []
      | ((Var v) as x) :: xs when equal x t ->
         Var (v ^ Int.to_string n) :: aux t (succ n) xs
      | _ :: xs -> aux t n xs
    in
    List.filter_map vars' ~f:(fun t ->
        let l = aux t 1 vars in
        Option.some_if (List.length l > 1) (t, l))

  let uniquify t m =
    let var t m = match List.Assoc.find m t ~equal with
      | None -> (t, m)
      | Some ts ->
         let m = List.Assoc.remove m t ~equal in
         match List.length ts with
         | n when n > 1 ->
            (List.hd_exn ts, (t, List.tl_exn ts) :: m)
         | 0 -> (t, m)
         | _ -> (List.hd_exn ts, m)
    in
    let rec aux t m = match t with
      | Wildcard -> (t, m)
      | Var v -> var t m
      | Str _ -> (t, m)
      | Constructor {name; args} ->
         let rec aux' m = function
           | [] -> ([], m)
           | x :: xs ->
              let (x, m) = aux x m in
              let (xs, m) = aux' m xs in
              (x :: xs, m)
         in
         let (args, m) = aux' m args in
         (Constructor {name; args}, m)
      | Binding {var; body} ->
         let (body, m) = aux body m in
         (Binding {var; body}, m)
      | Subst {body; substs} ->
         let rec aux' m = function
           | [] -> ([], m)
           | x :: xs ->
              let (x, m) = match x with
                | Subst_pair {term; var} ->              
                   let (term, m) = aux term m in
                   (Subst_pair {term; var}, m)
                | Subst_var v ->
                   match var (Var v) m with
                   | (Var v, m) ->
                      (Subst_var v, m)
                   | _ -> (x, m)
              in
              let (xs, m) = aux' m xs in
              (x :: xs, m)
         in
         let (body, m) = aux body m in        
         let (substs, m) = aux' m substs in
         (Subst {body; substs}, m)
      | Map_update {key; value; map} ->
         let (key, m) = match var (Var key) m with
           | (Var v, m) -> (v, m)
           | _ -> (key, m)
         in
         let (value, m) = aux value m in
         let (map, m) = match var (Var map) m with
           | (Var v, m) -> (v, m)
           | _ -> (map, m)
         in (Map_update {key; value; map}, m)         
      | Map_domain t ->
         let (t, m) = aux t m in
         (Map_domain t, m)
      | Map_range t ->
         let (t, m) = aux t m in
         (Map_range t, m)
      | Seq t ->
         let (t, m) = aux t m in
         (Seq t, m)
      | Map {key; value} ->
         let (key, m) = match var (Var key) m with
           | (Var v, m) -> (v, m)
           | _ -> (key, m)
         in
         let (value, m) = aux value m in
         (Map {key; value}, m)
      | Tuple ts ->
         let rec aux' m = function
           | [] -> ([], m)
           | x :: xs ->
              let (x, m) = aux x m in
              let (xs, m) = aux' m xs in
              (x :: xs, m)
         in
         let (ts, m) = aux' m ts in
         (Tuple ts, m)
      | Union ts ->
         let rec aux' m = function
           | [] -> ([], m)
           | x :: xs ->
              let (x, m) = aux x m in
              let (xs, m) = aux' m xs in
              (x :: xs, m)
         in
         let (ts, m) = aux' m ts in
         (Union ts, m)
      | Zip (t1, t2) ->
         let (t1, m) = aux t1 m in
         let (t2, m) = aux t2 m in
         (Zip (t1, t2), m)
    in aux t m
end

module Term_comparable = struct
  include Term
  include Comparable.Make(Term)
end

module Term_set = Set.Make(Term_comparable)

module Predicate = struct
  type t = string

  let compare = String.compare
  let equal = String.equal
  let sexp_of_t = String.sexp_of_t
  let t_of_sexp = String.t_of_sexp

  module Builtin = struct
    let typeof = "typeof"
    let step = "step"
    let subtype = "subtype"
  end
end

module Formula = struct
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

  let rec substitute f sub = match f with
    | Not f -> Not (substitute f sub)
    | Eq (t1, t2) -> Eq (Term.substitute t1 sub, Term.substitute t2 sub)
    | Default {predicate; args} ->
       let args = List.map args ~f:(fun t -> Term.substitute t sub) in
       Default {predicate; args}
    | Member {element; collection} ->
       let element = Term.substitute element sub in
       let collection = Term.substitute collection sub in
       Member {element; collection}

  let rec args = function
    | Not f -> args f
    | Eq (t1, t2) -> [t1; t2]
    | Default {predicate; args} -> args
    | Member {element; collection} -> [element; collection]
end

let hint_vars_of_formulae fs hint_map hint_var =
  let is_hint_constructor = function
    | Term.Constructor {name; _} ->
       List.Assoc.mem hint_map name ~equal:String.equal
    | _ -> false
  in
  let constructors =
    List.map fs ~f:(fun f ->
        let rec constructors = function
          | Formula.Not f -> constructors f
          | Formula.Eq (t1, t2) ->
             List.filter [t1; t2] ~f:is_hint_constructor
          | Formula.Default {predicate; args} ->
             List.filter args ~f:is_hint_constructor
          | Formula.Member {element; collection} ->
             List.filter [element; collection] ~f:is_hint_constructor
        in constructors f)
    |> List.concat
  in
  let formula_terms =
    List.map fs ~f:(fun f ->
        let rec terms = function
          | Formula.Not f -> terms f
          | Formula.Default {predicate; args} ->
             let equal = String.equal in
             begin match List.Assoc.find hint_map predicate ~equal with
             | None -> []
             | Some hints ->
                List.filter_mapi args ~f:(fun i t ->
                    let open Option.Let_syntax in
                    let%bind var = List.nth hints i in
                    Option.some_if (equal var hint_var) t)
             end
          | _ -> []
        in terms f)
    |> List.concat
  in
  let constructor_terms =
    List.filter_map constructors ~f:(function
        | Term.Constructor {name; args} ->
           let open Option.Let_syntax in
           let equal = String.equal in
           let%map hints = List.Assoc.find hint_map name ~equal in
           List.filter_mapi args ~f:(fun i t ->
               let%bind var = List.nth hints i in
               Option.some_if (equal var hint_var) t)
        | _ -> None)
    |> List.concat
  in
  List.append
    (List.map formula_terms ~f:Term.vars_dup |> List.concat)
    (List.map constructor_terms ~f:Term.vars_dup |> List.concat)

let uniquify_map_of_formulae fs hint_map hint_var =
  let vars = hint_vars_of_formulae fs hint_map hint_var in
  let vars' =
    List.fold vars ~init:[] ~f:(fun vars t ->
        if List.mem vars t ~equal:Term.equal
        then vars else t :: vars)
    |> List.rev
  in
  let rec aux t n = function
    | [] -> []
    | ((Term.Var v) as x) :: xs when Term.equal x t ->
       Term.Var (v ^ Int.to_string n) :: aux t (succ n) xs
    | _ :: xs -> aux t n xs
  in
  List.filter_map vars' ~f:(fun t ->
      let l = aux t 1 vars in
      Option.some_if (List.length l > 1) (t, l))

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

  let substitute p sub =
    let f f = Formula.substitute f sub in
    match p with
    | Prop f' -> Prop (f f')
    | Forall {element; collection; formulae; result} ->
       let element = Term.substitute element sub in
       let collection = Term.substitute collection sub in
       let formulae = List.map formulae ~f in
       let result =
         List.map result ~f:(fun (v, t) ->
             (v, Term.substitute t sub))
       in Forall {element; collection; formulae; result}
    | Find {element; collection; formulae} ->
       let element = Term.substitute element sub in
       let collection = Term.substitute collection sub in
       let formulae = List.map formulae ~f in
       Find {element; collection; formulae}
end

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
         "[%s]\n%s--------------------------------------\n%s\n."
         r.name premises_str
         (Formula.to_string r.conclusion)

  let is_reduction_rule r = match r.conclusion with
    | Default {predicate; _} ->
       String.is_prefix predicate ~prefix:Predicate.Builtin.step
    | _ -> false

  let is_typing_rule r = match r.conclusion with
    | Default {predicate; _} ->
       String.is_prefix predicate ~prefix:Predicate.Builtin.typeof
    | _ -> false

  let vars r =
    List.map r.premises ~f:Premise.vars
    |> List.concat
    |> List.append (Formula.vars r.conclusion)
    |> List.dedup_and_sort ~compare:Term.compare

  let substitute r sub =
    let premises =
      List.map r.premises ~f:(fun p ->
          Premise.substitute p sub)
    in
    let conclusion = Formula.substitute r.conclusion sub in
    {r with premises; conclusion}
end

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

    let term_vars_of c =
      Set.to_list c.terms
      |> List.filter_map ~f:(function
             | Term.Var v -> Some v
             | _ -> None)
  end

  type t = Category.t String.Map.t

  let to_string g =
    Map.data g
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

let is_var_kind lan v category_name =
  match Map.find lan.grammar category_name with
  | None -> false
  | Some c ->
     String.is_prefix v ~prefix:c.meta_var
     || Set.exists c.terms ~f:(function
            | Term.Var prefix -> String.is_prefix v ~prefix
            | _ -> false)

let is_op_kind lan op category_name =
  match Map.find lan.grammar category_name with
  | None -> false
  | Some c ->
     Set.exists c.terms ~f:(function
         | Term.Constructor {name; _} -> String.equal name op
         | _ -> false)

let reduction_rules_of lan =
  Map.data lan.rules
  |> List.filter ~f:Rule.is_reduction_rule

let typing_rules_of lan =
  Map.data lan.rules
  |> List.filter ~f:Rule.is_typing_rule
