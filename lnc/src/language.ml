open Core_kernel

module Term = struct 
  type t =
    | Wildcard
    | Nil
    | Var of string
    | Str of string
    | Constructor of {name: string; args: t list}
    | Binding of {var: string; body: t}
    | Subst of {body: t; substs: subst list}
    | Map_update of {key: t; value: t; map: t}
    | Map_domain of t
    | Map_range of t
    | Cons of t * t
    | List of t
    | Map of {key: string; value: t}
    | Tuple of t list
    | Union of t list
    | Map_union of t list
    | Zip of t * t
    | Fresh of t
  and subst =
    | Subst_pair of t * string
    | Subst_var of string * string [@@deriving equal, compare, sexp]

  type subs = (t, t) List.Assoc.t
  type uniquify_map = (t, t list) List.Assoc.t

  let rec to_string = function
    | Wildcard -> "_"
    | Nil -> "nil"
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
                  | Subst_pair (term, var) ->
                     Printf.sprintf "%s/%s"
                       (to_string term) var
                  | Subst_var (v, kind) ->
                     Printf.sprintf "%s:%s" v kind)
              |> String.concat ~sep:", ")
       in Printf.sprintf "%s%s" (to_string body) substs_str
    | Map_update {key; value; map} ->
       Printf.sprintf "[%s => %s]%s"
         (to_string key) (to_string value) (to_string map)
    | Map_domain m -> Printf.sprintf "dom(%s)" (to_string m)
    | Map_range m -> Printf.sprintf "range(%s)" (to_string m)
    | Cons (element, lst) ->
       Printf.sprintf "(%s :: %s)" (to_string element) (to_string lst)
    | List t -> Printf.sprintf "[%s...]" (to_string t)
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
    | Map_union ts ->
       Printf.sprintf "map_union(%s)"
         (List.map ts ~f:to_string
          |> String.concat ~sep:", ")
    | Zip (t1, t2) ->
       Printf.sprintf "zip(%s, %s)"
         (to_string t1) (to_string t2)
    | Fresh t -> Printf.sprintf "fresh(%s)" (to_string t)

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

  let is_subst_pair = function
    | Subst_pair _ -> true
    | _ -> false

  let is_subst_var = function
    | Subst_var _ -> true
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

  let is_nil = function
    | Nil -> true
    | _ -> false

  let is_cons = function
    | Cons _ -> true
    | _ -> false

  let is_list = function
    | List _ -> true
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
  
  let is_map_union = function
    | Map_union _ -> true
    | _ -> false
  
  let is_zip = function
    | Zip _ -> true
    | _ -> false

  let is_fresh = function
    | Fresh _ -> true
    | _ -> false

  let unbind t = match t with
    | Binding {var; body} -> body
    | _ -> t

  let rec unbind_rec t = match t with
    | Wildcard
      | Nil
      | Var _
      | Str _ -> t
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f:unbind_rec}
    | Binding {var; body} -> unbind_rec body
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair (term, var) ->
                Subst_pair (unbind_rec term, var)
             | Subst_var (v, name) -> Subst_var (v, name))
       in Subst {body = unbind_rec body; substs}
    | Map_update {key; value; map} ->
       Map_update {key; value = unbind_rec value; map}
    | Map_domain t -> Map_domain (unbind_rec t)
    | Map_range t -> Map_range (unbind_rec t)
    | Cons (element, lst) -> Cons (unbind_rec element, unbind_rec lst)
    | List t -> List (unbind_rec t)
    | Map {key; value} -> Map {key; value = unbind_rec value}
    | Tuple ts -> Tuple (List.map ts ~f:unbind_rec)
    | Union ts -> Union (List.map ts ~f:unbind_rec)
    | Map_union ts -> Map_union (List.map ts ~f:unbind_rec)
    | Zip (t1, t2) -> Zip (unbind_rec t1, unbind_rec t2)
    | Fresh t -> Fresh (unbind_rec t)

  let rec vars_dup ?(include_bindings = false) t =
    let f t = vars_dup t ~include_bindings in
    match t with
    | Wildcard
      | Nil
      | Str _ -> []
    | Var _ -> [t]
    | Constructor {name; args} ->
       List.map args ~f |> List.concat
    | Binding {var; body} ->
       if include_bindings
       then Var var :: f body
       else f body
    | Subst {body; substs} ->
       let substs_vars =
         List.map substs ~f:(function
             | Subst_pair (term, var) ->
                if include_bindings
                then Var var :: f term
                else f term
             | Subst_var (v, _) -> [Var v])
         |> List.concat
       in f body @ substs_vars
    | Map_update {key; value; map} ->
       (f key) @ (f value) @ (f map)
    | Map_domain m | Map_range m -> f m
    | Cons (element, lst) ->
       List.map [element; lst] ~f |> List.concat
    | List s -> f s
    | Map {key; value} -> f value
    | Tuple ts | Union ts | Map_union ts ->
       List.map ts ~f |> List.concat
    | Zip (t1, t2) -> f t1 @ f t2
    | Fresh t -> f t

  let vars ?(include_bindings = false) t =
    vars_dup t ~include_bindings |> List.dedup_and_sort ~compare

  let var_overlap t1 t2 =
    let vs = vars t1 in
    List.filter (vars t2) ~f:(fun v -> List.mem vs v ~equal)

  let rec ticked t = match t with
    | Wildcard
      | Nil
      | Str _ -> t
    | Var v -> Var (v ^ "'")
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f:ticked}
    | Binding {var; body} ->
       Binding {var; body = ticked body}
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair (term, var) ->
                Subst_pair (ticked term, var)
             | Subst_var (v, kind) -> Subst_var (v ^ "'", kind))
       in Subst {body = ticked body; substs}
    | Map_update {key; value; map} ->
       Map_update {
           key = ticked key;
           value = ticked value;
           map = ticked map;
         }
    | Map_domain m -> Map_domain (ticked m)
    | Map_range m -> Map_range (ticked m)
    | Cons (element, lst) -> Cons (ticked element, ticked lst)
    | List s -> List (ticked s)
    | Map {key; value} -> Map {key; value = ticked value}
    | Tuple ts -> Tuple (List.map ts ~f:ticked)
    | Union ts -> Union (List.map ts ~f:ticked)
    | Map_union ts -> Map_union (List.map ts ~f:ticked)
    | Zip (t1, t2) -> Zip (ticked t1, ticked t2)
    | Fresh t -> Fresh (ticked t)

  let rec unticked t =
    let f v = match String.index v '\'' with
      | None -> v
      | Some len ->
         String.sub v ~pos:0 ~len
    in
    match t with
    | Wildcard
      | Nil
      | Str _ -> t
    | Var v -> Var (f v)
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f:unticked}
    | Binding {var; body} ->
       Binding {var; body = unticked body}
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair (term, var) ->
                Subst_pair (unticked term, var)
             | Subst_var (v, kind) -> Subst_var (f v, kind))
       in Subst {body = unticked body; substs}
    | Map_update {key; value; map} ->
       Map_update {
           key = unticked key;
           value = unticked value;
           map = unticked map;
         }
    | Map_domain m -> Map_domain (unticked m)
    | Map_range m -> Map_range (unticked m)
    | Cons (element, lst) -> Cons (unticked element, unticked lst)
    | List s -> List (unticked s)
    | Map {key; value} -> Map {key; value = unticked value}
    | Tuple ts -> Tuple (List.map ts ~f:unticked)
    | Union ts -> Union (List.map ts ~f:unticked)
    | Map_union ts -> Map_union (List.map ts ~f:unticked)
    | Zip (t1, t2) -> Zip (unticked t1, unticked t2)
    | Fresh t -> Fresh (unticked t)

  let rec ticked_restricted t ts =
    let f t = ticked_restricted t ts in
    match t with
    | Wildcard
      | Nil
      | Str _ -> t
    | Var v when List.mem ts t ~equal -> Var (v ^ "'")
    | Var _ -> t
    | Constructor {name; args} ->
       Constructor {name; args = List.map args ~f}
    | Binding {var; body} ->
       Binding {var; body = f body}
    | Subst {body; substs} ->
       let substs =
         List.map substs ~f:(function
             | Subst_pair (term, var) ->
                Subst_pair (f term, var)
             | Subst_var (v, kind) ->
                if List.mem ts (Var v) ~equal
                then Subst_var (v ^ "'", kind)
                else Subst_var (v, kind))
       in Subst {body = f body; substs}
    | Map_update {key; value; map} ->
       let key = f key in
       let value = f value in
       let map = f map in
       Map_update {key; value; map}
    | Map_domain m -> Map_domain (ticked_restricted m ts)
    | Map_range m -> Map_range (ticked_restricted m ts)
    | Cons (element, lst) -> Cons (f element, f lst)
    | List s -> List (f s)
    | Map {key; value} -> Map {key; value = f value}
    | Tuple ts -> Tuple (List.map ts ~f)
    | Union ts -> Union (List.map ts ~f)
    | Map_union ts -> Map_union (List.map ts ~f)
    | Zip (t1, t2) -> Zip (f t1, f t2)
    | Fresh t -> Fresh (f t)

  let rec substitute t sub = match List.Assoc.find sub ~equal t with
    | Some t' -> t'
    | None ->
       let f t = substitute t sub in
       match t with
       | Wildcard
         | Nil
         | Var _
         | Str _ -> t
       | Constructor {name; args} ->
          Constructor {name; args = List.map args ~f}
       | Binding {var; body} ->
          Binding {var; body = f body}
       | Subst {body; substs} ->
          let substs =
            List.map substs ~f:(function
                | Subst_pair (term, var) ->
                   Subst_pair (f term, var)
                | Subst_var (v, kind) ->
                   match List.Assoc.find sub ~equal (Var v) with
                   | Some (Var v') -> Subst_var (v', kind)
                   | _ -> Subst_var (v, kind))
          in Subst {body = f body; substs}
       | Map_update {key; value; map} ->
          let key = f key in
          let value = f value in
          let map = f map in
          Map_update {key; value; map}
       | Map_domain m -> Map_domain (f m)
       | Map_range m -> Map_range (f m)
       | Cons (element, lst) -> Cons (f element, f lst)
       | List s -> List (f s)
       | Map {key; value} -> Map {key; value = f value}
       | Tuple ts -> Tuple (List.map ts ~f)
       | Union ts -> Union (List.map ts ~f)
       | Map_union ts -> Map_union (List.map ts ~f)
       | Zip (t1, t2) -> Zip (f t1, f t2)
       | Fresh t -> Fresh (f t)

  let uniquify_map include_bindings underscore min t =
    let vars = vars_dup t ~include_bindings in
    let vars' =
      List.fold vars ~init:[] ~f:(fun vars t ->
          if List.mem vars t ~equal
          then vars else t :: vars)
      |> List.rev
    in
    let rec aux t n = function
      | [] -> []
      | ((Var v) as x) :: xs when equal x t ->
         let v =
           if underscore
           then Printf.sprintf "%s_%d" v n
           else Printf.sprintf "%s%d" v n
         in Var v :: aux t (succ n) xs
      | _ :: xs -> aux t n xs
    in
    List.filter_map vars' ~f:(fun t ->
        let l = aux t 1 vars in
        Option.some_if (List.length l > min) (t, l))

  let uniquify' ?(include_bindings = false) t m =
    let make_var t m = match List.Assoc.find m t ~equal with
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
      | Wildcard | Nil | Str _ -> (t, m)
      | Var v -> make_var t m
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
         let (var, m) =
           if include_bindings then
             match make_var (Var var) m with
             | (Var v, m) -> (v, m)
             | (_, m) -> (var, m)
           else (var, m)
         in
         let (body, m) = aux body m in
         (Binding {var; body}, m)
      | Subst {body; substs} ->
         let rec aux' m = function
           | [] -> ([], m)
           | x :: xs ->
              let (x, m) = match x with
                | Subst_pair (term, var) ->              
                   let (var, m) =
                     if include_bindings then
                       match make_var (Var var) m with
                       | (Var v, m) -> (v, m)
                       | (_, m) -> (var, m)
                     else (var, m)
                   in
                   let (term, m) = aux term m in
                   (Subst_pair (term, var), m)
                | Subst_var (v, kind) ->
                   match make_var (Var v) m with
                   | (Var v, m) ->
                      (Subst_var (v, kind), m)
                   | _ -> (x, m)
              in
              let (xs, m) = aux' m xs in
              (x :: xs, m)
         in
         let (body, m) = aux body m in        
         let (substs, m) = aux' m substs in
         (Subst {body; substs}, m)
      | Map_update {key; value; map} ->
         let (key, m) = aux key m in
         let (value, m) = aux value m in
         let (map, m) = aux map m in
         (Map_update {key; value; map}, m)         
      | Map_domain t ->
         let (t, m) = aux t m in
         (Map_domain t, m)
      | Map_range t ->
         let (t, m) = aux t m in
         (Map_range t, m)
      | Cons (element, lst) ->
         let (element, m) = aux element m in
         let (lst, m) = aux lst m in
         (Cons (element, lst), m)
      | List t ->
         let (t, m) = aux t m in
         (List t, m)
      | Map {key; value} ->
         let (key, m) = match make_var (Var key) m with
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
      | Map_union ts ->
         let rec aux' m = function
           | [] -> ([], m)
           | x :: xs ->
              let (x, m) = aux x m in
              let (xs, m) = aux' m xs in
              (x :: xs, m)
         in
         let (ts, m) = aux' m ts in
         (Map_union ts, m)
      | Zip (t1, t2) ->
         let (t1, m) = aux t1 m in
         let (t2, m) = aux t2 m in
         (Zip (t1, t2), m)
      | Fresh t ->
         let (t, m) = aux t m in
         (Fresh t, m)
    in aux t m

  let uniquify
        ?(include_bindings = false)
        ?(underscore = true)
        ?(min = 1)
        t =
    uniquify_map include_bindings underscore min t
    |> uniquify' t ~include_bindings
    |> fst [@@inline]
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
    | Prop of {
        predicate: Predicate.t;
        args: Term.t list;
      }
    | Member of {
        element: Term.t;
        collection: Term.t;
      }
    | Subset of {
        sub: Term.t;
        super: Term.t;
      } [@@deriving equal, compare, sexp]

  let rec to_string = function
    | Not f -> Printf.sprintf "not(%s)" (to_string f)
    | Eq (t1, t2) ->
       Printf.sprintf "%s = %s"
         (Term.to_string t1)
         (Term.to_string t2)
    | Prop {predicate; args} ->
       let len = List.length args in
       if Predicate.(equal predicate Builtin.typeof)
          && len = 3 then
         Printf.sprintf "%s |- %s : %s"
           (Term.to_string (List.hd_exn args))
           (Term.to_string (List.nth_exn args 1))
           (Term.to_string (List.last_exn args))
       else if Predicate.(equal predicate Builtin.step)
               && len = 2 then
         Printf.sprintf "%s --> %s"
           (Term.to_string (List.hd_exn args))
           (Term.to_string (List.last_exn args))
       else if Predicate.(equal predicate Builtin.subtype)
               && len = 2 then
         Printf.sprintf "%s <: %s"
           (Term.to_string (List.hd_exn args))
           (Term.to_string (List.last_exn args))
       else if Predicate.(equal predicate Builtin.subtype)
               && len = 3 then
         Printf.sprintf "%s |- %s <: %s"
           (Term.to_string (List.hd_exn args))
           (Term.to_string (List.nth_exn args 1))
           (Term.to_string (List.last_exn args))
       else
         let args_str =
           List.map args ~f:Term.to_string
           |> String.concat ~sep:" "
         in Printf.sprintf "%s %s" predicate args_str
    | Member {element; collection} ->
       Printf.sprintf "member %s %s"
         (Term.to_string element)
         (Term.to_string collection)
    | Subset {sub; super} ->
       Printf.sprintf "subset %s %s"
         (Term.to_string sub)
         (Term.to_string super)

  let is_not = function
    | Not _ -> true
    | _ -> false

  let is_eq = function
    | Eq _ -> true
    | _ -> false

  let is_default = function
    | Prop _ -> true
    | _ -> false

  let is_member = function
    | Member _ -> true
    | _ -> false

  let is_subset = function
    | Subset _ -> true
    | _ -> false

  let rec vars = function
    | Not f -> vars f
    | Eq (t1, t2) ->
       Term.vars t1 @ Term.vars t2
       |> List.dedup_and_sort ~compare:Term.compare
    | Prop {predicate; args} ->
       List.map args ~f:Term.vars
       |> List.concat
       |> List.dedup_and_sort ~compare:Term.compare
    | Member {element; collection} ->
       Term.vars element @ Term.vars collection
       |> List.dedup_and_sort ~compare:Term.compare
    | Subset {sub; super} ->
       Term.vars sub @ Term.vars super
       |> List.dedup_and_sort ~compare:Term.compare

  let rec substitute f sub = match f with
    | Not f -> Not (substitute f sub)
    | Eq (t1, t2) -> Eq (Term.substitute t1 sub, Term.substitute t2 sub)
    | Prop {predicate; args} ->
       let args = List.map args ~f:(fun t -> Term.substitute t sub) in
       Prop {predicate; args}
    | Member {element; collection} ->
       let element = Term.substitute element sub in
       let collection = Term.substitute collection sub in
       Member {element; collection}
    | Subset s ->
       Subset {
           sub = Term.substitute s.sub sub;
           super = Term.substitute s.super sub;
         }
end

module Formula_comparable = struct
  include Formula
  include Comparable.Make(Formula)
end

module Formula_set = Set.Make(Formula_comparable)

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
          | Formula.Prop {predicate; args} ->
             List.filter args ~f:is_hint_constructor
          | Formula.Member {element; collection} ->
             List.filter [element; collection] ~f:is_hint_constructor
          | Formula.Subset {sub; super} ->
             List.filter [sub; super] ~f:is_hint_constructor
        in constructors f)
    |> List.concat
  in
  let formula_terms =
    List.map fs ~f:(fun f ->
        let rec terms = function
          | Formula.Not f -> terms f
          | Formula.Prop {predicate; args} ->
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

let uniquify_formulae fs ~hint_map ~hint_var =
  let m = uniquify_map_of_formulae fs hint_map hint_var in
  let rec aux_ts ts m = function
    | [] -> (List.rev ts, m)
    | x :: xs ->
       let (t, m) = Term.uniquify' x m in
       aux_ts (t :: ts) m xs
  in
  let rec aux_f m = function
    | Formula.Not f ->
       let (f, m) = aux_f m f in
       (Formula.Not f, m)
    | Formula.Eq (t1, t2) ->
       let (t1, m) = Term.uniquify' t1 m in
       let (t2, m) = Term.uniquify' t2 m in
       (Formula.Eq (t1, t2), m)
    | Formula.Prop {predicate; args} ->
       let (args, m) = aux_ts [] m args in
       (Formula.Prop {predicate; args}, m)
    | Formula.Member {element; collection} ->
       let (element, m) = Term.uniquify' element m in
       let (collection, m) = Term.uniquify' collection m in
       (Formula.Member {element; collection}, m)
    | Formula.Subset {sub; super} ->
       let (sub, m) = Term.uniquify' sub m in
       let (super, m) = Term.uniquify' super m in
       (Formula.Subset {sub; super}, m)
  in
  let rec aux_fs fs m = function
    | [] -> (List.rev fs, m)
    | x :: xs ->
       let (f, m) = aux_f m x in
       aux_fs (f :: fs) m xs
  in
  let (fs, _) = aux_fs [] m fs in
  (fs, m)

module Rule = struct
  type t = {
      name: string;
      premises: Formula.t list;
      conclusion: Formula.t;
    } [@@deriving equal, compare, sexp]

  let to_string r =
    let premises_str = match r.premises with
      | [] -> ""
      | premises ->
         List.map premises ~f:Formula.to_string
         |> String.concat ~sep:",\n"
         |> (fun s -> s ^ "\n")
    in Printf.sprintf
         "[%s]\n%s--------------------------------------\n%s."
         r.name premises_str
         (Formula.to_string r.conclusion)

  let is_reduction_rule r = match r.conclusion with
    | Formula.Prop {predicate; _} ->
       Predicate.(equal predicate Builtin.step)
    | _ -> false

  let is_typing_rule r = match r.conclusion with
    | Formula.Prop {predicate; _} ->
       Predicate.(equal predicate Builtin.typeof)
    | _ -> false

  let has_typing_premises r =
    List.exists r.premises ~f:(function
        | Formula.Prop {predicate; args} ->
           Predicate.(equal predicate Builtin.typeof)
        | _ -> false)

  let vars r =
    List.map r.premises ~f:Formula.vars
    |> List.concat
    |> List.append (Formula.vars r.conclusion)
    |> List.dedup_and_sort ~compare:Term.compare

  let substitute r sub =
    let premises =
      List.map r.premises ~f:(fun p ->
          Formula.substitute p sub)
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
      } [@@deriving equal, compare]

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

  type t = Category.t String.Map.t [@@deriving equal, compare]

  let to_string g =
    Map.data g
    |> List.map ~f:Category.to_string
    |> String.concat ~sep:"\n"
end

module Hint = struct
  type t = {
      name: string;
      elements: (string list) String.Map.t;
    } [@@deriving equal, compare]

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
  } [@@deriving equal, compare]

let to_string lan =
  let relations_str =
    if Map.is_empty lan.relations then "" else
      Map.to_alist lan.relations
      |> List.map ~f:(fun (p, ts) ->
             let len = List.length ts in
             if Predicate.(equal p Builtin.typeof)
                && len = 3 then
               Printf.sprintf "%s |- %s : %s."
                 (Term.to_string (List.hd_exn ts))
                 (Term.to_string (List.nth_exn ts 1))
                 (Term.to_string (List.last_exn ts))
             else if Predicate.(equal p Builtin.step)
                     && len = 2 then
               Printf.sprintf "%s --> %s."
                 (Term.to_string (List.hd_exn ts))
                 (Term.to_string (List.last_exn ts))
             else if Predicate.(equal p Builtin.subtype)
                     && len = 2 then
               Printf.sprintf "%s <: %s"
                 (Term.to_string (List.hd_exn ts))
                 (Term.to_string (List.last_exn ts))
             else if Predicate.(equal p Builtin.subtype)
                     && len = 3 then
               Printf.sprintf "%s |- %s <: %s"
                 (Term.to_string (List.hd_exn ts))
                 (Term.to_string (List.nth_exn ts 1))
                 (Term.to_string (List.last_exn ts))
             else
               Printf.sprintf "%s %s." p
                 (List.map ts ~f:Term.to_string
                  |> String.concat ~sep:" "))
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

let kind_of_var lan v =
  let open Grammar.Category in
  Map.data lan.grammar
  |> List.find ~f:(fun {name; meta_var; terms} ->
         String.is_prefix v ~prefix:meta_var
         || Set.exists terms ~f:(function
                | Term.Var prefix -> String.is_prefix v ~prefix
                | _ -> false))
  |> Option.map ~f:(fun c -> c.name)

let kind_of_op lan op =
  let open Grammar.Category in
  let ops_of c =
    Set.to_list c.terms
    |> List.filter_map ~f:(function
           | Term.Constructor {name; _} -> Some name
           | _ -> None)
    |> String.Set.of_list
  in
  Map.data lan.grammar
  |> List.filter ~f:(fun {name; meta_var; terms} ->
         Set.exists terms ~f:(function
             | Term.Constructor {name; _} -> String.equal name op
             | _ -> false))
  |> List.fold ~init:None ~f:(fun candidate c ->
         match candidate with
         | None -> Some c
         | Some c' ->
            (* this isn't a very good heuristic *)
            let ops' = ops_of c' in
            let ops = ops_of c in
            if Set.length ops > Set.length ops'
            then Some c else candidate)
  |> Option.map ~f:(fun c -> c.name)

let is_var_kind lan v category_name =
  match Map.find lan.grammar category_name with
  | None -> false
  | Some {name; meta_var; terms} ->
     String.is_prefix v ~prefix:meta_var
     || Set.exists terms ~f:(function
            | Term.Var prefix -> String.is_prefix v ~prefix
            | _ -> false)

let is_meta_var_of lan v category_name =
  match Map.find lan.grammar category_name with
  | None -> false
  | Some {name; meta_var; terms} ->
     String.is_prefix v ~prefix:meta_var

let is_const_var lan v = match kind_of_var lan v with
  | None -> false
  | Some name ->
     match Map.find lan.grammar name with
     | None -> false
     | Some {name; meta_var; terms} ->
        not (String.is_prefix v ~prefix:meta_var)
    
let is_op_kind lan op category_name =
  match Map.find lan.grammar category_name with
  | None -> false
  | Some {name; meta_var; terms} ->
     Set.exists terms ~f:(function
         | Term.Constructor {name; _} -> String.equal name op
         | _ -> false)

let reduction_rules_of lan =
  Map.data lan.rules
  |> List.filter ~f:Rule.is_reduction_rule

let typing_rules_of lan =
  Map.data lan.rules
  |> List.filter ~f:Rule.is_typing_rule

let subset_categories lan =
  let init = String.Map.empty in
  let ctor_name = function
    | Term.Constructor {name; args} -> Some name
    | _ -> None
  in
  let module C = Grammar.Category in
  Map.data lan.grammar
  |> List.fold ~init ~f:(fun subsets C.{name; meta_var; terms} ->
         let ops =
           Set.to_list terms
           |> List.filter_map ~f:ctor_name
           |> String.Set.of_list
         in
         if Set.is_empty ops then subsets else
           Map.remove lan.grammar name
           |> Map.data
           |> List.find ~f:(fun c ->
                  let ops' =
                    Set.to_list C.(c.terms)
                    |> List.filter_map ~f:ctor_name
                    |> String.Set.of_list
                  in
                  Set.length ops < Set.length ops'
                  && Set.is_subset ops ops')
           |> (function
               | None -> subsets
               | Some c -> Map.set subsets name C.(c.name)))
