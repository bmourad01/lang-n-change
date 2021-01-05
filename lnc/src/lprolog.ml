open Core_kernel
module L = Language
module T = L.Term
module F = L.Formula
module R = L.Rule
module G = L.Grammar
module C = G.Category

let kind_name name =
  let name = String.uncapitalize name in
  match name with
  | "type" -> "typ"
  | "kind" -> "knd"
  | _ -> name

let cat_name (lan : L.t) name =
  let name = String.capitalize name in
  match name with
  | "Typ" -> if Map.mem lan.grammar name then name else "Type"
  | "Knd" -> if Map.mem lan.grammar name then name else "Kind"
  | _ -> name

module Sigs = struct
  module Type = struct
    type t = Var of string | Constructor of {name: string; args: t list}
    [@@deriving equal, compare, hash, sexp]

    let rec to_string ?(parens = false) = function
      | Var v -> v
      | Constructor {name; args} ->
          let s =
            Printf.sprintf "%s %s" name
              ( List.map args ~f:(to_string ~parens:true)
              |> String.concat ~sep:" " )
          in
          if parens then Printf.sprintf "(%s)" s else s

    let rec substitute t ((t', t'') as sub) =
      if equal t t' then t''
      else
        match t with
        | Var _ -> t
        | Constructor {name; args} ->
            let args = List.map args ~f:(fun t -> substitute t sub) in
            Constructor {name; args}
  end

  module Term = struct
    type t = {name: string; args: Type.t list; typ: Type.t}

    let to_string {name; args; typ} =
      let args_str =
        match args with
        | [] -> ""
        | args ->
            let args = List.map args ~f:Type.to_string in
            String.concat args ~sep:" -> " ^ " -> "
      in
      Printf.sprintf "type %s %s%s." name args_str (Type.to_string typ)
  end

  module Prop = struct
    type t = {name: string; args: Type.t list}

    let to_string {name; args} =
      let args_str =
        match args with
        | [] -> ""
        | args ->
            let args = List.map args ~f:Type.to_string in
            String.concat args ~sep:" -> " ^ " -> "
      in
      Printf.sprintf "type %s %so." name args_str
  end

  module Syntax = struct
    let v v = Type.Var v [@@inline]

    let ( @ ) name args = Type.Constructor {name; args} [@@inline]

    let ( & ) name (args, typ) = Term.{name; args; typ} [@@inline]

    let ( $ ) name args = Prop.{name; args} [@@inline]
  end

  let builtin_props =
    let open Syntax in
    let lnc_member = "lnc_member" $ [v "A"; "list" @ [v "A"]] in
    let lnc_nmember = "lnc_nmember" $ [v "A"; "list" @ [v "A"]] in
    let lnc_map_update =
      "lnc_map_update"
      $ [ "list" @ ["lnc_pair" @ [v "A"; v "B"]]
        ; v "A"
        ; v "B"
        ; "list" @ ["lnc_pair" @ [v "A"; v "B"]] ]
    in
    let lnc_map_domain =
      "lnc_map_domain"
      $ ["list" @ ["lnc_pair" @ [v "A"; v "B"]]; "list" @ [v "A"]]
    in
    let lnc_map_range =
      "lnc_map_range"
      $ ["list" @ ["lnc_pair" @ [v "A"; v "B"]]; "list" @ [v "B"]]
    in
    let lnc_map_join =
      "lnc_map_join"
      $ [ "list" @ ["lnc_pair" @ [v "A"; v "B"]]
        ; "list" @ ["lnc_pair" @ [v "A"; v "B"]]
        ; "list" @ ["lnc_pair" @ [v "A"; v "B"]] ]
    in
    let lnc_map_union =
      "lnc_map_union"
      $ [ "list" @ ["list" @ ["lnc_pair" @ [v "A"; v "B"]]]
        ; "list" @ ["lnc_pair" @ [v "A"; v "B"]]
        ; "list" @ ["lnc_pair" @ [v "A"; v "B"]] ]
    in
    let lnc_append =
      "lnc_append" $ ["list" @ [v "A"]; "list" @ [v "A"]; "list" @ [v "A"]]
    in
    let lnc_reverse = "lnc_reverse" $ ["list" @ [v "A"]; "list" @ [v "A"]] in
    let lnc_subset = "lnc_subset" $ ["list" @ [v "A"]; "list" @ [v "A"]] in
    let lnc_zip =
      "lnc_zip"
      $ [ "list" @ [v "A"]
        ; "list" @ [v "B"]
        ; "list" @ ["lnc_pair" @ [v "A"; v "B"]] ]
    in
    let lnc_join =
      "lnc_join" $ ["list" @ [v "A"]; "list" @ [v "A"]; "list" @ [v "A"]]
    in
    let lnc_union =
      "lnc_union"
      $ ["list" @ ["list" @ [v "A"]]; "list" @ [v "A"]; "list" @ [v "A"]]
    in
    let lnc_fresh = "lnc_fresh" $ [v "string"; "list" @ [v "string"]] in
    String.Map.of_alist_exn
      [ (lnc_member.name, lnc_member)
      ; (lnc_nmember.name, lnc_nmember)
      ; (lnc_map_update.name, lnc_map_update)
      ; (lnc_map_domain.name, lnc_map_domain)
      ; (lnc_map_range.name, lnc_map_range)
      ; (lnc_map_join.name, lnc_map_join)
      ; (lnc_map_union.name, lnc_map_union)
      ; (lnc_append.name, lnc_append)
      ; (lnc_reverse.name, lnc_reverse)
      ; (lnc_subset.name, lnc_subset)
      ; (lnc_zip.name, lnc_zip)
      ; (lnc_join.name, lnc_join)
      ; (lnc_union.name, lnc_union)
      ; (lnc_fresh.name, lnc_fresh) ]

  type t =
    { kinds: int String.Map.t
    ; terms: Term.t String.Map.t
    ; props: Prop.t String.Map.t }

  let to_string {kinds; terms; props} =
    let kinds_str =
      Map.to_alist kinds
      |> List.map ~f:(fun (kind, n) ->
             let n_str =
               match n with
               | 0 -> ""
               | n ->
                   let n_str =
                     List.init n ~f:(fun _ -> "type")
                     |> String.concat ~sep:" -> "
                   in
                   n_str ^ " -> "
             in
             Printf.sprintf "kind %s %stype." kind n_str)
      |> String.concat ~sep:"\n"
    in
    let terms_str =
      Map.data terms |> List.map ~f:Term.to_string |> String.concat ~sep:"\n"
    in
    let props_str =
      Map.data props |> List.map ~f:Prop.to_string |> String.concat ~sep:"\n"
    in
    [kinds_str; terms_str; props_str]
    |> List.filter ~f:(fun s -> String.is_empty s |> not)
    |> String.concat ~sep:"\n\n"

  let of_language (lan : L.t) =
    let tuple_sizes = ref Int.Set.(singleton 2) in
    (* generate needed kinds and proposition types
     * from the relations of the language *)
    let subsets = L.subset_categories lan in
    let kinds, props =
      let kind_of_var_rel pred v =
        match L.kind_of_var lan v with
        | Some kind ->
            if L.is_meta_var_of lan v kind then kind_name kind else "string"
        | None -> "string"
      in
      let init = (String.Map.empty, builtin_props) in
      Map.to_alist lan.relations
      |> List.fold ~init ~f:(fun (kinds, props) (pred, ts) ->
             let aux ts =
               let init = (kinds, []) in
               List.fold ts ~init ~f:(fun (kinds, args) t ->
                   let rec aux kinds t =
                     match t with
                     | T.Var v ->
                         let k = kind_of_var_rel pred v in
                         let k =
                           match Map.find subsets (cat_name lan k) with
                           | None -> k
                           | Some k -> kind_name k
                         in
                         (k :: kinds, Syntax.v k)
                     | T.List t ->
                         let kinds, arg = aux kinds t in
                         (kinds, Syntax.("list" @ [arg]))
                     | T.Tuple ts ->
                         let kinds, args =
                           let init = (kinds, []) in
                           List.fold ts ~init ~f:(fun (kinds, args) t ->
                               let kinds, arg = aux kinds t in
                               (kinds, args @ [arg]))
                         in
                         let len = List.length ts in
                         tuple_sizes := Set.add !tuple_sizes len;
                         let ctor =
                           match len with
                           | 2 -> "lnc_pair"
                           | n -> Printf.sprintf "lnc_%dtuple" n
                         in
                         (kinds, Syntax.(ctor @ args))
                     | _ ->
                         invalid_arg
                           (Printf.sprintf "bad arg %s in relation %s"
                              (T.to_string t) pred)
                   in
                   let kinds', arg = aux [] t in
                   let kinds' =
                     List.filter kinds' ~f:(function
                       | "string" -> false
                       | _ -> true)
                   in
                   let kinds =
                     List.fold kinds' ~init:kinds ~f:(fun kinds k ->
                         Map.set kinds k 0)
                   in
                   (kinds, arg :: args))
             in
             let kinds, args = aux ts in
             let prop = Syntax.(pred $ List.rev args) in
             let props = Map.set props pred prop in
             let props =
               (* hardcode step for lists, but assume that if we
                * have a tuple configuration then the first
                * element is the actual "list" to evaluate *)
               if String.equal pred L.Predicate.Builtin.step then
                 let subs =
                   List.map ts ~f:(fun t ->
                       match t with
                       | T.Var _ -> [(t, T.List t)]
                       | T.(Tuple (Var v :: _)) ->
                           [(T.Var v, T.(List (Var v)))]
                       | _ ->
                           invalid_arg
                             (Printf.sprintf
                                "unsupported term %s for relation %s_list"
                                (T.to_string t) pred))
                 in
                 let ts =
                   List.(
                     map (zip_exn ts subs) ~f:(fun (t, sub) ->
                         T.substitute t sub))
                 in
                 let _, args = aux ts in
                 let prop =
                   Prop.{name= pred ^ "_list"; args= List.rev args}
                 in
                 Map.set props prop.name prop
               else props
             in
             (kinds, Map.set props pred prop))
    in
    (* infer additional propositions based on
     * whether one category is a proper subset of another *)
    let props =
      Map.fold subsets ~init:props ~f:(fun ~key ~data props ->
          let key' = kind_name key in
          let data' = kind_name data in
          let args = Syntax.[v data'] in
          let prop = Syntax.(key' $ args) in
          let prop_list = Syntax.(key' ^ "_list" $ ["list" @ args]) in
          let props = Map.set props key' prop in
          Map.set props prop_list.name prop_list)
    in
    (* generate term constructor types from the grammar *)
    let aliases = Hashtbl.create (module Type) in
    let kinds, terms =
      let kinds =
        Map.data lan.grammar
        |> List.fold ~init:kinds ~f:(fun kinds C.{name; meta_var; terms} ->
               let name' = kind_name name in
               match Map.find kinds name' with
               | Some _ -> kinds
               | None -> (
                 match Map.find subsets name with
                 | None -> Map.set kinds name' 0
                 | Some _ -> kinds ))
      in
      let init = (kinds, String.Map.empty) in
      Map.data lan.grammar
      |> List.fold ~init ~f:(fun (kinds, terms') C.{name; meta_var; terms} ->
             let name' = kind_name name in
             if not (Map.mem kinds name') then (kinds, terms')
             else
               let rec aux t =
                 match t with
                 | T.Var v -> (
                   match L.kind_of_var lan v with
                   | None -> Syntax.[v "string"]
                   | Some kind ->
                       if L.is_meta_var_of lan v kind then
                         let kind' = kind_name kind in
                         if Map.mem kinds kind' then Syntax.[v kind']
                         else
                           match Map.find subsets kind with
                           | None -> Syntax.[v "string"]
                           | Some kind -> Syntax.[v (kind_name kind)]
                       else Syntax.[v "string"] )
                 | T.Str _ -> Syntax.[v "string"]
                 | T.Binding {var; body} -> Syntax.v "string" :: aux body
                 | T.List t ->
                     let t' = aux t in
                     if List.length t' > 1 then
                       invalid_arg
                         (Printf.sprintf "bad list kind %s in category %s"
                            (T.to_string t) name)
                     else Syntax.["list" @ [List.hd_exn t']]
                 | T.Tuple ts ->
                     let ts' = List.map ts ~f:aux |> List.concat in
                     let len = List.length ts' in
                     tuple_sizes := Set.add !tuple_sizes len;
                     let ctor =
                       match len with
                       | 2 -> "lnc_pair"
                       | n -> Printf.sprintf "lnc_%dtuple" n
                     in
                     Syntax.[ctor @ ts']
                 | _ ->
                     invalid_arg
                       (Printf.sprintf "invalid term %s in category %s"
                          (T.to_string t) name)
               in
               let f (kinds, terms') t =
                 match t with
                 | T.Constructor {name; args} ->
                     let name = kind_name name in
                     let args = List.map args ~f:aux |> List.concat in
                     let term = Syntax.(name & (args, v name')) in
                     (kinds, Map.set terms' name term)
                 | T.List t' ->
                     let t'' = aux t' in
                     if List.length t'' > 1 then
                       invalid_arg
                         (Printf.sprintf "bad list term %s in category %s"
                            (T.to_string t') name)
                     else
                       let typ = Syntax.("list" @ t'') in
                       Hashtbl.set aliases (Syntax.v name') typ;
                       (kinds, terms')
                 | T.Tuple ts ->
                     if not (Map.is_empty terms') then
                       invalid_arg
                         (Printf.sprintf "bad term %s in category %s"
                            (T.to_string t) name)
                     else
                       let ts' = List.map ts ~f:aux |> List.concat in
                       let len = List.length ts' in
                       tuple_sizes := Set.add !tuple_sizes len;
                       let ctor = Printf.sprintf "lnc_%dtuple" len in
                       let typ = Syntax.(ctor @ ts') in
                       Hashtbl.set aliases (Syntax.v name') typ;
                       (kinds, terms')
                 | _ -> (kinds, terms')
               in
               List.fold (Set.to_list terms) ~init:(kinds, terms') ~f)
    in
    (* substitute with aliases *)
    let kinds, terms, props =
      let init = (kinds, terms, props) in
      Hashtbl.to_alist aliases
      |> List.fold ~init ~f:(fun (kinds, terms, props) ((k, _) as sub) ->
             let kinds =
               match k with
               | Type.Var v -> Map.remove kinds v
               | _ -> kinds
             in
             let terms =
               Map.map terms ~f:(fun ({name; args; typ} as term) ->
                   let args =
                     List.map args ~f:(fun a -> Type.substitute a sub)
                   in
                   let typ = Type.substitute typ sub in
                   {term with args; typ})
             in
             let props =
               Map.map props ~f:(fun ({name; args} as prop) ->
                   let args =
                     List.map args ~f:(fun a -> Type.substitute a sub)
                   in
                   {prop with args})
             in
             (kinds, terms, props))
    in
    (* generate signatures for builtin
     * tuples since lambda-prolog doesn't
     * support declaring them anonymously *)
    let kinds, terms =
      let init = (kinds, terms) in
      Set.to_list !tuple_sizes
      |> List.fold ~init ~f:(fun (kinds, terms) n ->
             let name =
               match n with
               | 2 -> "lnc_pair"
               | n -> Printf.sprintf "lnc_%dtuple" n
             in
             let kinds = Map.set kinds name n in
             let args =
               List.init n ~f:(fun n -> Syntax.(v (Printf.sprintf "A%d" n)))
             in
             let typ = Syntax.(name @ args) in
             let term = Syntax.(name & (args, typ)) in
             let terms = Map.set terms name term in
             (kinds, terms))
    in
    (* programming variables are strings
     * but we have to wrap them in a constructor *)
    let terms =
      Map.data lan.grammar
      |> List.fold ~init:terms ~f:(fun terms' C.{name; meta_var; terms} ->
             if Set.exists terms ~f:T.is_var then
               let kind = kind_name name in
               let name = kind ^ "_var" in
               let term = Syntax.(name & ([v "string"], v kind)) in
               Map.set terms' name term
             else terms')
    in
    ({kinds; terms; props}, subsets)
end

module Term = struct
  type t =
    | Var of string
    | Str of string
    | Strcat of t * t
    | Constructor of {name: string; args: t list}
    | Cons of t * t
  [@@deriving equal, compare]

  let rec to_string = function
    | Var v -> v
    | Str s -> Printf.sprintf "\"%s\"" s
    | Strcat (t1, t2) ->
        Printf.sprintf "((%s) ^ (%s))" (to_string t1) (to_string t2)
    | Constructor {name; args} -> (
      match args with
      | [] -> name
      | args ->
          Printf.sprintf "(%s %s)" name
            (List.map args ~f:to_string |> String.concat ~sep:" ") )
    | Cons (t1, t2) ->
        Printf.sprintf "(%s :: %s)" (to_string t1) (to_string t2)

  let rec vars = function
    | Var v -> String.Set.singleton v
    | Str _ -> String.Set.empty
    | Strcat (t1, t2) -> String.Set.union (vars t1) (vars t2)
    | Constructor {name; args} ->
        List.fold args ~init:String.Set.empty ~f:(fun s t ->
            Set.union s (vars t))
    | Cons (t1, t2) -> Set.union (vars t1) (vars t2)
end

module Prop = struct
  type t =
    | Not of t
    | Eq of Term.t * Term.t
    | Prop of {name: string; args: Term.t list}
  [@@deriving equal, compare]

  let rec to_string = function
    | Not p -> Printf.sprintf "not(%s)" (to_string p)
    | Eq (t1, t2) ->
        Printf.sprintf "%s = %s" (Term.to_string t1) (Term.to_string t2)
    | Prop {name; args} -> (
      match args with
      | [] -> name
      | args ->
          Printf.sprintf "%s %s" name
            (List.map args ~f:Term.to_string |> String.concat ~sep:" ") )

  let rec vars = function
    | Not p -> vars p
    | Eq (t1, t2) -> Set.union (Term.vars t1) (Term.vars t2)
    | Prop {name; args} ->
        List.fold args ~init:String.Set.empty ~f:(fun s t ->
            Set.union s (Term.vars t))
end

module Rule = struct
  type t = {name: string; premises: Prop.t list; conclusion: Prop.t}

  let to_string {name; premises; conclusion} =
    let conclusion_str = Prop.to_string conclusion in
    let premises_str =
      match premises with
      | [] -> ""
      | premises ->
          Printf.sprintf " :- %s"
            (List.map premises ~f:Prop.to_string |> String.concat ~sep:", ")
    in
    Printf.sprintf "%s%s. %% %s" conclusion_str premises_str name
end

module Syntax = struct
  let v v = Term.Var v [@@inline]

  let ( !$ ) s = Term.Str s [@@inline]

  let ( ^^ ) t1 t2 = Term.Strcat (t1, t2) [@@inline]

  let ( @ ) name args = Term.Constructor {name; args} [@@inline]

  let ( ++ ) t1 t2 = Term.Cons (t1, t2) [@@inline]

  let ( ! ) prop = Prop.Not prop [@@inline]

  let ( = ) t1 t2 = Prop.Eq (t1, t2) [@@inline]

  let ( $ ) name args = Prop.Prop {name; args} [@@inline]

  let ( <-- ) (name, conclusion) premises =
    Rule.{name; premises; conclusion}
    [@@inline]
end

let builtin_rules =
  let open Syntax in
  let lnc_member_1 =
    ("LNC-MEMBER-1", "lnc_member" $ [v "X"; v "X" ++ v "L"]) <-- []
  in
  let lnc_member_2 =
    ("LNC-MEMBER-2", "lnc_member" $ [v "X"; v "Y" ++ v "L"])
    <-- ["lnc_member" $ [v "X"; v "L"]]
  in
  let lnc_nmember_1 =
    ("LNC-NMEMBER-1", "lnc_nmember" $ [v "X"; "nil" @ []]) <-- []
  in
  let lnc_nmember_2 =
    ("LNC-NMEMBER-2", "lnc_nmember" $ [v "X"; v "Y" ++ v "L"])
    <-- ["lnc_nmember" $ [v "X"; v "L"]]
  in
  let lnc_map_update_1 =
    ( "LNC-MAP-UPDATE-1"
    , "lnc_map_update"
      $ [ "nil" @ []
        ; v "X"
        ; v "Y"
        ; ("lnc_pair" @ [v "X"; v "Y"]) ++ ("nil" @ []) ] )
    <-- []
  in
  let lnc_map_update_2 =
    ( "LNC-MAP-UPDATE-2"
    , "lnc_map_update"
      $ [ ("lnc_pair" @ [v "X"; v "Y"]) ++ v "L"
        ; v "X"
        ; v "Y'"
        ; ("lnc_pair" @ [v "X"; v "Y'"]) ++ v "L" ] )
    <-- []
  in
  let lnc_map_update_3 =
    ( "LNC-MAP-UPDATE-3"
    , "lnc_map_update"
      $ [ ("lnc_pair" @ [v "X'"; v "Y"]) ++ v "L"
        ; v "X"
        ; v "Y'"
        ; ("lnc_pair" @ [v "X'"; v "Y"]) ++ v "L'" ] )
    <-- ["lnc_map_update" $ [v "L"; v "X"; v "Y'"; v "L'"]]
  in
  let lnc_map_domain_1 =
    ("LNC-MAP-DOMAIN-1", "lnc_map_domain" $ ["nil" @ []; "nil" @ []]) <-- []
  in
  let lnc_map_domain_2 =
    ( "LNC-MAP-DOMAIN-2"
    , "lnc_map_domain"
      $ [("lnc_pair" @ [v "X"; v "Y"]) ++ v "M"; v "X" ++ v "L"] )
    <-- []
  in
  let lnc_map_range_1 =
    ("LNC-MAP-RANGE-1", "lnc_map_range" $ ["nil" @ []; "nil" @ []]) <-- []
  in
  let lnc_map_range_2 =
    ( "LNC-MAP-RANGE-2"
    , "lnc_map_range"
      $ [("lnc_pair" @ [v "X"; v "Y"]) ++ v "M"; v "Y" ++ v "L"] )
    <-- []
  in
  let lnc_map_join_1 =
    ("LNC-MAP-JOIN-1", "lnc_map_join" $ ["nil" @ []; v "K"; v "K"]) <-- []
  in
  let lnc_map_join_2 =
    ( "LNC_MAP-JOIN-2"
    , "lnc_map_join" $ [("lnc_pair" @ [v "X"; v "Y"]) ++ v "M"; v "K"; v "M'"]
    )
    <-- [ "lnc_member" $ ["lnc_pair" @ [v "X"; v "Y"]; v "K"]
        ; "lnc_map_join" $ [v "M"; v "K"; v "M'"] ]
  in
  let lnc_map_join_3 =
    ( "LNC_MAP-JOIN-3"
    , "lnc_map_join"
      $ [ ("lnc_pair" @ [v "X"; v "Y"]) ++ v "M"
        ; v "K"
        ; ("lnc_pair" @ [v "X"; v "Y"]) ++ v "M'" ] )
    <-- [ !("lnc_member" $ ["lnc_pair" @ [v "X"; v "Y'"]; v "K"])
        ; "lnc_map_join" $ [v "M"; v "K"; v "M'"] ]
  in
  let lnc_map_union_1 =
    ("LNC-MAP-UNION-1", "lnc_map_union" $ ["nil" @ []; v "K"; v "K"]) <-- []
  in
  let lnc_map_union_2 =
    ("LNC-MAP-UNION-2", "lnc_map_union" $ [v "X" ++ v "L"; v "K"; v "M2"])
    <-- [ "lnc_map_join" $ [v "X"; v "K"; v "M1"]
        ; "lnc_map_union" $ [v "L"; v "M1"; v "M2"] ]
  in
  let lnc_append_1 =
    ("LNC-APPEND-1", "lnc_append" $ ["nil" @ []; v "K"; v "K"]) <-- []
  in
  let lnc_append_2 =
    ("LNC-APPEND-2", "lnc_append" $ [v "X" ++ v "L"; v "K"; v "X" ++ v "M"])
    <-- ["lnc_append" $ [v "L"; v "K"; v "M"]]
  in
  let lnc_reverse_1 =
    ("LNC-REVERSE-1", "lnc_reverse" $ ["nil" @ []; "nil" @ []]) <-- []
  in
  let lnc_reverse_2 =
    ("LNC-REVERSE-2", "lnc_reverse" $ [v "X" ++ v "L1"; v "L2"])
    <-- [ "lnc_reverse" $ [v "L1"; v "L3"]
        ; "lnc_append" $ [v "L3"; v "X" ++ ("nil" @ []); v "L2"] ]
  in
  let lnc_subset_1 =
    ("LNC-SUBSET-1", "lnc_subset" $ ["nil" @ []; "nil" @ []]) <-- []
  in
  let lnc_subset_2 =
    ("LNC-SUBSET-2", "lnc_subset" $ ["nil" @ []; v "Y" ++ v "L"]) <-- []
  in
  let lnc_subset_3 =
    ("LNC-SUBSET-3", "lnc_subset" $ [v "X" ++ v "L1"; v "Y" ++ v "L2"])
    <-- ["lnc_subset" $ [v "L1"; v "L2"]]
  in
  let lnc_subset_4 =
    ("LNC-SUBSET-4", "lnc_subset" $ [v "X" ++ v "L1"; v "Y" ++ v "L2"])
    <-- ["lnc_member" $ [v "X"; v "L2"]; "lnc_subset" $ [v "L1"; v "L2"]]
  in
  let lnc_zip_1 =
    ("LNC-ZIP-1", "lnc_zip" $ ["nil" @ []; "nil" @ []; "nil" @ []]) <-- []
  in
  let lnc_zip_2 =
    ( "LNC-ZIP-2"
    , "lnc_zip"
      $ [ v "X" ++ v "L1"
        ; v "Y" ++ v "L2"
        ; ("lnc_pair" @ [v "X"; v "Y"]) ++ v "M" ] )
    <-- ["lnc_zip" $ [v "L1"; v "L2"; v "M"]]
  in
  let lnc_join_1 =
    ("LNC-JOIN-1", "lnc_join" $ ["nil" @ []; v "K"; v "K"]) <-- []
  in
  let lnc_join_2 =
    ("LNC-JOIN-2", "lnc_join" $ [v "X" ++ v "L"; v "K"; v "L'"])
    <-- ["lnc_member" $ [v "X"; v "K"]; "lnc_join" $ [v "L"; v "K"; v "L'"]]
  in
  let lnc_join_3 =
    ("LNC-JOIN-3", "lnc_join" $ [v "X" ++ v "L"; v "K"; v "X" ++ v "L'"])
    <-- [ !("lnc_member" $ [v "X"; v "K"])
        ; "lnc_join" $ [v "L"; v "K"; v "L'"] ]
  in
  let lnc_union_1 =
    ("LNC-UNION-1", "lnc_union" $ ["nil" @ []; v "K"; v "K"]) <-- []
  in
  let lnc_union_2 =
    ("LNC-UNION-2", "lnc_union" $ [v "X" ++ v "L"; v "K"; v "M2"])
    <-- [ "lnc_join" $ [v "X"; v "K"; v "M1"]
        ; "lnc_union" $ [v "L"; v "M1"; v "M2"] ]
  in
  let lnc_fresh_1 =
    ("LNC-FRESH-1", "lnc_fresh" $ [!$"a"; "nil" @ []]) <-- []
  in
  let lnc_fresh_2 =
    ("LNC-FRESH-2", "lnc_fresh" $ [v "X" ^^ !$"'"; v "X" ++ v "L"]) <-- []
  in
  String.Map.of_alist_exn
    [ (lnc_member_1.name, lnc_member_1)
    ; (lnc_member_2.name, lnc_member_2)
    ; (lnc_nmember_1.name, lnc_nmember_1)
    ; (lnc_nmember_2.name, lnc_nmember_2)
    ; (lnc_map_domain_1.name, lnc_map_domain_1)
    ; (lnc_map_domain_2.name, lnc_map_domain_2)
    ; (lnc_map_range_1.name, lnc_map_range_1)
    ; (lnc_map_range_2.name, lnc_map_range_2)
    ; (lnc_map_join_1.name, lnc_map_join_1)
    ; (lnc_map_join_2.name, lnc_map_join_2)
    ; (lnc_map_join_3.name, lnc_map_join_3)
    ; (lnc_map_union_1.name, lnc_map_union_1)
    ; (lnc_map_union_2.name, lnc_map_union_2)
    ; (lnc_append_1.name, lnc_append_1)
    ; (lnc_append_2.name, lnc_append_2)
    ; (lnc_reverse_1.name, lnc_reverse_1)
    ; (lnc_reverse_2.name, lnc_reverse_2)
    ; (lnc_subset_1.name, lnc_subset_1)
    ; (lnc_subset_2.name, lnc_subset_2)
    ; (lnc_subset_3.name, lnc_subset_3)
    ; (lnc_subset_4.name, lnc_subset_4)
    ; (lnc_zip_1.name, lnc_zip_1)
    ; (lnc_zip_2.name, lnc_zip_2)
    ; (lnc_map_update_1.name, lnc_map_update_1)
    ; (lnc_map_update_2.name, lnc_map_update_2)
    ; (lnc_map_update_3.name, lnc_map_update_3)
    ; (lnc_join_1.name, lnc_join_1)
    ; (lnc_join_2.name, lnc_join_2)
    ; (lnc_join_3.name, lnc_join_3)
    ; (lnc_union_1.name, lnc_union_1)
    ; (lnc_union_2.name, lnc_union_2)
    ; (lnc_fresh_1.name, lnc_fresh_1)
    ; (lnc_fresh_2.name, lnc_fresh_2) ]

type t = {sigs: Sigs.t; rules: Rule.t String.Map.t}

let of_language (lan : L.t) =
  let sigs, subsets = Sigs.of_language lan in
  let new_wildcard wildcard =
    let v = Syntax.v ("_" ^ Int.to_string !wildcard) in
    wildcard := succ !wildcard;
    v
  in
  let fresh_var vars v t =
    let v = String.capitalize v in
    let rec aux i =
      let v' = v ^ Int.to_string i in
      if Hashtbl.mem vars v' then aux (succ i)
      else (Hashtbl.set vars v' t; Syntax.v v')
    in
    aux 0
  in
  (* generate terms along with additional propositions
   * if the term itself needs to make use of some
   * propositions to compute its result *)
  let subst_kinds = Hashtbl.create (module String) in
  let subst_list_kinds = Hashtbl.create (module String) in
  let aux_term wildcard vars rule_name depth t =
    let rec aux_term ?(is_list = false) depth t =
      match t with
      | T.Wildcard -> ([new_wildcard wildcard], [])
      | T.Nil -> (Syntax.["nil" @ []], [])
      | T.Cons (element, lst) ->
          let element, ps1 = aux_term (succ depth) element in
          let element = List.hd_exn element in
          let lst, ps2 = aux_term (succ depth) lst in
          let lst = List.hd_exn lst in
          (Syntax.[element ++ lst], ps1 @ ps2)
      | T.Var v ->
          let k = L.kind_of_var lan v in
          let def = Syntax.v (String.capitalize v) in
          let t' =
            match k with
            | None -> [def]
            | Some kind ->
                if L.is_meta_var_of lan v kind then [def]
                else if depth = 0 then
                  (* fixme: we shouldn't rely on depth of
                   * terms to infer whether we should wrap
                   * a variable in a constructor (we should
                   * look at the signatures instead) *)
                  let kind = kind_name kind in
                  Syntax.[(kind ^ "_var") @ [def]]
                else [def]
          in
          let prop =
            match k with
            | None -> []
            | Some kind ->
                let kind = kind_name kind in
                if Map.mem sigs.props kind then
                  let kind = if is_list then kind ^ "_list" else kind in
                  [Prop.Prop {name= kind; args= t'}]
                else []
          in
          (t', prop)
      | T.Str s -> (Syntax.[!$s], [])
      | T.Constructor {name; args} ->
          let arg_map =
            let name_kind = L.kind_of_op lan name in
            let name_kind = Option.value_exn name_kind in
            let c = Map.find_exn lan.grammar name_kind in
            let ts =
              Set.to_list c.terms
              |> List.find_map_exn ~f:(function
                   | T.Constructor {name= op; args= ts}
                     when String.equal name op -> Some ts
                   | _ -> None)
            in
            List.zip_exn args ts
            |> List.map ~f:(fun (t1, t2) ->
                   match t2 with
                   | T.List _ -> (t1, true)
                   | _ -> (t1, false))
          in
          let args, props =
            List.map arg_map ~f:(fun (t, is_list) ->
                aux_term (succ depth) t ~is_list)
            |> List.unzip
          in
          let args, props = (List.concat args, List.concat props) in
          (Syntax.[name @ args], props)
      | T.Binding {var; body} ->
          let ts, props = aux_term (succ depth) body in
          (Syntax.(v (String.capitalize var)) :: ts, props)
      | T.Subst {body; subst} ->
          let rec subst_kind s = function
            | T.Var v -> (
              match L.kind_of_var lan v with
              | None ->
                  invalid_arg
                    (Printf.sprintf "unknown kind of subst %s %s in rule %s"
                       s (T.to_string body) rule_name)
              | Some kind ->
                  let kind =
                    match Map.find subsets kind with
                    | None -> kind
                    | Some kind -> kind
                  in
                  (kind_name kind, not (L.is_meta_var_of lan v kind)) )
            | T.Constructor {name; _} -> (
              match L.kind_of_op lan name with
              | None ->
                  invalid_arg
                    (Printf.sprintf "unknown kind of subst %s %s in rule %s"
                       s (T.to_string body) rule_name)
              | Some kind ->
                  let kind =
                    match Map.find subsets kind with
                    | None -> kind
                    | Some kind -> kind
                  in
                  (kind_name kind, false) )
            | T.Subst {body; subst} -> subst_kind "body" body
            | _ ->
                invalid_arg
                  (Printf.sprintf "invalid subst %s term %s in rule %s" s
                     (T.to_string body) rule_name)
          in
          let body_kind, wrap = subst_kind "body" body in
          if wrap then
            invalid_arg
              (Printf.sprintf "invalid subst body term %s in rule %s"
                 (T.to_string body) rule_name)
          else
            let body', props = aux_term (succ depth) body in
            if List.length body' > 1 then
              invalid_arg
                (Printf.sprintf "invalid subst body term %s in rule %s"
                   (T.to_string body) rule_name)
            else
              let body' = List.hd_exn body' in
              let props, sub =
                match subst with
                | T.Subst_pair (term, var) ->
                    let term_kind, wrap = subst_kind "term" term in
                    let sub = fresh_var vars "Sub" None in
                    (* fixme: this is a hack *)
                    let depth' = if wrap then 0 else succ depth in
                    let terms, props' = aux_term depth' term in
                    if List.length terms > 1 then
                      invalid_arg
                        (Printf.sprintf "invalid subst term %s in rule %s"
                           (T.to_string t) rule_name)
                    else
                      let term = List.hd_exn terms in
                      let var = Syntax.(v (String.capitalize var)) in
                      let arg = Syntax.("lnc_pair" @ [term; var]) in
                      let args = [body'; arg; sub] in
                      let name =
                        Printf.sprintf "lnc_subst_%s_%s" body_kind term_kind
                      in
                      let prop = Syntax.(name $ args) in
                      Hashtbl.add_multi subst_kinds body_kind term_kind;
                      (prop :: (List.rev props' @ props), sub)
                | T.Subst_var (s, k) ->
                    let term_kind =
                      match Map.find lan.grammar k with
                      | Some _ -> kind_name k
                      | None ->
                          invalid_arg
                            (Printf.sprintf
                               "invalid kind %s for subst %s in rule %s" k
                               (T.to_string t) rule_name)
                    in
                    let sub = fresh_var vars "Sub" None in
                    let args =
                      Syntax.[body'; v (String.capitalize s); sub]
                    in
                    let name =
                      Printf.sprintf "lnc_subst_list_%s_%s" body_kind
                        term_kind
                    in
                    let prop = Syntax.(name $ args) in
                    Hashtbl.add_multi subst_kinds body_kind body_kind;
                    Hashtbl.add_multi subst_list_kinds body_kind body_kind;
                    (prop :: props, sub)
              in
              ([sub], props)
      | T.Map_update {key; value; map} ->
          let key', ps1 = aux_term (succ depth) key in
          if List.length key' > 1 then
            invalid_arg
              (Printf.sprintf "invalid map key term %s in rule %s"
                 (T.to_string key) rule_name)
          else
            let key' = List.hd_exn key' in
            let value', ps2 = aux_term (succ depth) value in
            if List.length value' > 1 then
              invalid_arg
                (Printf.sprintf "invalid map value term %s in rule %s"
                   (T.to_string value) rule_name)
            else
              let value' = List.hd_exn value' in
              let map', ps3 = aux_term (succ depth) map in
              if List.length map' > 1 then
                invalid_arg
                  (Printf.sprintf "invalid map source term %s in rule %s"
                     (T.to_string map) rule_name)
              else
                let map' = List.hd_exn map' in
                let m = fresh_var vars "Map" None in
                let prop =
                  Syntax.("lnc_map_update" $ [map'; key'; value'; m])
                in
                ([m], ps1 @ ps2 @ ps3 @ [prop])
      | T.Map_domain t ->
          let t', ps = aux_term (succ depth) t in
          if List.length t' > 1 then
            invalid_arg
              (Printf.sprintf "invalid map domain key term %s in rule %s"
                 (T.to_string t) rule_name)
          else
            let t' = List.hd_exn t' in
            let m = fresh_var vars "List" None in
            let prop = Syntax.("lnc_map_domain" $ [t'; m]) in
            ([m], ps @ [prop])
      | T.Map_range t ->
          let t', ps = aux_term (succ depth) t in
          if List.length t' > 1 then
            invalid_arg
              (Printf.sprintf "invalid map range key term %s in rule %s"
                 (T.to_string t) rule_name)
          else
            let t' = List.hd_exn t' in
            let m = fresh_var vars "List" None in
            let prop = Syntax.("lnc_map_range" $ [t'; m]) in
            ([m], ps @ [prop])
      | T.Tuple ts ->
          let ts', props =
            List.map ts ~f:(aux_term (succ depth)) |> List.unzip
          in
          let args, props = (List.concat ts', List.concat props) in
          let name =
            match List.length ts with
            | 2 -> "lnc_pair"
            | n -> Printf.sprintf "lnc_%dtuple" n
          in
          (Syntax.[name @ args], props)
      | T.List _ -> ([fresh_var vars "List" (Some t)], [])
      | T.Union ts ->
          let ts', props =
            List.map ts ~f:(aux_term (succ depth)) |> List.unzip
          in
          let ts', props = (List.concat ts', List.concat props) in
          let l = fresh_var vars "List" None in
          let t' =
            List.rev ts'
            |> List.fold_right
                 ~init:Syntax.("nil" @ [])
                 ~f:(fun t t' -> Syntax.(t ++ t'))
          in
          let prop = Syntax.("lnc_union" $ [t'; "nil" @ []; l]) in
          ([l], props @ [prop])
      | T.Map_union ts ->
          let ts', props =
            List.map ts ~f:(aux_term (succ depth)) |> List.unzip
          in
          let ts', props = (List.concat ts', List.concat props) in
          let l = fresh_var vars "List" None in
          let t' =
            List.rev ts'
            |> List.fold_right
                 ~init:Syntax.("nil" @ [])
                 ~f:(fun t t' -> Syntax.(t ++ t'))
          in
          let prop = Syntax.("lnc_map_union" $ [t'; "nil" @ []; l]) in
          ([l], props @ [prop])
      | T.Zip (t1, t2) ->
          let t1', ps1 = aux_term (succ depth) t1 in
          if List.length t1' > 1 then
            invalid_arg
              (Printf.sprintf "invalid zip term %s in rule %s"
                 (T.to_string t1) rule_name)
          else
            let t1' = List.hd_exn t1' in
            let t2', ps2 = aux_term (succ depth) t2 in
            if List.length t2' > 1 then
              invalid_arg
                (Printf.sprintf "invalid zip term %s in rule %s"
                   (T.to_string t2) rule_name)
            else
              let t2' = List.hd_exn t2' in
              let m = fresh_var vars "Map" None in
              let prop = Syntax.("lnc_zip" $ [t1'; t2'; m]) in
              ([m], ps1 @ ps2 @ [prop])
      | T.Fresh t ->
          let t', props = aux_term (succ depth) t in
          if List.length t' > 1 then
            invalid_arg
              (Printf.sprintf "invalid fresh term %s in rule %s"
                 (T.to_string t) rule_name)
          else
            let t' = List.hd_exn t' in
            let res = fresh_var vars "Fresh" None in
            let prop = Syntax.("lnc_fresh" $ [res; t']) in
            ([res], props @ [prop])
    in
    aux_term depth t
  in
  (* generate the propositions *)
  let aux_formula wildcard vars rule_name f =
    let rec aux_formula ?(depth = 0) f =
      match f with
      | F.Not f ->
          let ps = aux_formula f ~depth:1 |> List.rev in
          Syntax.(!(List.hd_exn ps)) :: List.tl_exn ps
      | F.Eq (t1, t2) ->
          let t1', ps1 = aux_term wildcard vars rule_name depth t1 in
          if List.length t1' > 1 then
            invalid_arg
              (Printf.sprintf "invalid term %s in Eq of rule %s"
                 (T.to_string t1) rule_name)
          else
            let t2', ps2 = aux_term wildcard vars rule_name depth t2 in
            if List.length t1' > 1 then
              invalid_arg
                (Printf.sprintf "invalid term %s in Eq of rule %s"
                   (T.to_string t2) rule_name)
            else
              let t1 = List.hd_exn t1' in
              let t2 = List.hd_exn t2' in
              ps1 @ ps2 @ Syntax.[t1 = t2]
      | F.Prop {predicate; args} ->
          let args, ps =
            List.map args ~f:(aux_term wildcard vars rule_name depth)
            |> List.unzip
          in
          let args, ps = (List.concat args, List.concat ps) in
          ps @ Syntax.[predicate $ args]
      | F.Member {element; collection} ->
          let t1', ps1 = aux_term wildcard vars rule_name 1 element in
          if List.length t1' > 1 then
            invalid_arg
              (Printf.sprintf "invalid term %s in Member of rule %s"
                 (T.to_string element) rule_name)
          else
            let t2', ps2 = aux_term wildcard vars rule_name 1 collection in
            if List.length t1' > 1 then
              invalid_arg
                (Printf.sprintf "invalid term %s in Member of rule %s"
                   (T.to_string collection) rule_name)
            else
              let t1 = List.hd_exn t1' in
              let t2 = List.hd_exn t2' in
              ps1 @ ps2 @ Syntax.["lnc_member" $ [t1; t2]]
      | F.Subset {sub; super} ->
          let t1', ps1 = aux_term wildcard vars rule_name 1 sub in
          if List.length t1' > 1 then
            invalid_arg
              (Printf.sprintf "invalid term %s in Subset of rule %s"
                 (T.to_string sub) rule_name)
          else
            let t2', ps2 = aux_term wildcard vars rule_name 1 super in
            if List.length t1' > 1 then
              invalid_arg
                (Printf.sprintf "invalid term %s in Subset of rule %s"
                   (T.to_string super) rule_name)
            else
              let t1 = List.hd_exn t1' in
              let t2 = List.hd_exn t2' in
              ps1 @ ps2 @ Syntax.["lnc_subset" $ [t1; t2]]
    in
    aux_formula f
  in
  (* compile the inference rules of the language *)
  let rules =
    let init = builtin_rules in
    Map.data lan.rules
    |> List.fold ~init ~f:(fun rules (R.{name; premises; conclusion} as r) ->
           let wildcard = ref 0 in
           let vars =
             R.vars r
             |> List.filter_map ~f:(function
                  | T.Var v -> Some (v, None)
                  | _ -> None)
             |> Hashtbl.of_alist_exn (module String)
           in
           let premises =
             List.map premises ~f:(aux_formula wildcard vars name)
             |> List.concat
           in
           let conclusion, premises' =
             let ps =
               aux_formula wildcard vars name conclusion |> List.rev
             in
             (List.hd_exn ps, List.tl_exn ps |> List.rev)
           in
           let premises =
             Aux.dedup_list_stable ~compare:Prop.compare
               (premises @ premises')
           in
           (* reorder premises where the predicates indicating
            * a subset kind are moved to the end *)
           let premises =
             let subset_list_prems =
               List.filter premises ~f:(function
                 | Prop.Prop {name; args}
                   when String.is_suffix name ~suffix:"_list" ->
                     let name' =
                       cat_name lan
                         (String.chop_suffix_exn name ~suffix:"_list")
                     in
                     Map.mem subsets name'
                 | _ -> false)
             in
             let removed = ref [] in
             let subset_prems =
               List.filter premises ~f:(fun p ->
                   match p with
                   | Prop.Prop {name; args} ->
                       let found =
                         List.find subset_list_prems ~f:(function
                           | Prop.Prop {name= name2; args= args2} ->
                               String.is_prefix name2 ~prefix:name
                               && List.equal Term.equal args args2
                           | _ -> false)
                       in
                       if Option.is_some found then (
                         removed := p :: !removed;
                         false )
                       else
                         let name' = cat_name lan name in
                         Map.mem subsets name'
                   | _ -> false)
             in
             let premises =
               Aux.diff_list_stable ~equal:Prop.equal premises !removed
             in
             let subset_prems = subset_list_prems @ subset_prems in
             let premises =
               Aux.diff_list_stable ~equal:Prop.equal premises subset_prems
             in
             premises @ subset_prems
           in
           let rule = Rule.{name; premises; conclusion} in
           Map.set rules name rule)
  in
  (* for categories which are proper subsets of others
   * we need to generate the rules which declare them
   * as distinct (for example, Value vs Expression
   * needs to be distinguishable for call-by-value) *)
  let rules =
    let init = rules in
    Map.data lan.grammar
    |> List.fold ~init ~f:(fun rules C.{name; meta_var; terms} ->
           if not (Map.mem subsets name) then rules
           else
             let name' = kind_name name in
             Set.to_list terms
             |> List.fold ~init:rules ~f:(fun rules t ->
                    let t = T.uniquify t in
                    match t with
                    | T.Constructor c ->
                        let rule_name =
                          Printf.sprintf "%s-%s" (String.uppercase name)
                            (String.uppercase c.name)
                        in
                        let vars = Hashtbl.create (module String) in
                        let wildcard = ref 0 in
                        let t', props =
                          aux_term wildcard vars rule_name 0 t
                        in
                        let lprops =
                          List.fold c.args ~init:[] ~f:(fun props t ->
                              match t with
                              | T.(List (Var lv))
                                when String.is_prefix lv ~prefix:meta_var
                                -> (
                                  Hashtbl.to_alist vars
                                  |> List.find_map ~f:(fun (v, t') ->
                                         match t' with
                                         | Some t' when phys_equal t t' ->
                                             Some v
                                         | _ -> None)
                                  |> function
                                  | None -> props
                                  | Some v' ->
                                      let prop =
                                        Syntax.(name' ^ "_list" $ [v v'])
                                      in
                                      prop :: props )
                              | _ -> props)
                        in
                        let props = props @ List.rev lprops in
                        if List.length t' > 1 then
                          invalid_arg
                            (Printf.sprintf
                               "invalid term %s in subset category %s"
                               (T.to_string t) name)
                        else
                          let t' = List.hd_exn t' in
                          Map.set rules rule_name
                            Syntax.((rule_name, name' $ [t']) <-- props)
                    | _ -> rules))
  in
  let rules =
    let init = rules in
    Map.keys subsets
    |> List.fold ~init ~f:(fun rules name ->
           let name' = kind_name name in
           let name_list = name' ^ "_list" in
           let rule_name =
             Printf.sprintf "%s-LIST" (String.uppercase name)
           in
           let rule1_list =
             Syntax.((rule_name ^ "-1", name_list $ ["nil" @ []]) <-- [])
           in
           let rule2_list =
             Syntax.(
               (rule_name ^ "-2", name_list $ [v "X" ++ v "L"])
               <-- [name' $ [v "X"]; name_list $ [v "L"]])
           in
           let rules = Map.set rules rule1_list.name rule1_list in
           let rules = Map.set rules rule2_list.name rule2_list in
           rules)
  in
  (* update the signatures with substitutions *)
  let sigs =
    Hashtbl.to_alist subst_kinds
    |> List.fold ~init:sigs ~f:(fun sigs (body, terms) ->
           List.fold terms ~init:sigs ~f:(fun sigs term ->
               let name = Printf.sprintf "lnc_subst_%s_%s" body term in
               let name_list =
                 Printf.sprintf "lnc_subst_%s_list_%s" body term
               in
               let arg = Sigs.Syntax.("lnc_pair" @ [v term; v "string"]) in
               let prop = Sigs.Syntax.(name $ [v body; arg; v body]) in
               let props = Map.set sigs.props name prop in
               let prop =
                 let body = Sigs.Syntax.("list" @ [v body]) in
                 Sigs.Syntax.(name_list $ [body; arg; body])
               in
               let props = Map.set props name_list prop in
               {sigs with props}))
  in
  let sigs =
    Hashtbl.to_alist subst_list_kinds
    |> List.fold ~init:sigs ~f:(fun sigs (body, terms) ->
           List.fold terms ~init:sigs ~f:(fun sigs term ->
               let name = Printf.sprintf "lnc_subst_list_%s_%s" body term in
               let name_list =
                 Printf.sprintf "lnc_subst_list_%s_list_%s" body term
               in
               let arg =
                 Sigs.Syntax.("list" @ ["lnc_pair" @ [v term; v "string"]])
               in
               let prop = Sigs.Syntax.(name $ [v body; arg; v body]) in
               let props = Map.set sigs.props name prop in
               let prop =
                 let body = Sigs.Syntax.("list" @ [v body]) in
                 Sigs.Syntax.(name_list $ [body; arg; body])
               in
               let props = Map.set props name_list prop in
               {sigs with props}))
  in
  (* generate substitution rules *)
  let rules =
    let subst_rule wildcard vars rule_name name name_list t meta_var_body
        meta_var_term var =
      let t = T.uniquify t ~min:0 ~include_bindings:true in
      let t', _ = aux_term wildcard vars rule_name 0 t in
      let t' = List.hd_exn t' in
      let prems_and_sub ignore_bindings =
        match t with
        | T.Constructor c ->
            (* fixme: this assumes that constructors in the
             * grammar will have a maximum term depth of 1 *)
            let open Option.Let_syntax in
            List.filter_map c.args ~f:(fun t ->
                match t with
                | T.Var v ->
                    let orig = String.capitalize v in
                    let%map _ =
                      Option.some_if
                        (String.is_prefix orig ~prefix:meta_var_body)
                        ()
                    in
                    let sub = orig ^ "'" in
                    ( Syntax.
                        [ name
                          $ [ v orig
                            ; "lnc_pair" @ [v meta_var_term; v var]
                            ; v sub ] ]
                    , (T.Var v, T.Var (v ^ "'"))
                    , false )
                | T.Binding {var= bvar; body= T.Var v}
                  when not ignore_bindings ->
                    let orig = String.capitalize v in
                    let%map _ =
                      Option.some_if
                        (String.is_prefix orig ~prefix:meta_var_body)
                        ()
                    in
                    let sub = orig ^ "'" in
                    let bvar' = String.capitalize bvar in
                    ( Syntax.
                        [ !(v bvar' = v var)
                        ; name
                          $ [ v orig
                            ; "lnc_pair" @ [v meta_var_term; v var]
                            ; v sub ] ]
                    , (T.Var v, T.Var (v ^ "'"))
                    , true )
                | T.Binding {var= bvar; body= T.Var v} when ignore_bindings
                  ->
                    let orig = String.capitalize v in
                    let%map _ =
                      Option.some_if
                        (String.is_prefix orig ~prefix:meta_var_body)
                        ()
                    in
                    let bvar' = String.capitalize bvar in
                    (Syntax.[v bvar' = v var], (T.Var v, T.Var v), false)
                | T.(List (Var v)) ->
                    let orig = String.capitalize v in
                    let%map _ =
                      Option.some_if
                        (String.is_prefix orig ~prefix:meta_var_body)
                        ()
                    in
                    let lv, lv' =
                      Hashtbl.to_alist vars
                      |> List.find_map ~f:(fun (lv, t') ->
                             match t' with
                             | Some t' when phys_equal t' t -> Some lv
                             | _ -> None)
                      |> function
                      | None ->
                          invalid_arg
                            (Printf.sprintf
                               "invalid list argument %s for constructor %s"
                               (T.to_string t) c.name)
                      | Some lv -> (lv, lv ^ "'")
                    in
                    ( Syntax.
                        [ name_list
                          $ [ v lv
                            ; "lnc_pair" @ [v meta_var_term; v var]
                            ; v lv' ] ]
                    , (t, T.Var lv')
                    , false )
                | _ -> None)
            |> List.unzip3
        | _ -> ([], [], [])
      in
      let premises, sub, is_bnd = prems_and_sub false in
      let r1 =
        let premises = List.concat premises in
        let t'', _ =
          Hashtbl.clear vars;
          aux_term wildcard vars rule_name 0 (T.substitute t sub)
        in
        let t'' = List.hd_exn t'' in
        Syntax.(
          (rule_name, name $ [t'; "lnc_pair" @ [v meta_var_term; v var]; t''])
          <-- premises)
      in
      if List.mem is_bnd true ~equal:Bool.equal then
        let premises, sub, _ = prems_and_sub true in
        let premises = List.concat premises in
        let t'', _ =
          Hashtbl.clear vars;
          aux_term wildcard vars rule_name 0 (T.substitute t sub)
        in
        let t'' = List.hd_exn t'' in
        let r2 =
          Syntax.(
            ( rule_name ^ "-IGNORE"
            , name $ [t'; "lnc_pair" @ [v meta_var_term; v var]; t''] )
            <-- premises)
        in
        [r1; r2]
      else [r1]
    in
    Hashtbl.to_alist subst_kinds
    |> List.fold ~init:rules ~f:(fun rules (body, terms) ->
           let body_cat = cat_name lan body in
           let f rules term =
             let name = Printf.sprintf "lnc_subst_%s_%s" body term in
             let name_list =
               Printf.sprintf "lnc_subst_%s_list_%s" body term
             in
             let term_cat = cat_name lan term in
             match
               (Map.find lan.grammar body_cat, Map.find lan.grammar term_cat)
             with
             | None, _ | _, None -> rules
             | Some bc, Some tc ->
                 let var_body =
                   let f = function
                     | T.Var v -> Some v
                     | _ -> None
                   in
                   match Set.find_map bc.terms ~f with
                   | Some var -> String.capitalize var
                   | None ->
                       invalid_arg
                         (Printf.sprintf
                            "no variable kind found for category %s" bc.name)
                 in
                 let var_term =
                   let f = function
                     | T.Var v -> Some v
                     | _ -> None
                   in
                   match Set.find_map tc.terms ~f with
                   | Some var -> String.capitalize var
                   | None ->
                       invalid_arg
                         (Printf.sprintf
                            "no variable kind found for category %s" bc.name)
                 in
                 let f rules t =
                   let suffix =
                     match t with
                     | T.Var v -> Some (String.uppercase v)
                     | T.Constructor {name; _} ->
                         Some (String.uppercase name)
                     | _ -> None
                   in
                   Option.(
                     value ~default:rules
                       ( suffix
                       >>| fun suffix ->
                       let rule_name =
                         Printf.sprintf "LNC-SUBST-%s-%s-%s"
                           (String.uppercase body) (String.uppercase term)
                           suffix
                       in
                       let meta_var_body = String.capitalize bc.meta_var in
                       let meta_var_term = String.capitalize tc.meta_var in
                       if T.is_constructor t then
                         let rs =
                           let vars = Hashtbl.create (module String) in
                           subst_rule (ref 0) vars rule_name name name_list t
                             meta_var_body meta_var_term var_body
                         in
                         List.fold rs ~init:rules
                           ~f:(fun rules (r : Rule.t) ->
                             Map.set rules r.name r)
                       else if String.equal body term then
                         let rule1 =
                           Syntax.(
                             ( rule_name ^ "-EQ"
                             , name
                               $ [ (body ^ "_var") @ [v var_body]
                                 ; "lnc_pair" @ [v meta_var_term; v var_term]
                                 ; v meta_var_body ] )
                             <-- [])
                         in
                         let rule2 =
                           let var_term' = var_term ^ "'" in
                           Syntax.(
                             ( rule_name ^ "-NEQ"
                             , name
                               $ [ (body ^ "_var") @ [v var_body]
                                 ; "lnc_pair" @ [v meta_var_body; v var_term']
                                 ; (body ^ "_var") @ [v var_body] ] )
                             <-- [!(v var_body = v var_term')])
                         in
                         Map.set
                           (Map.set rules rule1.name rule1)
                           rule2.name rule2
                       else
                         let rule =
                           Syntax.(
                             ( rule_name
                             , name
                               $ [ (body ^ "_var") @ [v var_body]
                                 ; "lnc_pair" @ [v meta_var_term; v var_term]
                                 ; (body ^ "_var") @ [v var_body] ] )
                             <-- [])
                         in
                         Map.set rules rule_name rule ))
                 in
                 let rule_name_list =
                   Printf.sprintf "LNC-SUBST-%s-LIST-%s"
                     (String.uppercase body) (String.uppercase term)
                 in
                 let rule1 =
                   Syntax.(
                     ( rule_name_list ^ "-1"
                     , name_list $ ["nil" @ []; v "_"; "nil" @ []] )
                     <-- [])
                 in
                 let rule2 =
                   Syntax.(
                     let arg = "lnc_pair" @ [v "A"; v "B"] in
                     ( rule_name_list ^ "-2"
                     , name_list $ [v "X" ++ v "L"; arg; v "X'" ++ v "L'"] )
                     <-- [ name $ [v "X"; arg; v "X'"]
                         ; name_list $ [v "L"; arg; v "L'"] ])
                 in
                 let rules =
                   Set.to_list bc.terms |> List.fold ~init:rules ~f
                 in
                 let rules = Map.set rules rule1.name rule1 in
                 let rules = Map.set rules rule2.name rule2 in
                 rules
           in
           List.fold terms ~init:rules ~f)
  in
  let rules =
    Hashtbl.to_alist subst_list_kinds
    |> List.fold ~init:rules ~f:(fun rules (body, terms) ->
           let body_cat = cat_name lan body in
           List.fold terms ~init:rules ~f:(fun rules term ->
               let term_cat = cat_name lan term in
               match
                 ( Map.find lan.grammar body_cat
                 , Map.find lan.grammar term_cat )
               with
               | None, _ | _, None -> rules
               | Some bc, Some tc ->
                   let name =
                     Printf.sprintf "lnc_subst_list_%s_%s" body term
                   in
                   let name' = Printf.sprintf "lnc_subst_%s_%s" body term in
                   let rule_name =
                     Printf.sprintf "LNC-SUBST-LIST-%s-%s"
                       (String.uppercase body) (String.uppercase term)
                   in
                   let meta_var = String.capitalize tc.meta_var in
                   let meta_var_s = meta_var ^ "1" in
                   let meta_var_s' = meta_var_s ^ "'" in
                   let meta_var_s'' = meta_var_s' ^ "'" in
                   let rule1 =
                     Syntax.(
                       ( rule_name ^ "-1"
                       , name $ [v meta_var_s; "nil" @ []; v meta_var_s] )
                       <-- [])
                   in
                   let rule2 =
                     Syntax.(
                       ( rule_name ^ "-2"
                       , name
                         $ [v meta_var_s; v "Sub" ++ v "L"; v meta_var_s'']
                       )
                       <-- [ name' $ [v meta_var_s; v "Sub"; v meta_var_s']
                           ; name $ [v meta_var_s'; v "L"; v meta_var_s''] ])
                   in
                   Map.set (Map.set rules rule1.name rule1) rule2.name rule2))
  in
  (* ad-hoc: generate evaluation context rules, which we
   * assume is hardcoded in the Context grammar category *)
  let rules =
    match Map.find lan.grammar "Context" with
    | None -> rules
    | Some ctx -> (
        let pred = L.Predicate.Builtin.step in
        match Map.find lan.relations pred with
        | None -> rules
        | Some step ->
            let step_lhs = List.hd_exn step in
            let ev =
              match step_lhs with
              | T.Var v -> v
              | T.(Tuple (Var v :: _)) -> v
              | _ ->
                  invalid_arg
                    (Printf.sprintf "invalid %s relation for %s grammar" pred
                       ctx.name)
            in
            let ev_kind =
              match L.kind_of_var lan ev with
              | Some kind -> kind
              | None ->
                  invalid_arg
                    (Printf.sprintf "invalid kind for '%s' in %s relation" ev
                       pred)
            in
            let step_term (props, no_tick) t wildcard vars rule_name =
              let f ?(suff = "") vv =
                match L.kind_of_var lan vv with
                | None -> (props, no_tick)
                | Some kind -> (
                  match Map.find subsets kind with
                  | Some _ ->
                      let kind = kind_name kind in
                      let kind = kind ^ suff in
                      let t', _ = aux_term wildcard vars rule_name 0 t in
                      let t' = List.hd_exn t' in
                      let prop = Syntax.(kind $ [t']) in
                      (prop :: props, t :: no_tick)
                  | None ->
                      if String.equal kind ev_kind then (props, t :: no_tick)
                      else if L.is_meta_var_of lan vv ctx.name then
                        let lhs = T.substitute step_lhs [(T.Var ev, t)] in
                        let rhs = T.ticked lhs in
                        let lhs, _ =
                          aux_term wildcard vars rule_name 0 lhs
                        in
                        let rhs, _ =
                          aux_term wildcard vars rule_name 0 rhs
                        in
                        let lhs = List.hd_exn lhs in
                        let rhs = List.hd_exn rhs in
                        let pred = pred ^ suff in
                        let prop = Syntax.(pred $ [lhs; rhs]) in
                        (prop :: props, no_tick)
                      else (props, t :: no_tick) )
              in
              match t with
              | T.Var vv -> f vv
              | T.(List (Var vv)) -> f vv ~suff:"_list"
              | _ -> (props, no_tick)
            in
            List.foldi (Set.to_list ctx.terms) ~init:rules
              ~f:(fun i rules t ->
                match t with
                | T.Constructor c -> (
                  match L.kind_of_op lan c.name with
                  | Some kind when String.equal ev_kind kind ->
                      let args =
                        List.mapi c.args ~f:(fun i t ->
                            match t with
                            | T.Var v -> T.Var (v ^ Int.to_string i)
                            | _ -> t)
                      in
                      let t = T.Constructor {c with args} in
                      let rule_name =
                        (* we include a "Z" at the beginning just
                         * so that these rules appear AFTER the
                         * actual reduction rules, since it assumed that
                         * no pattern-matching occurs on these rules
                         * that we are generating here *)
                        Printf.sprintf "Z-%s-%s-%s-%d"
                          (String.uppercase ctx.name)
                          (String.uppercase c.name) (String.uppercase pred) i
                      in
                      let vars = Hashtbl.create (module String) in
                      let no_tick =
                        List.filter_map c.args ~f:(function
                          | T.Binding {var; body} -> Some body
                          | _ -> None)
                      in
                      let props, no_tick =
                        let wildcard = ref 0 in
                        List.fold args ~init:([], no_tick) ~f:(fun a t ->
                            step_term a t wildcard vars rule_name)
                      in
                      let props, no_tick =
                        (List.rev props, List.rev no_tick)
                      in
                      let lhs = T.substitute step_lhs [(T.Var ev, t)] in
                      let vars =
                        List.filter (T.vars lhs) ~f:(fun t ->
                            not (List.mem no_tick t ~equal:T.equal))
                      in
                      let rhs = T.ticked_restricted lhs vars in
                      let wildcard = ref 0 in
                      let vars = Hashtbl.create (module String) in
                      let lhs', _ = aux_term wildcard vars rule_name 0 lhs in
                      (* this is a hack to prevent generation of fresh
                       * variables for terms that were not part of the step *)
                      let prop_vars_step =
                        List.filter props ~f:(function
                          | Prop.Prop {name; _} ->
                              String.is_prefix name ~prefix:pred
                          | _ -> false)
                        |> List.fold ~init:String.Set.empty ~f:(fun s p ->
                               Set.union s (Prop.vars p))
                      in
                      Hashtbl.filter_keys_inplace vars
                        ~f:(Set.mem prop_vars_step);
                      let rhs', _ = aux_term wildcard vars rule_name 0 rhs in
                      let lhs', rhs' =
                        (List.hd_exn lhs', List.hd_exn rhs')
                      in
                      let rule =
                        Syntax.((rule_name, pred $ [lhs'; rhs']) <-- props)
                      in
                      Map.set rules rule_name rule
                  | _ -> rules )
                | _ -> rules) )
  in
  (* generate "step_list" if it exists in the relations *)
  let rules =
    let pred = L.Predicate.Builtin.step in
    match Map.find lan.relations pred with
    | None -> rules
    | Some ts ->
        let pred' = pred ^ "_list" in
        let rule_name = Printf.sprintf "%s-LIST" (String.uppercase pred) in
        let rule_name_1 = rule_name ^ "-1" in
        let rule_name_2 = rule_name ^ "-2" in
        let rule_name_3 = rule_name ^ "-3" in
        let t1 = List.hd_exn ts in
        let err () =
          invalid_arg
            (Printf.sprintf "unsupported term %s for relation %s_list"
               (T.to_string t1) pred)
        in
        let ts_1 =
          match t1 with
          | T.Var _ -> T.Nil
          | T.(Tuple (Var _ :: rest)) -> T.(Tuple (T.Nil :: rest))
          | _ -> err ()
        in
        let rule1 =
          let ts_1', _ =
            let wildcard = ref 0 in
            let vars = Hashtbl.create (module String) in
            aux_term wildcard vars rule_name_1 0 ts_1
          in
          let args = ts_1' @ ts_1' in
          Syntax.((rule_name_1, pred' $ args) <-- [])
        in
        let rule2 =
          let subkind v =
            match L.kind_of_var lan v with
            | None -> v
            | Some kind -> (
                (* fixme: what if there are multiple
                 * kinds that are subsets of this kind? *)
                Map.to_alist subsets
                |> List.find_map ~f:(fun (k, k') ->
                       Option.some_if (String.equal kind k') k)
                |> function
                | None -> v
                | Some kind -> (
                  match Map.find lan.grammar kind with
                  | None -> v
                  | Some cat -> cat.meta_var ) )
          in
          let ts_2, v =
            match t1 with
            | T.Var v ->
                let v = subkind v in
                (T.(Cons (Var v, Var "L")), v)
            | T.(Tuple (Var v :: rest)) ->
                let v = subkind v in
                (T.(Tuple (Cons (Var v, Var "L") :: rest)), v)
            | _ -> err ()
          in
          let ts_2_l =
            match t1 with
            | T.Var _ -> T.Var "L"
            | T.(Tuple (Var v :: rest)) -> T.(Tuple (Var "L" :: rest))
            | _ -> err ()
          in
          let vs = T.vars ts_2 in
          let ts_2_t =
            let vs = List.filter vs ~f:(fun t -> not T.(equal t (Var v))) in
            T.ticked_restricted ts_2 vs
          in
          let ts_2_l_t = T.ticked ts_2_l in
          let wildcard = ref 0 in
          let vars = Hashtbl.create (module String) in
          let ts_2', props = aux_term wildcard vars rule_name_2 0 ts_2 in
          let ts_2_l', _ = aux_term wildcard vars rule_name_2 0 ts_2_l in
          let ts_2_t', _ = aux_term wildcard vars rule_name_2 0 ts_2_t in
          let ts_2_l_t', _ = aux_term wildcard vars rule_name_2 0 ts_2_l_t in
          let args = ts_2' @ ts_2_t' in
          let args' = ts_2_l' @ ts_2_l_t' in
          let props = props @ Syntax.[pred' $ args'] in
          Syntax.((rule_name_2, pred' $ args) <-- props)
        in
        let rule3 =
          let ts_3 =
            match t1 with
            | T.Var v -> T.(Cons (t1, Var "L"))
            | T.(Tuple ((Var v as element) :: rest)) ->
                T.(Tuple (Cons (element, Var "L") :: rest))
            | _ -> err ()
          in
          let ts_3_l =
            match t1 with
            | T.Var v -> T.Var "L"
            | T.(Tuple (Var v :: rest)) -> T.(Tuple (Var "L" :: rest))
            | _ -> err ()
          in
          let ts_3_t =
            let vs = T.vars ts_3 in
            let vs =
              List.filter vs ~f:(fun t -> not T.(equal t (Var "L")))
            in
            T.ticked_restricted ts_3 vs
          in
          let ts_3_l_t = T.ticked ts_3_l in
          let ts_3_l_tt =
            let vs = T.vars ts_3_l_t in
            let vs =
              List.filter vs ~f:(fun t -> not T.(equal t (Var "L'")))
            in
            T.ticked_restricted ts_3_l_t vs
          in
          let t1_t = T.ticked t1 in
          let wildcard = ref 0 in
          let vars = Hashtbl.create (module String) in
          let ts_3', props = aux_term wildcard vars rule_name_3 0 ts_3 in
          let t1', _ = aux_term wildcard vars rule_name_3 0 t1 in
          let t1_t', _ = aux_term wildcard vars rule_name_3 0 t1_t in
          let ts_3_t', _ = aux_term wildcard vars rule_name_3 0 ts_3_t in
          let ts_3_l_tt', _ =
            aux_term wildcard vars rule_name_3 0 ts_3_l_tt
          in
          let args = ts_3' @ ts_3_l_tt' in
          let args' = t1' @ t1_t' in
          let args'' = ts_3_t' @ ts_3_l_tt' in
          let props = props @ Syntax.[pred $ args'; pred' $ args''] in
          Syntax.((rule_name_3, pred' $ args) <-- props)
        in
        let rules = Map.set rules rule1.name rule1 in
        let rules = Map.set rules rule2.name rule2 in
        let rules = Map.set rules rule3.name rule3 in
        rules
  in
  {sigs; rules}
