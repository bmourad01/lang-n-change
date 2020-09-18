open Core_kernel

module L = Language
module T = L.Term
module F = L.Formula
module R = L.Rule
module G = L.Grammar
module C = G.Category

let kind_name name =
  let name = String.lowercase name in
  match name with
  | "type" -> "typ"
  | "kind" -> "knd"
  | _ -> name

module Sigs = struct
  module Term = struct
    type t = {
        name: string; 
        args: string list;
        typ: string;
      }
    
    let to_string {name; args; typ} =
      let args_str = match args with
        | [] -> ""
        | args ->
           (String.concat args ~sep:" -> ") ^ " -> "
      in Printf.sprintf "type %s %s%s." name args_str typ
  end

  module Prop = struct
    type t = {
        name: string;
        args: string list;
      }
    
    let to_string {name; args} =
      let args_str = match args with
        | [] -> ""
        | args ->
           (String.concat args ~sep:" -> ") ^ " -> "
      in Printf.sprintf "type %s %so." name args_str
  end

  let builtin_props =
    let lnc_subst =
      Prop.{
          name = "lnc_subst";
          args = ["A"; "lnc_pair A string"; "A"];
      } in
    let lnc_member =
      Prop.{
          name = "lnc_member";
          args = ["A"; "list A"];
      } in
    let lnc_map_update =
      Prop.{
          name = "lnc_map_update";
          args = ["A"; "B"; "list (lnc_pair A B)"; "list (lnc_pair A B)"];
      } in
    let lnc_map_domain =
      Prop.{
          name = "lnc_map_domain";
          args = ["list (lnc_pair A B)"; "list A"];
      } in
    let lnc_map_range =
      Prop.{
          name = "lnc_map_range";
          args = ["list (lnc_pair A B)"; "list A"];
      } in
    let lnc_zip =
      Prop.{
          name = "lnc_zip";
          args = ["list A"; "list B"; "list (lnc_pair A B)"];
      } in
    String.Map.of_alist_exn
      [(lnc_subst.name, lnc_subst);
       (lnc_member.name, lnc_member);
       (lnc_map_update.name, lnc_map_update);
       (lnc_map_domain.name, lnc_map_domain);
       (lnc_map_range.name, lnc_map_range);
       (lnc_zip.name, lnc_zip);
       ]

  type t = {
      kinds: int String.Map.t;
      terms: Term.t String.Map.t;
      props: Prop.t String.Map.t;
    }

  let to_string {kinds; terms; props} =
    let kinds_str =
      Map.to_alist kinds
      |> List.map ~f:(fun (kind, n) ->
             let n_str = match n with
               | 0 -> ""
               | n ->
                  let n_str =
                    List.init n ~f:(fun _ -> "type")
                    |> String.concat ~sep:" -> "
                  in n_str ^ " -> "
             in Printf.sprintf "kind %s %stype." kind n_str)
      |> String.concat ~sep:"\n"
    in
    let terms_str =
      Map.data terms
      |> List.map ~f:Term.to_string
      |> String.concat ~sep:"\n"
    in
    let props_str =
      Map.data props
      |> List.map ~f:Prop.to_string
      |> String.concat ~sep:"\n"
    in
    [kinds_str; terms_str; props_str]
    |> List.filter ~f:(fun s -> String.is_empty s |> not)
    |> String.concat  ~sep:"\n\n"

  let of_language (lan: L.t) =
    let tuple_sizes = ref Int.Set.empty in
    (* generate needed kinds and proposition types
     * from the relations of the language *)
    let (kinds, props) =
      let kind_of_var_rel pred v = match L.kind_of_var lan v with
        | Some kind ->
           if L.is_meta_var_of lan v kind
           then kind_name kind
           else "string"
        | None ->
           invalid_arg
             (Printf.sprintf "bad var %s in relation %s" v pred)
      in
      let init = (String.Map.empty, builtin_props) in
      Map.to_alist lan.relations
      |> List.fold ~init ~f:(fun (kinds, props) (pred, ts) ->
             let (kinds, args) =
               let init = (kinds, []) in
               List.fold ts ~init ~f:(fun (kinds, args) t ->
                   let rec aux kinds t =  match t with
                     | T.Var v ->
                        let k = kind_of_var_rel pred v in
                        (k :: kinds, k)
                     | T.List t ->
                        let (kinds, arg) = aux kinds t in
                        (kinds, Printf.sprintf "(list %s)" arg)
                     | T.Map {key; value} ->
                        let key = kind_of_var_rel pred key in
                        let (kinds, arg) = aux kinds value in
                        (key :: kinds,
                         Printf.sprintf "(list (lnc_pair %s %s))"
                           key arg)
                     | T.Tuple ts ->
                        let (kinds, args) =
                          let init = (kinds, []) in
                          List.fold ts ~init ~f:(fun (kinds, args) t ->
                              let (kinds, arg) = aux kinds t in
                              (kinds, args @ [arg]))
                        in
                        let args = String.concat args ~sep:" " in
                        let len = List.length ts in
                        tuple_sizes := Set.add !tuple_sizes len;
                        let ctor = match len with
                          | 2 -> "lnc_pair"
                          | n -> Printf.sprintf "lnc_%dtuple" n
                        in (kinds, Printf.sprintf "(%s %s)" ctor args)
                     | _ ->
                        invalid_arg
                          (Printf.sprintf "bad arg %s in relation %s"
                             (T.to_string t) pred)
                   in
                   let (kinds', arg) = aux [] t in
                   let kinds' =
                     List.filter kinds' ~f:(function
                         | "string" -> false
                         | _ -> true)
                   in
                   let kinds =
                     List.fold kinds' ~init:kinds ~f:(fun kinds k ->
                         Map.set kinds k 0)
                   in (kinds, arg :: args))
             in
             let prop = Prop.{name = pred; args = List.rev args} in
             (kinds, Map.set props pred prop))
    in
    (* infer additional propositions based on
     * whether one category is a proper subset of another *)
    let props =
      let ctor_name = function
        | T.Constructor {name; args} -> Some name
        | _ -> None
      in
      Map.data lan.grammar
      |> List.fold ~init:props ~f:(fun props C.{name; meta_var; terms} ->
             let ops =
               Set.to_list terms
               |> List.filter_map ~f:ctor_name
               |> String.Set.of_list
             in
             if Set.is_empty ops then props else
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
               |> function
                 | None -> props
                 | Some c ->
                    let name = kind_name name in
                    if Set.mem ops name then props else
                      let args = [kind_name C.(c.name)] in
                      let prop = Prop.{name; args} in
                      Map.set props name prop)
    in
    (* generate term constructor types from the grammar *)
    let aliases = Hashtbl.create (module String) in
    let terms = 
      let init = String.Map.empty in
      Map.data lan.grammar
      |> List.fold ~init ~f:(fun terms' C.{name; meta_var; terms} ->
             let name' = kind_name name in
             if not (Map.mem kinds name') then terms' else
               let rec aux = function
                 | T.Var v ->
                    begin match L.kind_of_var lan v with
                    | None ->
                       invalid_arg
                         (Printf.sprintf "bad var %s in category %s"
                            v name)
                    | Some kind ->
                       if L.is_meta_var_of lan v kind then
                         let kind = kind_name kind in
                         if Map.mem kinds kind
                         then [kind]
                         else ["string"]
                       else ["string"]
                    end
                 | T.Str _ -> ["string"]
                 | T.Binding {var; body} -> "string" :: aux body
                 | T.List t -> aux t
                 | T.Map {key; value} -> aux_map key value
                 | T.Tuple ts ->
                    let ts' =
                      List.map ts ~f:aux
                      |> List.concat
                    in
                    let len = List.length ts' in
                    let ts' = String.concat ts' ~sep:" " in
                    tuple_sizes := Set.add !tuple_sizes len;
                    let ctor = match len with
                      | 2 -> "lnc_pair"
                      | n -> Printf.sprintf "lnc_%dtuple" n
                    in [Printf.sprintf "(%s %s)" ctor ts']
                 | t ->
                    invalid_arg
                      (Printf.sprintf "invalid term %s in category %s"
                         (T.to_string t) name)
               and aux_map key value =
                 let key = match L.kind_of_var lan key with
                   | None ->
                      invalid_arg
                        (Printf.sprintf "bad map key %s in category %s"
                           key name)
                   | Some kind ->
                      if L.is_meta_var_of lan key kind then
                        let kind = kind_name kind in
                        if Map.mem kinds kind
                        then kind
                        else "string"
                      else "string"
                 in
                 let value' = aux value in
                 if List.length value' > 1 then
                   invalid_arg
                     (Printf.sprintf "bad map value %s in category %s"
                        (T.to_string value) name)
                 else key :: value'
               in
               Set.to_list terms
               |> List.fold ~init:terms' ~f:(fun terms' t ->
                      match t with
                      | T.Constructor {name; args} ->
                         let name = kind_name name in
                         let args = List.map args ~f:aux |> List.concat in
                         let typ = name' in
                         let term = Term.{name; args; typ} in
                         Map.set terms' name term
                      | T.Map {key; value} ->
                         if not (Map.is_empty terms') then
                           invalid_arg
                             (Printf.sprintf
                                "bad term %s in category %s"
                                (T.to_string t) name)
                         else
                           let typ =
                             Printf.sprintf
                               "list (lnc_pair %s)"
                               (String.concat (aux_map key value) ~sep:" ")
                           in Hashtbl.set aliases name' typ; terms'
                      | T.List t' ->
                         if not (Map.is_empty terms') then
                           invalid_arg
                             (Printf.sprintf
                                "bad term %s in category %s"
                                (T.to_string t) name)
                         else
                           let t'' = aux t' in
                           if List.length t'' > 1 then
                             invalid_arg
                               (Printf.sprintf
                                  "bad list term %s in category %s"
                                  (T.to_string t') name)
                           else
                             let typ =
                               Printf.sprintf "list %s"
                                 (String.concat t'' ~sep:" ")
                             in Hashtbl.set aliases name' typ; terms'
                      | T.Tuple ts ->
                         if not (Map.is_empty terms') then
                           invalid_arg
                             (Printf.sprintf
                                "bad term %s in category %s"
                                (T.to_string t) name)
                         else
                           let ts' = List.map ts ~f:aux |> List.concat in
                           let len = List.length ts' in
                           tuple_sizes := Set.add !tuple_sizes len;
                           let typ =                           
                             Printf.sprintf "lnc_%dtuple %s" len
                               (String.concat ts' ~sep:" ")
                           in Hashtbl.set aliases name' typ; terms'
                      | _ -> terms'))
    in
    (* substitute with aliases *)
    let (kinds, terms, props) =
      let init = (kinds, terms, props) in
      Hashtbl.to_alist aliases
      |> List.fold ~init ~f:(fun (kinds, terms, props) (k, ty) ->
             let kinds = Map.remove kinds k in
             let terms =
               Map.map terms ~f:(fun ({name; args; typ} as term) ->
                   let args =
                     List.map args ~f:(fun a ->
                         String.substr_replace_all a
                           ~pattern:k ~with_:ty)
                   in
                   let typ =
                     String.substr_replace_all typ
                       ~pattern:k ~with_:ty
                   in {term with args; typ})
             in
             let props =
               Map.map props ~f:(fun ({name; args} as prop) ->
                   let args =
                     List.map args ~f:(fun a ->
                         String.substr_replace_all a
                           ~pattern:k ~with_:ty)
                   in {prop with args})
             in (kinds, terms, props))
    in           
    (* generate signatures for builtin
     * tuples since lambda-prolog doesn't
     * support declaring them anonymously *)
    let (kinds, terms) =
      let init = (kinds, terms) in
      Set.to_list !tuple_sizes 
      |> List.fold ~init ~f:(fun (kinds, terms) n ->
             let name = match n with
               | 2 -> "lnc_pair"
               | n -> Printf.sprintf "lnc_%dtuple" n
             in
             let kinds = Map.set kinds name n in
             let args = List.init n ~f:(fun n -> Printf.sprintf "A%d" n) in
             let typ =
               Printf.sprintf "(%s %s)" name
                 (String.concat args ~sep:" ")
             in                   
             let term = Term.{name; args; typ} in
             let terms = Map.set terms name term in
             (kinds, terms))
    in {kinds; terms; props}
end

module Term = struct
  type t =
    | Var of string
    | Constructor of {
        name: string;
        args: t list;
      } [@@deriving equal, compare]

  let rec to_string = function
    | Var v -> v
    | Constructor {name; args} ->
       match args with
       | [] -> name
       | args ->
          Printf.sprintf "(%s %s)" name
            (List.map args ~f:to_string
             |> String.concat ~sep:" ")
end

module Prop = struct
  type t =
    | Not of t
    | Eq of Term.t * Term.t
    | Prop of {
        name: string;
        args: Term.t list;
      } [@@deriving equal, compare]

  let rec to_string = function
    | Not p -> Printf.sprintf "not(%s)" (to_string p)
    | Eq (t1, t2) ->
       Printf.sprintf "%s = %s"
         (Term.to_string t1) (Term.to_string t2)
    | Prop {name; args} ->
       match args with
       | [] -> name
       | args ->
          Printf.sprintf "%s %s" name
            (List.map args ~f:Term.to_string
             |> String.concat ~sep:" ")
end

module Rule = struct
  type t = {
      name: string;
      premises: Prop.t list;
      conclusion: Prop.t;
    }

  let to_string {name; premises; conclusion} =
    let conclusion_str = Prop.to_string conclusion in
    let premises_str = match premises with
      | [] -> "" 
      | premises ->
         Printf.sprintf " :- %s"
           (List.map premises ~f:Prop.to_string
            |> String.concat ~sep:", ")
    in Printf.sprintf "%s%s %% %s" conclusion_str premises_str name
end

type t = {
    sigs: Sigs.t;
    rules: Rule.t String.Map.t;
  }

let of_language (lan: L.t) =
  let sigs = Sigs.of_language lan in
  let new_wildcard wildcard =
    let v = Term.Var ("_" ^ Int.to_string !wildcard) in
    wildcard := succ !wildcard; v
  in
  let fresh_var vars v =
    let v = String.capitalize v in
    let rec aux i =
      let v' = v ^ Int.to_string i in
      if Hash_set.mem vars v'
      then aux (succ i)
      else Term.Var v'
    in aux 0
  in
  let aux_term wildcard vars rule_name t =
    let rec aux_term t = match t with
      | T.Wildcard -> ([new_wildcard wildcard], [])
      | T.Nil ->
         ([Term.Constructor {name = "nil"; args = []}], [])
      | T.Var v ->
         let t' = [Term.Var (String.capitalize v)] in
         let prop = match L.kind_of_var lan v with
           | None -> []
           | Some kind ->
              let kind = kind_name kind in
              if Map.mem sigs.props kind
              then [Prop.Prop {name = kind; args = t'}]
              else []
         in (t', prop)
      | T.Constructor {name; args} ->
         let (args, props) =
           List.map args ~f:aux_term
           |> List.unzip
         in
         let (args, props) = (List.concat args, List.concat props) in
         ([Term.Constructor {name; args}], props)
      | T.Binding {var; body} ->
         let (ts, props) = aux_term body in
         (Term.Var (String.capitalize var) :: ts, props)
      | T.Subst {body; substs} ->
         let (body', props) = aux_term body in
         if List.length body' > 1 then
           invalid_arg
             (Printf.sprintf
                "invalid subst body term %s in rule %s"
                (T.to_string body) rule_name)
         else
           let body' = List.hd_exn body' in
           let rec aux props subs = function
             | [] -> (List.rev props, List.rev subs)
             | x :: xs ->
                match x with
                | T.Subst_pair {term; var} ->
                   let sub = fresh_var vars "sub" in
                   let (terms, props') = aux_term term in
                   if List.length terms > 1 then
                     invalid_arg
                       (Printf.sprintf
                          "invalid subst term %s in rule %s"
                          (T.to_string t) rule_name)
                   else
                     let term = List.hd_exn terms in
                     let var = Term.Var var in
                     let arg =
                       let name = "lnc_pair" in
                       let args = [term; var] in
                       Term.Constructor {name; args}
                     in
                     let body = match List.hd subs with
                       | None -> body'
                       | Some sub -> sub
                     in
                     let args = [body; arg; sub] in
                     let prop = Prop.Prop {name = "lnc_subst"; args} in
                     aux (prop :: (List.rev props' @ props)) (sub :: subs) xs
                | T.Subst_var s ->
                   let sub = fresh_var vars "sub" in
                   let body = match List.hd subs with
                     | None -> body'
                     | Some sub -> sub
                   in
                   let args = [body; Term.Var s; sub] in
                   let prop = Prop.Prop {name = "lnc_subst"; args} in
                   aux (prop :: props) (sub :: subs) xs
           in
           let (props, subs) = aux props [] substs in
           ([List.last_exn subs], props)
      | T.Map_update {key; value; map} ->
         let (key', ps1) = aux_term key in
         if List.length key' > 1 then
           invalid_arg
             (Printf.sprintf
                "invalid map key term %s in rule %s"
                (T.to_string key) rule_name)
         else
           let key' = List.hd_exn key' in
           let (value', ps2) = aux_term value in
           if List.length value' > 1 then
             invalid_arg
               (Printf.sprintf
                  "invalid map value term %s in rule %s"
                  (T.to_string value) rule_name)
           else
             let value' = List.hd_exn value' in
             let (map', ps3) = aux_term map in
             if List.length map' > 1 then
               invalid_arg
                 (Printf.sprintf
                    "invalid map source term %s in rule %s"
                    (T.to_string map) rule_name)
             else
               let map' = List.hd_exn map' in
               let m = fresh_var vars "Map" in
               let prop =
                 Prop.Prop {
                     name = "lnc_map_update";
                     args = [key'; value'; map'; m];
                 } in
               ([m], ps1 @ ps2 @ ps3 @ [prop])
      | T.Map_domain t ->
         let (t', ps) = aux_term t in
         if List.length t' > 1 then
           invalid_arg
             (Printf.sprintf
                "invalid map domain key term %s in rule %s"
                (T.to_string t) rule_name)
         else
           let t' = List.hd_exn t' in
           let m = fresh_var vars "List" in
           let prop =
             Prop.Prop {
                 name = "lnc_map_domain";
                 args = [t'; m];
               } in
           ([m], ps @ [prop])
      | T.Map_range t ->
         let (t', ps) = aux_term t in
         if List.length t' > 1 then
           invalid_arg
             (Printf.sprintf
                "invalid map range key term %s in rule %s"
                (T.to_string t) rule_name)
         else
           let t' = List.hd_exn t' in
           let m = fresh_var vars "List" in
           let prop =
             Prop.Prop {
                 name = "lnc_map_range";
                 args = [t'; m];
               } in
           ([m], ps @ [prop])
      | T.Tuple ts ->
         let (ts', props) =
           List.map ts ~f:aux_term
           |> List.unzip
         in
         let (args, props) = (List.concat ts', List.concat props) in
         let name = match List.length ts with
           | 2 -> "lnc_pair"
           | n -> Printf.sprintf "lnc_%dtuple" n
         in
         ([Term.Constructor {name; args}], props)
      | T.Zip (t1, t2) ->
         let (t1', ps1) = aux_term t1 in
         if List.length t1' > 1 then
           invalid_arg
             (Printf.sprintf
                "invalid zip term %s in rule %s"
                (T.to_string t1) rule_name)
         else
           let t1' = List.hd_exn t1' in
           let (t2', ps2) = aux_term t2 in
           if List.length t2' > 1 then
             invalid_arg
               (Printf.sprintf
                  "invalid zip term %s in rule %s"
                  (T.to_string t2) rule_name)
           else
             let t2' = List.hd_exn t2' in
             let m = fresh_var vars "Map" in
             let prop =
               Prop.Prop {
                   name = "lnc_zip";
                   args = [t1'; t2'; m];
                 } in
             ([m], ps1 @ ps2 @ [prop])
      | _ ->
         invalid_arg
           (Printf.sprintf "invalid term %s in rule %s" 
              (T.to_string t) rule_name)
    in aux_term t
  in
  let aux_formula wildcard vars rule_name f =
    let rec aux_formula f = match f with
      | F.Not f ->
         let ps = aux_formula f in
         if List.length ps > 1 then
           invalid_arg
             (Printf.sprintf "invalid 'not' formula %s of rule %s"
                (F.to_string f) rule_name)
         else [Prop.Not (List.hd_exn ps)]
      | F.Eq (t1, t2) ->
         let (t1', ps1) = aux_term wildcard vars rule_name t1 in
         if List.length t1' > 1 then
           invalid_arg
             (Printf.sprintf "invalid term %s in Eq of rule %s"
                (T.to_string t1) rule_name)
         else
           let (t2', ps2) = aux_term wildcard vars rule_name t2 in
           if List.length t1' > 1 then
             invalid_arg
               (Printf.sprintf "invalid term %s in Eq of rule %s"
                  (T.to_string t2) rule_name)
           else
             let t1 = List.hd_exn t1' in
             let t2 = List.hd_exn t2' in
             ps1 @ ps2 @ [Prop.Eq (t1, t2)]
      | F.Prop {predicate; args} ->
         let (args, ps) =
           List.map args ~f:(aux_term wildcard vars rule_name)
           |> List.unzip
         in
         let (args, ps) = (List.concat args, List.concat ps) in
         ps @ [Prop.Prop {name = predicate; args}]
      | F.Member {element; collection} ->
         let (t1', ps1) = aux_term wildcard vars rule_name element in
         if List.length t1' > 1 then
           invalid_arg
             (Printf.sprintf "invalid term %s in Eq of rule %s"
                (T.to_string collection) rule_name)
         else
           let (t2', ps2) = aux_term wildcard vars rule_name collection in
           if List.length t1' > 1 then
             invalid_arg
               (Printf.sprintf "invalid term %s in Eq of rule %s"
                  (T.to_string collection) rule_name)
           else
             let t1 = List.hd_exn t1' in
             let t2 = List.hd_exn t2' in
             let name = "lnc_member" in
             let args = [t1; t2] in
             ps1 @ ps2 @ [Prop.Prop {name; args}]
    in aux_formula f
  in
  let rules =
    let init = String.Map.empty in
    Map.data lan.rules
    |> List.fold ~init ~f:(fun rules (R.{name; premises; conclusion} as r) ->
           let wildcard = ref 0 in
           let vars =
             R.vars r
             |> List.filter_map ~f:(function
                    | T.Var v -> Some v
                    | _ -> None)
             |> String.Hash_set.of_list 
           in
           let premises =
             List.map premises ~f:(aux_formula wildcard vars name)
             |> List.concat
           in
           let (conclusion, premises') =
             let ps =
               aux_formula wildcard vars name conclusion
               |> List.rev
             in  (List.hd_exn ps, List.tl_exn ps |> List.rev)
           in
           let premises =
             Aux.dedup_list_stable ~compare:Prop.compare
               (premises @ premises')
           in
           let rule = Rule.{name; premises; conclusion} in
           Map.set rules name rule)
  in
  {sigs; rules}
