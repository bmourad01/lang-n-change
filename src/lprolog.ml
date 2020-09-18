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

let cat_name (lan: L.t) name =
  let name = String.capitalize name in
  match name with
  | "Typ" ->
     if Map.mem lan.grammar name
     then name
     else "Type"
  | "Knd" ->
     if Map.mem lan.grammar name
     then name
     else "Kind"
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
    let lnc_subset =
      Prop.{
          name = "lnc_subset";
          args = ["list A"; "list A"]
      } in
    let lnc_zip =
      Prop.{
          name = "lnc_zip";
          args = ["list A"; "list B"; "list (lnc_pair A B)"];
      } in
    String.Map.of_alist_exn
      [(lnc_member.name, lnc_member);
       (lnc_map_update.name, lnc_map_update);
       (lnc_map_domain.name, lnc_map_domain);
       (lnc_map_range.name, lnc_map_range);
       (lnc_subset.name, lnc_subset);
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
    let tuple_sizes = ref Int.Set.(singleton 2) in
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
    let subsets = Hashtbl.create (module String) in
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
                    let name' = kind_name name in
                    if Set.mem ops name' then props else
                      let args = [kind_name C.(c.name)] in
                      let prop = Prop.{name = name'; args} in
                      Hashtbl.set subsets name C.(c.name);
                      Map.set props name' prop)
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
    in
    (* programming variables are strings
     * but we have to wrap them in a constructor *)
    let terms =    
      Map.data lan.grammar
      |> List.fold ~init:terms ~f:(fun terms' C.{name; meta_var; terms} ->
             if Set.exists terms ~f:T.is_var then
               let kind = kind_name name in
               let name = kind ^ "_var" in
               let term = Term.{name; args = ["string"]; typ = kind} in
               Map.set terms' name term
             else terms')
    in             
    ({kinds; terms; props}, subsets)
end

module Term = struct
  type t =
    | Var of string
    | Constructor of {
        name: string;
        args: t list;
      }
    | Cons of t * t [@@deriving equal, compare]

  let rec to_string = function
    | Var v -> v
    | Constructor {name; args} ->
       begin match args with
       | [] -> name
       | args ->
          Printf.sprintf "(%s %s)" name
            (List.map args ~f:to_string
             |> String.concat ~sep:" ")
       end
    | Cons (t1, t2) ->
       Printf.sprintf "(%s :: %s)"
         (to_string t1) (to_string t2)
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
    in Printf.sprintf "%s%s. %% %s" conclusion_str premises_str name
end

let builtin_rules =
  let lnc_member_1 =
    Rule.{
        name = "LNC-MEMBER-1";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_member";
              args = [
                  Term.Var "X";
                  Term.(Cons (Var "X", Var "L"));
                ];
            };
    } in
  let lnc_member_2 =
    Rule.{
        name = "LNC-MEMBER-2";
        premises = [
            Prop.Prop {
                name = "lnc_member";
                args = [
                    Term.Var "X";
                    Term.Var "L";
                  ]
              };
          ];
        conclusion =
          Prop.Prop {
              name = "lnc_member";
              args = [
                  Term.Var "X";
                  Term.(Cons (Var "Y", Var "L"));
                ];
            };
    } in
  let lnc_map_update_1 =
    Rule.{
        name = "LNC-MAP-UPDATE-1";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_map_update";
              args = [
                  Term.Constructor {
                      name = "nil";
                      args = [];
                    };
                  Term.Var "X";
                  Term.Var "Y";
                  Term.(
                    Cons (
                        Constructor {
                            name = "lnc_pair";
                            args = [Var "X"; Var "Y"];
                          },
                        Constructor {
                            name = "nil";
                            args = [];
                          }));
                ];
            };
    } in
  let lnc_map_update_2 =
    Rule.{
        name = "LNC-MAP-UPDATE-2";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_map_update";
              args = [
                  Term.(
                    Cons (
                        Constructor {
                            name = "lnc_pair";
                            args = [Var "X"; Var "Y"];
                          },
                        Var "L"));
                  Term.Var "X";
                  Term.Var "Y'";
                  Term.(
                    Cons (
                        Constructor {
                            name = "lnc_pair";
                            args = [Var "X"; Var "Y'"];
                          },
                        Var "L"));
                ];
            };
    } in
  let lnc_map_update_3 =
    Rule.{
        name = "LNC-MAP-UPDATE-3";
        premises = [
            Prop.Prop {
                name = "lnc_map_update";
                args = [
                    Term.Var "L";
                    Term.Var "X";
                    Term.Var "Y";
                    Term.Var "L'";
                  ];
              };
          ];
        conclusion =
          Prop.Prop {
              name = "lnc_map_update";
              args = [
                  Term.(
                    Cons (
                        Constructor {
                            name = "lnc_pair";
                            args = [Var "X'"; Var "Y"];
                          },
                        Var "L"));
                  Term.Var "X";
                  Term.Var "Y'";
                  Term.(
                    Cons (
                        Constructor {
                            name = "lnc_pair";
                            args = [Var "X'"; Var "Y"];
                          },
                        Var "L'"));
                ];
            };
    } in
  let lnc_map_domain_1 =
    Rule.{
        name = "LNC-MAP-DOMAIN-1";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_map_domain";
              args = [
                  Term.Constructor {name = "nil"; args = []};
                  Term.Constructor {name = "nil"; args = []};
                ];
            };
    } in
  let lnc_map_domain_2 =
    Rule.{
        name = "LNC-MAP-DOMAIN-2";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_map_domain";
              args = [
                  Term.(
                    Cons
                      (Constructor {
                           name = "lnc_pair";
                           args = [Var "X"; Var "Y"];
                         },
                       Var "M"));
                  Term.(Cons (Var "X", Var "L"));
                ];
            };
    } in
  let lnc_map_range_1 =
    Rule.{
        name = "LNC-MAP-RANGE-1";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_map_range";
              args = [
                  Term.Constructor {name = "nil"; args = []};
                  Term.Constructor {name = "nil"; args = []};
                ];
            };
    } in
  let lnc_map_range_2 =
    Rule.{
        name = "LNC-MAP-RANGE-2";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_map_range";
              args = [
                  Term.(
                    Cons (
                        Constructor {
                            name = "lnc_pair";
                            args = [Var "X"; Var "Y"];
                          },
                        Var "M"));
                  Term.(Cons (Var "Y", Var "L"));
                ];
            };
    } in
  let lnc_subset_1 =
    Rule.{
        name = "LNC-SUBSET-1";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_subset";
              args = [
                  Term.Constructor {name = "nil"; args = []};
                  Term.Constructor {name = "nil"; args = []};
                ];
            };
    } in
  let lnc_subset_2 =
    Rule.{
        name = "LNC-SUBSET-2";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_subset";
              args = [
                  Term.Constructor {name = "nil"; args = []};
                  Term.(Cons (Var "Y", Var "L"));
                ];
            };
    } in
  let lnc_subset_3 =
    Rule.{
        name = "LNC-SUBSET-3";
        premises = [
            Prop.Prop {
                name = "lnc_subset";
                args = Term.[Var "L1"; Var "L2"];
              };
          ];
        conclusion =
          Prop.Prop {
              name = "lnc_subset";
              args = [
                  Term.(Cons (Var "X", Var "L1"));
                  Term.(Cons (Var "Y", Var "L2"));
                ];
            };
    } in
  let lnc_subset_4 =
    Rule.{
        name = "LNC-SUBSET-4";
        premises = [
            Prop.Prop {
                name = "lnc_member";
                args = Term.[Var "X"; Var "L2"];
              };
            Prop.Prop {
                name = "lnc_subset";
                args = Term.[Var "L1"; Var "L2"];
              };
          ];
        conclusion =
          Prop.Prop {
              name = "lnc_subset";
              args = [
                  Term.(Cons (Var "X", Var "L1"));
                  Term.(Cons (Var "Y", Var "L2"));
                ];
            };
    } in
  let lnc_zip_1 =
    Rule.{
        name = "LNC-ZIP-1";
        premises = [];
        conclusion =
          Prop.Prop {
              name = "lnc_zip";
              args = [
                  Term.Constructor {name = "nil"; args = []};
                  Term.Constructor {name = "nil"; args = []};
                  Term.Constructor {name = "nil"; args = []};
                ];
            };
    } in
  let lnc_zip_2 =
    Rule.{
        name = "LNC-ZIP-2";
        premises = [
            Prop.Prop {
                name = "lnc_zip";
                args = [
                    Term.Var "L1";
                    Term.Var "L2";
                    Term.Var "M";
                  ];
              };
          ];
        conclusion =
          Prop.Prop {
              name = "lnc_zip";
              args = [
                  Term.(Cons (Var "X", Var "L1"));
                  Term.(Cons (Var "Y", Var "L2"));
                  Term.(
                    Cons (
                        Constructor {
                            name = "lnc_pair";
                            args = [Var "X"; Var "Y"];
                          },
                        Var "M"));
                ];
            };
    } in
  String.Map.of_alist_exn
    [(lnc_member_1.name, lnc_member_1);
     (lnc_member_2.name, lnc_member_2);
     (lnc_map_domain_1.name, lnc_map_domain_1);
     (lnc_map_domain_2.name, lnc_map_domain_2);
     (lnc_map_range_1.name, lnc_map_range_1);
     (lnc_map_range_2.name, lnc_map_range_2);
     (lnc_subset_1.name, lnc_subset_1);
     (lnc_subset_2.name, lnc_subset_2);
     (lnc_subset_3.name, lnc_subset_3);
     (lnc_subset_4.name, lnc_subset_4);
     (lnc_zip_1.name, lnc_zip_1);
     (lnc_zip_2.name, lnc_zip_2);
     (lnc_map_update_1.name, lnc_map_update_1);
     (lnc_map_update_2.name, lnc_map_update_2);
     (lnc_map_update_3.name, lnc_map_update_3);
    ]

type t = {
    sigs: Sigs.t;
    rules: Rule.t String.Map.t;
  }

let of_language (lan: L.t) =
  let (sigs, subsets) = Sigs.of_language lan in
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
  (* generate terms along with additional propositions
   * if the term itself needs to make use of some
   * propositions to compute its result *)
  let subst_kinds = Hashtbl.create (module String) in
  let aux_term wildcard vars rule_name depth t =
    let rec aux_term depth t = match t with
      | T.Wildcard -> ([new_wildcard wildcard], [])
      | T.Nil ->
         ([Term.Constructor {name = "nil"; args = []}], [])
      | T.Var v ->
         let k = L.kind_of_var lan v in
         let def = Term.Var (String.capitalize v) in
         let t' = match k with
           | None -> [def]
           | Some kind ->
              if L.is_meta_var_of lan v kind then [def]
              else if depth = 0 then
                (* fixme: we shouldn't rely on depth of
                 * terms to infer whether we should wrap
                 * a variable in a constructor (we should
                 * look at the signatures instead) *)
                let kind = kind_name kind in
                [Term.Constructor {
                     name = kind ^ "_var";
                     args = [def];
                   }]
              else [def]
         in
         let prop = match k with
           | None -> []
           | Some kind ->
              let kind = kind_name kind in
              if Map.mem sigs.props kind
              then [Prop.Prop {name = kind; args = t'}]
              else []
         in (t', prop)
      | T.Constructor {name; args} ->
         let (args, props) =
           List.map args ~f:(aux_term (succ depth))
           |> List.unzip
         in
         let (args, props) = (List.concat args, List.concat props) in
         ([Term.Constructor {name; args}], props)
      | T.Binding {var; body} ->
         let (ts, props) = aux_term (succ depth) body in
         (Term.Var (String.capitalize var) :: ts, props)
      | T.Subst {body; substs} ->
         let subst_kind s = function
           | T.Var v ->
              begin match L.kind_of_var lan v with
              | None ->
                 invalid_arg
                   (Printf.sprintf
                      "invalid kind of subst %s %s in rule %s"
                      s (T.to_string body) rule_name)
              | Some kind ->
                 if not (L.is_meta_var_of lan v kind) then
                   invalid_arg
                     (Printf.sprintf
                        "invalid kind of subst %s %s in rule %s"
                        s (T.to_string body) rule_name)
                 else
                   let kind = match Hashtbl.find subsets kind with
                     | None -> kind
                     | Some kind -> kind
                   in kind_name kind
              end
           | T.Constructor {name; _} ->
              begin match L.kind_of_op lan name with
              | None ->
                 invalid_arg
                   (Printf.sprintf
                      "invalid kind of subst %s %s in rule %s"
                      s (T.to_string body) rule_name)
              | Some kind ->
                 let kind = match Hashtbl.find subsets kind with
                   | None -> kind
                   | Some kind -> kind
                 in kind_name kind
              end
           | _ ->
              invalid_arg
                (Printf.sprintf
                   "invalid subst %s term %s in rule %s"
                   s (T.to_string body) rule_name)
         in
         let body_kind = subst_kind "body" body in
         let (body', props) = aux_term (succ depth) body in
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
                   let term_kind = subst_kind "term" term in
                   let sub = fresh_var vars "sub" in
                   let (terms, props') = aux_term (succ depth) term in
                   if List.length terms > 1 then
                     invalid_arg
                       (Printf.sprintf
                          "invalid subst term %s in rule %s"
                          (T.to_string t) rule_name)
                   else
                     let term = List.hd_exn terms in
                     let var = Term.Var (String.capitalize var) in
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
                     let name = Printf.sprintf "lnc_subst_%s_%s" body_kind term_kind in
                     let prop = Prop.Prop {name; args} in
                     Hashtbl.add_multi subst_kinds body_kind term_kind;
                     aux (prop :: (List.rev props' @ props)) (sub :: subs) xs
                | T.Subst_var s ->
                   let sub = fresh_var vars "sub" in
                   let body = match List.hd subs with
                     | None -> body'
                     | Some sub -> sub
                   in
                   let args = [body; Term.Var s; sub] in
                   (* fixme: how do we infer the kind of the substitution? *)
                   let name = Printf.sprintf "lnc_subst_%s_%s" body_kind body_kind in
                   let prop = Prop.Prop {name; args} in
                   Hashtbl.add_multi subst_kinds body_kind body_kind;
                   aux (prop :: props) (sub :: subs) xs
           in
           let (props, subs) = aux props [] substs in
           ([List.last_exn subs], props)
      | T.Map_update {key; value; map} ->
         let (key', ps1) = aux_term (succ depth) key in
         if List.length key' > 1 then
           invalid_arg
             (Printf.sprintf
                "invalid map key term %s in rule %s"
                (T.to_string key) rule_name)
         else
           let key' = List.hd_exn key' in
           let (value', ps2) = aux_term (succ depth) value in
           if List.length value' > 1 then
             invalid_arg
               (Printf.sprintf
                  "invalid map value term %s in rule %s"
                  (T.to_string value) rule_name)
           else
             let value' = List.hd_exn value' in
             let (map', ps3) = aux_term (succ depth) map in
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
         let (t', ps) = aux_term (succ depth) t in
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
         let (t', ps) = aux_term (succ depth) t in
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
           List.map ts ~f:(aux_term (succ depth))
           |> List.unzip
         in
         let (args, props) = (List.concat ts', List.concat props) in
         let name = match List.length ts with
           | 2 -> "lnc_pair"
           | n -> Printf.sprintf "lnc_%dtuple" n
         in
         ([Term.Constructor {name; args}], props)
      | T.Zip (t1, t2) ->
         let (t1', ps1) = aux_term (succ depth) t1 in
         if List.length t1' > 1 then
           invalid_arg
             (Printf.sprintf
                "invalid zip term %s in rule %s"
                (T.to_string t1) rule_name)
         else
           let t1' = List.hd_exn t1' in
           let (t2', ps2) = aux_term (succ depth) t2 in
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
    in aux_term depth t
  in
  (* generate the propositions *)
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
         let (t1', ps1) = aux_term wildcard vars rule_name 0 t1 in
         if List.length t1' > 1 then
           invalid_arg
             (Printf.sprintf "invalid term %s in Eq of rule %s"
                (T.to_string t1) rule_name)
         else
           let (t2', ps2) = aux_term wildcard vars rule_name 0 t2 in
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
           List.map args ~f:(aux_term wildcard vars rule_name 0)
           |> List.unzip
         in
         let (args, ps) = (List.concat args, List.concat ps) in
         ps @ [Prop.Prop {name = predicate; args}]
      | F.Member {element; collection} ->
         let (t1', ps1) = aux_term wildcard vars rule_name 1 element in
         if List.length t1' > 1 then
           invalid_arg
             (Printf.sprintf "invalid term %s in Member of rule %s"
                (T.to_string element) rule_name)
         else
           let (t2', ps2) = aux_term wildcard vars rule_name 1 collection in
           if List.length t1' > 1 then
             invalid_arg
               (Printf.sprintf "invalid term %s in Member of rule %s"
                  (T.to_string collection) rule_name)
           else
             let t1 = List.hd_exn t1' in
             let t2 = List.hd_exn t2' in
             let name = "lnc_member" in
             let args = [t1; t2] in
             ps1 @ ps2 @ [Prop.Prop {name; args}]
      | F.Subset {sub; super} ->
         let (t1', ps1) = aux_term wildcard vars rule_name 1 sub in
         if List.length t1' > 1 then
           invalid_arg
             (Printf.sprintf "invalid term %s in Subset of rule %s"
                (T.to_string sub) rule_name)
         else
           let (t2', ps2) = aux_term wildcard vars rule_name 1 super in
           if List.length t1' > 1 then
             invalid_arg
               (Printf.sprintf "invalid term %s in Subset of rule %s"
                  (T.to_string super) rule_name)
           else
             let t1 = List.hd_exn t1' in
             let t2 = List.hd_exn t2' in
             let name = "lnc_subset" in
             let args = [t1; t2] in
             ps1 @ ps2 @ [Prop.Prop {name; args}]
    in aux_formula f
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
  (* for categories which are proper subsets of others
   * we need to generate the rules which declare them
   * as distinct (for example, Value vs Expression
   * needs to be distinguishable for call-by-value) *)
  let rules =
    let init = rules in
    Map.data lan.grammar
    |> List.fold ~init ~f:(fun rules C.{name; meta_var; terms} ->
           if not (Hashtbl.mem subsets name) then rules else
             let name' = kind_name name in             
             Set.to_list terms
             |> List.fold ~init:rules ~f:(fun rules t ->
                    match t with
                    | T.Constructor c ->
                       let t = T.uniquify t in
                       let rule_name =
                         Printf.sprintf "%s-%s"
                           (String.uppercase name)
                           (String.uppercase c.name)
                       in
                       let (t', props) =
                         aux_term (ref 0) (String.Hash_set.create ())
                            rule_name 0 t
                       in
                       if List.length t' > 1 then
                         invalid_arg
                           (Printf.sprintf
                              "invalid term %s in subset category %s"
                              (T.to_string t) name)
                       else
                         let t' = List.hd_exn t' in
                         let conclusion =
                           Prop.Prop {
                               name = name';
                               args = [t'];
                             } in
                         let rule =
                           Rule.{
                               name = rule_name;
                               premises = props;
                               conclusion;
                           } in
                         Map.set rules rule_name rule
                    | _ -> rules))
  in
  (* update the signatures with substitutions *)
  let sigs =
    Hashtbl.to_alist subst_kinds
    |> List.fold ~init:sigs ~f:(fun sigs (body, terms) ->
           List.fold terms ~init:sigs ~f:(fun sigs term ->
               let name = Printf.sprintf "lnc_subst_%s_%s" body term in
               let prop =
                 Sigs.Prop.{
                     name;
                     args = [
                         body;
                         Printf.sprintf "(lnc_pair %s string)" term;
                         body;
                       ];
                 } in
               let props = Map.set sigs.props name prop in
               {sigs with props}))
  in
  (* generate substitution rules *)
  let rules =
    let subst_rule wildcard vars rule_name name t meta_var var =
      let t = T.uniquify t ~min:0 in
      let (t', _) = aux_term wildcard vars rule_name 0 t in
      let t' = List.hd_exn t' in
      let (premises, sub) = match t with
        | T.Constructor c ->
           (* fixme: this assumes that constructors in the
            * grammar will have a maximum term depth of 1 *)
           List.filter_map c.args ~f:(function
               | T.Var v ->
                  let orig = String.capitalize v in
                  if String.is_prefix orig ~prefix:meta_var then
                    let sub = orig ^ "'" in
                    Some
                      (Prop.Prop {
                           name;
                           args = [
                               Term.Var orig;
                               Term.Constructor {
                                   name = "lnc_pair";
                                   args = [
                                       Term.Var meta_var;
                                       Term.Var var;
                                     ];
                                 };
                               Term.Var sub;
                             ];
                         }, (T.Var v, T.Var (v ^ "'")))
                  else None
               | _ -> None)
           |> List.unzip
        | _ -> ([], [])
      in
      let (t'', _) =
        aux_term wildcard vars rule_name 0
          (T.substitute t sub)
      in
      let t'' = List.hd_exn t'' in
      Rule.{
          name = rule_name;
          premises;
          conclusion =
            Prop.Prop {
                name;
                args = [
                    t';
                    Term.Constructor {
                        name = "lnc_pair";
                        args = [
                            Term.Var meta_var;
                            Term.Var var;
                          ];
                      };
                    t'';
                  ];
              };
      }
    in
    Hashtbl.to_alist subst_kinds
    |> List.fold ~init:rules ~f:(fun rules (body, terms) ->
           let body_cat = cat_name lan body in
           List.fold terms ~init:rules ~f:(fun rules term ->
               let term_cat = cat_name lan term in
               match (Map.find lan.grammar body_cat,
                      Map.find lan.grammar term_cat) with
               | (None, _) | (_, None) -> rules
               | (Some bc, Some tc) ->
                  let var =
                    let f = function
                      | T.Var v -> Some v
                      | _ -> None
                    in
                    match Set.find_map bc.terms ~f with
                    | Some var -> String.capitalize var
                    | None ->
                       invalid_arg                      
                         (Printf.sprintf
                            "no variable kind found for category %s"
                            bc.name)
                  in
                  let f rules t =
                    let suffix = match t with
                      | T.Var v -> Some (String.uppercase v)
                      | T.Constructor {name; _} ->
                         Some (String.uppercase name)
                      | _ -> None
                    in
                    Option.(
                      value ~default:rules
                        (suffix >>| fun suffix ->
                         let name =
                           Printf.sprintf "lnc_subst_%s_%s"
                             body term
                         in
                         let rule_name =
                           Printf.sprintf "LNC-SUBST-%s-%s-%s"
                             (String.uppercase body)
                             (String.uppercase term)
                             suffix
                         in
                         let meta_var =
                           String.capitalize tc.meta_var
                         in
                         if T.is_constructor t then
                           let rule =
                             subst_rule
                               (ref 0) (String.Hash_set.create ())
                               rule_name name t meta_var var
                           in Map.set rules rule_name rule
                         else
                           let rule1 =
                             Rule.{
                                 name = rule_name ^ "-EQ";
                                 premises = [];
                                 conclusion =
                                   Prop.Prop {
                                       name;
                                       args = [
                                           Term.Constructor {
                                               name = body ^ "_var";
                                               args = [
                                                   Term.Var var;
                                                 ];
                                             };
                                           Term.Constructor {
                                               name = "lnc_pair";
                                               args = [
                                                   Term.Var meta_var;
                                                   Term.Var var;
                                                 ];
                                             };
                                           Term.Var meta_var;
                                         ];
                                     };
                             } in
                           let rule2 =
                             Rule.{
                                 name = rule_name ^ "-NEQ";
                                 premises = [];
                                 conclusion =
                                   Prop.Prop {
                                       name;
                                       args = [
                                           Term.Constructor {
                                               name = body ^ "_var";
                                               args = [
                                                   Term.Var var;
                                                 ];
                                             };
                                           Term.Constructor {
                                               name = "lnc_pair";
                                               args = [
                                                   Term.Var meta_var;
                                                   Term.Var (var ^ "'");
                                                 ];
                                             };
                                           Term.Constructor {
                                               name = body ^ "_var";
                                               args = [
                                                   Term.Var var;
                                                 ];
                                             };
                                         ];
                                     };
                             } in
                           Map.set
                             (Map.set rules rule1.name rule1)
                             rule2.name rule2))
                  in List.fold (Set.to_list bc.terms) ~init:rules ~f))
  in
  {sigs; rules}
