open Core_kernel

module L = Language
module T = L.Term
module G = L.Grammar
module C = G.Category

module Sigs = struct
  module Term = struct
    type t = {
        name: string; 
        args: string list;
        kind: string;
      }
    
    let to_string {name; args; kind} =
      let args_str = match args with
        | [] -> ""
        | args ->
           (String.concat args ~sep:" -> ") ^ " -> "
      in Printf.sprintf "type %s %s%s." name args_str kind
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

  type t = {
      kinds: String.Set.t;
      terms: Term.t String.Map.t;
      props: Prop.t String.Map.t;
    }

  let to_string {kinds; terms; props} =
    let kinds_str =
      Set.to_list kinds
      |> List.map ~f:(Printf.sprintf "kind %s type.")
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
    let kind_name name =
      let name = String.lowercase name in
      match name with
      | "type" -> "typ"
      | "kind" -> "knd"
      | _ -> name
    in
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
      let init = (String.Set.empty, String.Map.empty) in
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
                        let ctor = match List.length ts with
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
                     |> String.Set.of_list
                   in
                   let kinds = Set.union kinds kinds' in
                   (kinds, arg :: args))
             in
             let prop = Prop.{name = pred; args = List.rev args} in
             (kinds, Map.set props pred prop))
    in
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
                      in Set.is_subset ops ops')
               |> function
                 | None -> props
                 | Some c ->
                    let name = kind_name name in
                    if Set.mem ops name then props else
                      let args = [kind_name C.(c.name)] in
                      let prop = Prop.{name; args} in
                      Map.set props name prop)
    in
    let terms = 
      let init = String.Map.empty in
      Map.data lan.grammar
      |> List.fold ~init ~f:(fun terms' C.{name; meta_var; terms} ->
             let name' = kind_name name in
             if not (Set.mem kinds name') then terms' else
               let rec aux = function
                 | T.Var v ->
                    begin match L.kind_of_var lan v with
                    | None ->
                       invalid_arg
                         (Printf.sprintf "bad var %s in category %s"
                            v name)
                    | Some kind ->
                       let kind = kind_name kind in
                       if Set.mem kinds kind
                       then [kind]
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
                      |> String.concat ~sep:" "
                    in
                    let ctor = match List.length ts with
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
                      let kind = kind_name kind in
                      if Set.mem kinds kind
                      then kind
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
                         let kind = name' in
                         let term = Term.{name; args; kind} in
                         Map.set terms' name term
                      | T.Map {key; value} ->
                         let name = name' ^ "_t" in
                         let args =
                           Printf.sprintf
                             "list (lnc_pair %s)"
                             (String.concat (aux_map key value) ~sep:" ")
                           :: []
                         in
                         let kind = name' in
                         let term = Term.{name; args; kind} in
                         begin match Map.add terms' name term with
                         | `Duplicate -> 
                            invalid_arg
                              (Printf.sprintf
                                 "duplicate term %s for category %s"
                                 (T.to_string t) name)
                         | `Ok terms' -> terms'
                         end
                      | _ -> terms'))
                      
    in {kinds; terms; props}
end

module Term = struct
  type t =
    | Var of string
    | Constructor of {
        name: string;
        args: t list;
      }

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
  type t = {
      name: string;
      args: Term.t list;
    }

  let to_string {name; args} = match args with
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
    in Printf.sprintf "%s%s.%%%s" conclusion_str premises_str name
end

type t = {
    sigs: Sigs.t;
    rules: Rule.t String.Map.t;
  }

let of_language (lan: L.t) =
  let sigs = Sigs.of_language lan in
  let rules = String.Map.empty in
  {sigs; rules}
