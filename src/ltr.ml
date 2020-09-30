open Core_kernel

module Type = struct
  type t =
    | Any
    | Lan
    | Syntax
    | Rule
    | Formula
    | Term
    | String
    | Bool
    | Int
    | Tuple of t list
    | Option of t
    | List of t
    | Arrow of t list [@@deriving equal]

  let rec to_string = function
    | Any -> "any"
    | Lan -> "lan"
    | Syntax -> "syntax"
    | Rule -> "rule"
    | Formula -> "formula"
    | Term -> "term"
    | String -> "string"
    | Bool -> "bool"
    | Int -> "int"
    | Tuple ts ->
       List.map ts ~f:to_string
       |> String.concat ~sep:", "
       |> Printf.sprintf "(%s) tuple"
    | Option t -> Printf.sprintf "%s option" (to_string t)
    | List t -> Printf.sprintf "%s list" (to_string t)
    | Arrow ts ->
       List.map ts ~f:to_string
       |> String.concat ~sep:" -> "
       |> Printf.sprintf "(%s)"
end

module Exp = struct
  type t =
    (* builtin *)
    | Self
    (* variable operations *)
    | Var of string
    (* string operations *)
    | Str of string
    | Str_concat of t * t
    | Uppercase of t
    | Lowercase of t
    (* integer operations *)
    | Int of int
    | Int_str of t
    (* boolean operations *)
    | Bool_exp of boolean
    (* control operations *)
    | Let of {
        recursive: Type.t option;
        names: string list;
        args: (string * Type.t) list;
        exp: t;
        body: t;
      }
    | Apply of t * t list
    | Ite of t * t * t
    | Seq of t * t
    | Select of {
        keep: bool;
        field: t;
        pattern: t;
        body: t;
      }
    (* tuple operations *)
    | Tuple of t list
    (* list operations *)
    | List of t list
    | Head of t
    | Tail of t
    | Last of t
    | Nth of t * t
    | List_concat of t
    | Rev of t
    | Dedup of t
    | Append of t * t
    | Diff of t * t
    | Zip of t * t
    | Assoc of t * t
    (* option operations *)
    | Nothing
    | Something of t
    | Option_get of t
    (* term operations *)
    | New_term of term
    | Vars_of of t
    | Fresh_var of string
    | Unbind of t
    | Bound_of of t
    | Substitute of t * t
    | Var_overlap of t * t
    | Ticked of t
    | Ticked_restricted of t * t
    (* grammar operations *)
    | New_syntax of {
        extend: bool;
        name: string;
        meta_var: string;
        terms: t list;
      }
    | Remove_syntax of string
    | Meta_var_of of string
    | Syntax_terms_of of string
    (* relation operations *)
    | New_relation of string * t list
    (* formula operations *)
    | New_formula of formula
    | Uniquify_formulae of {
        formulae: t;
        hint_map: t;
        hint_var: string;
      }
    (* rule operations *)
    | New_rule of {
        name: t;
        premises: t list;
        conclusion: t;
      }
    | Rule_name of t
    | Rule_premises of t
    | Rule_conclusion of t
    | Rules_of
    | Add_rule of t
    | Set_rules of t
    (* hint operations *)
    | New_hint of {
        extend: bool;
        name: string;
        elements: (string * string list) list;
      }
    | Lookup_hint of string
  and boolean =
    | Bool of bool
    | Not of t
    | And of t * t
    | Or of t * t
    | Eq of t * t
    | Is_member of t * t
    | Is_nothing of t
    | Is_something of t
    | Is_empty of t
    | Is_var of t
    | Is_str of t
    | Is_constructor of t
    | Is_binding of t
    | Is_subst of t
    | Is_list of t
    | Is_map of t
    | Is_tuple of t
    | Is_var_kind of t * string
    | Is_op_kind of t * string
    | Has_syntax of string
  and term = 
    | Term_nil
    | Term_var of string
    | Term_str of string
    | Term_constructor of t * t
    | Term_binding of t * t
    | Term_subst of t * subst list
    | Term_map_update of t * t * t
    | Term_map_domain of t
    | Term_map_range of t
    | Term_cons of t * t
    | Term_list of t
    | Term_map of string * t
    | Term_tuple of t list
    | Term_union of t list
    | Term_map_union of t list
    | Term_zip of t * t
    | Term_fresh of t
  and formula =
    | Formula_not of t
    | Formula_eq of t * t
    | Formula_prop of t * t
    | Formula_member of t * t
    | Formula_subset of t * t
  and subst =
    | Subst_pair of t * string
    | Subst_var of string * string

  let rec to_string = function
    | Self -> "self"
    | Var v -> v
    | Str s -> Printf.sprintf "\"%s\"" s
    | Str_concat (e1, e2) ->
       Printf.sprintf "%s ^ %s"
         (to_string e1) (to_string e2)
    | Uppercase e ->
       Printf.sprintf "uppercase(%s)"
         (to_string e)
    | Lowercase e ->
       Printf.sprintf "lowercase(%s)"
         (to_string e)
    | Int n -> Int.to_string n
    | Int_str e ->
       Printf.sprintf "int_str(%s)"
         (to_string e)
    | Bool_exp b -> string_of_boolean b
    | Let {recursive; names; args; exp; body} ->
       let args_str = match args with
         | [] -> " "
         | _ ->
            List.map args ~f:(fun (a, t) ->
                Printf.sprintf "(%s: %s)"
                  a (Type.to_string t))
            |> String.concat ~sep:" "
            |> Printf.sprintf " %s"
       in
       let let_str = match recursive with
         | None -> "let"
         | Some _ -> "let rec"
       in
       let rec_typ = match recursive with
         | None -> ""
         | Some typ -> Printf.sprintf " : %s " (Type.to_string typ)
       in
       let names_str = match names with
         | [] -> failwith "unreachable"
         | x :: [] -> x
         | _ ->
            Printf.sprintf "(%s)"
              (String.concat names ~sep:", ")
       in
       Printf.sprintf "%s %s%s%s= %s in %s"
         let_str names_str args_str rec_typ
         (to_string exp) (to_string body)
    | Apply (e, args) ->
       Printf.sprintf "%s(%s)" (to_string e)
         (List.map args ~f:to_string
          |> String.concat ~sep:", ")
    | Ite (b, e1, e2) ->
       Printf.sprintf "if %s then %s else %s"
         (to_string b) (to_string e1) (to_string e2)
    | Seq (e1, e2) ->
       Printf.sprintf "%s; %s"
         (to_string e1) (to_string e2)
    | Select {keep; field; pattern; body} ->
       let field_str = to_string field in
       let field_str = if keep then field_str ^ "!" else field_str in
       Printf.sprintf "%s[%s]: {%s}"
         field_str (to_string pattern) (to_string body)
    | Tuple es ->
       Printf.sprintf "(%s)"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | List es ->
       Printf.sprintf "[%s]"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | Head e -> Printf.sprintf "head(%s)" (to_string e)
    | Tail e -> Printf.sprintf "tail(%s)" (to_string e)
    | Last e -> Printf.sprintf "last(%s)" (to_string e)
    | Nth (e1, e2) ->
       Printf.sprintf "nth(%s, %s)"
         (to_string e1) (to_string e2)
    | List_concat e -> Printf.sprintf "concat(%s)" (to_string e)
    | Rev e -> Printf.sprintf "rev(%s)" (to_string e)       
    | Dedup e -> Printf.sprintf "dedup(%s)" (to_string e)
    | Append (e1, e2) ->
       Printf.sprintf "%s @ %s"
         (to_string e1) (to_string e2)
    | Diff (e1, e2) ->
       Printf.sprintf "diff(%s, %s)"
         (to_string e1) (to_string e2)
    | Zip (e1, e2) ->
       Printf.sprintf "zip(%s, %s)"
         (to_string e1) (to_string e2)
    | Assoc (e1, e2) ->
       Printf.sprintf "assoc(%s, %s)"
         (to_string e1) (to_string e2)
    | Nothing -> "nothing"
    | Something e -> Printf.sprintf "something(%s)" (to_string e)
    | Option_get e -> Printf.sprintf "get(%s)" (to_string e)
    | New_term t -> string_of_term t
    | Vars_of e -> Printf.sprintf "vars(%s)" (to_string e)
    | Fresh_var v -> Printf.sprintf "fresh_var(%s)" v
    | Unbind e -> Printf.sprintf "unbind(%s)" (to_string e)
    | Bound_of e -> Printf.sprintf "bound(%s)" (to_string e)
    | Substitute (e1, e2) ->
       Printf.sprintf "substitute(%s, %s)"
         (to_string e1) (to_string e2)
    | Var_overlap (e1, e2) ->
       Printf.sprintf "var_overlap(%s, %s)"
         (to_string e1) (to_string e2)
    | Ticked e -> to_string e ^ "'"
    | Ticked_restricted (e1, e2) ->
       Printf.sprintf "%s'|%s"
         (to_string e1) (to_string e2)
    | New_syntax {extend; name; meta_var; terms} ->
       let extend_str = if extend then " ... | " else " " in
       Printf.sprintf "%s %s ::=%s%s"
         name meta_var extend_str
         (List.map terms ~f:to_string
          |> String.concat ~sep:" | ")
    | Remove_syntax name -> Printf.sprintf "remove_syntax(%s)" name
    | Meta_var_of name -> Printf.sprintf "meta_var(%s)" name
    | Syntax_terms_of name -> Printf.sprintf "syntax(%s)" name
    | New_relation (predicate, terms) ->
       Printf.sprintf "%%%s %s"
         predicate
         (List.map terms ~f:to_string
          |> String.concat ~sep:" ")
    | New_formula f -> string_of_formula f
    | Uniquify_formulae {formulae; hint_map; hint_var} ->
       Printf.sprintf "uniquify(%s, %s, \"%s\")"
         (to_string formulae) (to_string hint_map) hint_var
    | New_rule {name; premises; conclusion} ->
       Printf.sprintf "[%s] {%s---------------------%s}"
         (to_string name)
         (List.map premises ~f:to_string
          |> String.concat ~sep:", ")
         (to_string conclusion)
    | Rule_name e -> Printf.sprintf "rule_name(%s)" (to_string e)
    | Rule_premises e -> Printf.sprintf "premises(%s)" (to_string e)
    | Rule_conclusion e -> Printf.sprintf "conclusion(%s)" (to_string e)
    | Rules_of -> "rules"
    | Add_rule e -> Printf.sprintf "add_rule(%s)" (to_string e)
    | Set_rules e -> Printf.sprintf "set_rules(%s)" (to_string e)
    | New_hint {extend; name; elements} ->
       let extend_str = if extend then " ... | " else " " in
       let elements_str =
         List.map elements ~f:(fun (k, v) ->
             Printf.sprintf "%s => %s" k
               (String.concat v ~sep:" "))
         |> String.concat ~sep:" | "
       in Printf.sprintf "#%s:%s%s" name extend_str elements_str
    | Lookup_hint hint -> Printf.sprintf "hint(%s)" hint
  and string_of_boolean = function
    | Bool b -> Bool.to_string b
    | Not e -> Printf.sprintf "not(%s)" (to_string e)
    | And (e1, e2) ->
       Printf.sprintf "and(%s, %s)"
         (to_string e1) (to_string e2)
    | Or (e1, e2) ->
       Printf.sprintf "or(%s, %s)"
         (to_string e1) (to_string e2)
    | Eq (e1, e2) ->
       Printf.sprintf "%s = %s"
         (to_string e1) (to_string e2)
    | Is_member (e1, e2) ->
       Printf.sprintf "member?(%s, %s)"
         (to_string e1) (to_string e2)
    | Is_nothing e ->
       Printf.sprintf "nothing?(%s)"
         (to_string e)
    | Is_something e ->
       Printf.sprintf "something?(%s)"
         (to_string e)
    | Is_empty e ->
       Printf.sprintf "empty?(%s)"
         (to_string e)
    | Is_var e ->
       Printf.sprintf "var?(%s)"
         (to_string e)
    | Is_str e ->
       Printf.sprintf "str?(%s)"
         (to_string e)
    | Is_constructor e ->
       Printf.sprintf "constructor?(%s)"
         (to_string e)
    | Is_binding e ->
       Printf.sprintf "binding?(%s)"
         (to_string e)
    | Is_subst e ->
       Printf.sprintf "subst?(%s)"
         (to_string e)
    | Is_list e ->
       Printf.sprintf "list?(%s)"
         (to_string e)
    | Is_map e ->
       Printf.sprintf "map?(%s)"
         (to_string e)
    | Is_tuple e ->
       Printf.sprintf "tuple?(%s)"
         (to_string e)
    | Is_var_kind (e, kind) ->
       Printf.sprintf "var_kind?(%s, %s)"
         (to_string e) kind
    | Is_op_kind (e, kind) ->
       Printf.sprintf "op_kind?(%s, %s)"
         (to_string e) kind
    | Has_syntax name -> Printf.sprintf "syntax?(%s)" name
  and string_of_term = function
    | Term_nil -> "$nil"
    | Term_var v -> "$" ^ v
    | Term_str s -> Printf.sprintf "$\"%s\"" s
    | Term_constructor (name, e) ->
       Printf.sprintf "(%s %s)"
         (to_string name) (to_string e)
    | Term_binding (var, e) ->
       Printf.sprintf "(%s)%s"
         (to_string var) (to_string e)
    | Term_subst (e, substs) ->
       let substs_str =
         List.map substs ~f:(function
             | Subst_pair (e, var) ->
                Printf.sprintf "%s/%s"
                  (to_string e) var
             | Subst_var (v, k) ->
                Printf.sprintf "%s: %s" v k)
         |> String.concat ~sep:", "
       in Printf.sprintf "%s[%s]" (to_string e) substs_str
    | Term_map_update (key, value, map) ->
       Printf.sprintf "[%s => %s]%s"
         (to_string key) (to_string value) (to_string map)
    | Term_map_domain e -> Printf.sprintf "$dom(%s)" (to_string e)
    | Term_map_range e -> Printf.sprintf "$range(%s)" (to_string e)
    | Term_cons (e1, e2) ->
       Printf.sprintf "(%s :: %s)"
         (to_string e1) (to_string e2)
    | Term_list e -> Printf.sprintf "[%s...]" (to_string e)
    | Term_map (key, value) ->
       Printf.sprintf "{%s => %s}"
         key (to_string value)
    | Term_tuple es ->
       Printf.sprintf "<%s>"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | Term_union es ->
       Printf.sprintf "$union(%s)"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | Term_map_union es ->
       Printf.sprintf "$map_union(%s)"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | Term_zip (e1, e2) ->
       Printf.sprintf "$zip(%s, %s)"
         (to_string e1) (to_string e2)
    | Term_fresh e -> Printf.sprintf "$fresh(%s)" (to_string e)
  and string_of_formula = function
    | Formula_not e -> Printf.sprintf "&not(%s)" (to_string e)
    | Formula_eq (e1, e2) ->
       Printf.sprintf "&(%s = %s)"
         (to_string e1) (to_string e2)
    | Formula_prop (e1, e2) ->
       Printf.sprintf "&(%s %s)"
         (to_string e1) (to_string e2)
    | Formula_member (e1, e2) ->
       Printf.sprintf "&member %s %s"
         (to_string e1) (to_string e2)
    | Formula_subset (e1, e2) ->
       Printf.sprintf "&subset %s %s"
         (to_string e1) (to_string e2)
end

type ctx = {
    type_env: Type.t String.Map.t;
  }

let typeof_var ctx v = match Map.find ctx.type_env v with
  | Some typ -> typ
  | None -> failwith (Printf.sprintf "var '%s' is unbound" v)

let is_reserved_name = function
  | "lan" -> true
  | _ -> false

let reserved_name v =
  if is_reserved_name v then
    failwith
      (Printf.sprintf "cannot bind reserved var name %s" v)

let bind_var ctx v typ =
  reserved_name v;
  let type_env = Map.set ctx.type_env v typ in
  {type_env}

let incompat name ts ts' =
  let expect = match ts' with
    | [] -> ""
    | _ ->
       Printf.sprintf "; expected %s"
         (List.map ts' ~f:Type.to_string
          |> String.concat ~sep:", ")
  in
  failwith
    (Printf.sprintf
       "%s: incompatible type(s) %s%s"
       name
       (List.map ts ~f:Type.to_string
        |> String.concat ~sep:", ")
       expect)

let type_equal pref t =
  let no_equal t =
    failwith
      (Printf.sprintf "%s: no equality predicate exits for type %s"
         pref (Type.to_string t))
  in
  let rec eq t = match t with
    | Type.Lan -> "Language.equal"
    | Type.Syntax -> "Language.Grammar.Category.equal"
    | Type.Rule -> "Language.Rule.equal"
    | Type.Formula -> "Language.Formula.equal"
    | Type.Term -> "Language.Term.equal"
    | Type.String -> "String.equal"
    | Type.Bool -> "Bool.equal"
    | Type.Int -> "Int.equal"
    | Type.List t -> Printf.sprintf "(List.equal %s)" (eq t)
    | Type.Any
      | Type.Tuple _
      | Type.Option _
      | Type.Arrow _ -> no_equal t
  in eq t

let type_compare pref t =
  let no_compare t =
    failwith
      (Printf.sprintf "%s: no comparison predicate exits for type %s"
         pref (Type.to_string t))
  in
  let rec eq t = match t with
    | Type.Lan -> "Language.compare"
    | Type.Syntax -> "Language.Grammar.Category.compare"
    | Type.Rule -> "Language.Rule.compare"
    | Type.Formula -> "Language.Formula.compare"
    | Type.Term -> "Language.Term.compare"
    | Type.String -> "String.compare"
    | Type.Bool -> "Bool.compare"
    | Type.Int -> "Int.compate"
    | Type.List t -> Printf.sprintf "(List.compare %s)" (eq t)
    | Type.Any
      | Type.Tuple _
      | Type.Option _
      | Type.Arrow _ -> no_compare t
  in eq t

let rec compile ctx e = match e with
  | Exp.Self ->
     let typ = typeof_var ctx "self" in
     ("self", typ, ctx)
  | Exp.Var v ->
     let typ = typeof_var ctx v in
     (v, typ, ctx)
  | Exp.Str s ->
     let e' = Printf.sprintf "\"%s\"" s in
     (e', Type.String, ctx)
  | Exp.Str_concat (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.String, Type.String) ->
        let e' = Printf.sprintf "(%s ^ %s)" e1' e2' in
        (e', Type.String, ctx)
     | _ -> incompat "Str_concat" [typ1; typ2] [Type.String; Type.String]
     end
  | Exp.Uppercase e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.String ->
        let e' = Printf.sprintf "(String.uppercase %s)" e' in
        (e', typ, ctx)
     | _ -> incompat "Uppercase" [typ] [Type.String]
     end
  | Exp.Lowercase e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.String ->
        let e' = Printf.sprintf "(String.lowercase %s)" e' in
        (e', typ, ctx)
     | _ -> incompat "Lowercase" [typ] [Type.String]
     end
  | Exp.Int i -> (Int.to_string i, Type.Int, ctx)
  | Exp.Int_str e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Int ->
        let e' = Printf.sprintf "(Int.to_string %s)" e' in
        (e', Type.String, ctx)
     | _ -> incompat "Int_str" [typ] [Type.Int]
     end
  | Exp.Bool_exp b -> compile_bool ctx b
  | Exp.Let {recursive; names; args; exp; body} ->
     (* don't allow users to bind special
      * names used internally by the compiler *)
     List.iter names ~f:reserved_name;
     List.iter args ~f:(fun (v, _) -> reserved_name v);
     let type_env_exp = match String.Map.of_alist args with
       | `Ok m -> m
       | `Duplicate_key a -> 
          failwith
            (Printf.sprintf "Let: duplicate arg %s" a)
     in
     let type_env_exp = match recursive with
       | None -> type_env_exp
       | Some typ ->
          let typs = List.map args ~f:snd in
          let typ = Type.Arrow (typs @ [typ]) in
          let name = List.hd_exn names in
          match Map.add type_env_exp name typ with
          | `Ok m -> m
          | `Duplicate ->
             failwith
               (Printf.sprintf
                  "Let: recursive name %s is redefined" name)
     in
     let ctx_exp =
       let type_env =
         Map.merge_skewed type_env_exp ctx.type_env
           ~combine:(fun ~key t _ -> t)
       in {type_env}
     in
     let (exp', exp_typ, _) = compile ctx_exp exp in
     let ctx_body = match recursive with
       | None ->
          let num_names = List.length names in
          if num_names > 1 then
            match exp_typ with
            | Type.Tuple typs ->
               begin match List.zip names typs with
               | Unequal_lengths -> incompat "Let" typs []
               | Ok m ->
                  List.fold m ~init:ctx ~f:(fun ctx (v, typ) ->
                      bind_var ctx v typ)
               end
            | _ -> failwith "Let: expected tuple, cannot destructure"
          else bind_var ctx (List.hd_exn names) exp_typ
       | Some typ ->
          if Type.equal typ exp_typ then
            let typs = List.map args ~f:snd in
            bind_var ctx (List.hd_exn names) (Type.Arrow (typs @ [typ]))
          else incompat "Let" [exp_typ] [typ]
     in
     let let_str = match recursive with
       | None -> "let"
       | Some _ -> "let rec"
     in
     let args_str = match args with
       | [] -> ""
       | _ -> " " ^ (List.map args ~f:fst |> String.concat ~sep:" ")
     in
     let (body', body_typ, _) = compile ctx_body body in
     let names_str = match names with
       | [] -> failwith "unreachable"
       | x :: [] -> x
       | _ -> Printf.sprintf "(%s)" (String.concat names ~sep:", ")
     in
     let e' =
       Printf.sprintf "%s %s%s = %s in %s"
         let_str names_str args_str exp' body'
     in (e', body_typ, ctx_body)
  | Exp.Apply (e, es) ->
     let (e', typ, _) = compile ctx e in
     let (es', typs, _) = List.map es ~f:(compile ctx) |> List.unzip3 in
     begin match typ with
     | Type.Arrow typs' ->
        let len = List.length typs' in
        if List.(equal Type.equal (take typs' (len - 1)) typs) then
          let e' =
            Printf.sprintf "(%s %s)" e'
              (String.concat es' ~sep:" ")
          in (e', List.last_exn typs', ctx)
        else incompat "Apply" typs typs'
     | _ -> incompat "Apply" [typ] []
     end
  | Exp.Ite (b, e1, e2) ->
     let (b', b_typ, _) = compile ctx b in
     begin match b_typ with
     | Type.Bool ->
        let (e1', typ1, _) = compile ctx e1 in
        let (e2', typ2, _) = compile ctx e2 in
        if Type.equal typ1 typ2 then
          let e' = Printf.sprintf "if %s then %s else %s" b' e1' e2' in
          (e', typ1, ctx)
        else incompat "Ite" [typ1; typ2] []
     | _ -> incompat "Ite" [b_typ] [Type.Bool]
     end
  | Exp.Seq (e1, e2) ->
     let (e1', typ1, ctx1) = compile ctx e1 in
     let (e2', typ2, ctx2) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Lan, Type.Lan) ->
        let e' = Printf.sprintf "let lan = %s in %s" e1' e2' in
        (e', Type.Lan, ctx2)
     | _ -> incompat "Seq" [typ1; typ2] [Type.Lan; Type.Lan]
     end
  | Exp.Tuple es ->
     let (es', typs, _) = List.map es ~f:(compile ctx) |> List.unzip3 in
     let e' = Printf.sprintf "(%s)" (String.concat es' ~sep:", ") in
     (e', Type.Tuple typs, ctx)
  | Exp.List es ->
     let (es', typs, _) = List.map es ~f:(compile ctx) |> List.unzip3 in
     let typ = match List.hd typs with
       | None -> Type.Any
       | Some typ -> typ
     in
     if List.for_all typs ~f:(Type.equal typ) then
       let e' = Printf.sprintf "[%s]" (String.concat es' ~sep:"; ") in
       (e', typ, ctx)
     else incompat "List" typs []
  | Exp.Head e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List typ' ->
        let e' = Printf.sprintf "(List.hd_exn %s)" e' in
        (e', typ', ctx)
     | _ -> incompat "Head" [typ] []
     end
  | Exp.Tail e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List _ ->
        let e' = Printf.sprintf "(List.tl_exn %s)" e' in
        (e', typ, ctx)
     | _ -> incompat "Tail" [typ] []
     end
  | Exp.Last e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List typ' ->
        let e' = Printf.sprintf "(List.last_exn %s)" e' in
        (e', typ', ctx)
     | _ -> incompat "Last" [typ] []
     end
  | Exp.Nth (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.List typ', Type.Int) ->
        let e' = Printf.sprintf "(List.nth_exn %s %s)" e1' e2' in
        (e', typ', ctx)
     | _ -> incompat "Nth" [typ1; typ2] []
     end
  | Exp.List_concat e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.(List (List _ as typ')) ->
        let e' = Printf.sprintf "(List.concat %s)" e' in
        (e', typ', ctx)
     | _ -> incompat "Last" [typ] []
     end
  | Exp.Rev e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List _ ->
        let e' = Printf.sprintf "(List.rev %s)" e' in
        (e', typ, ctx)
     | _ -> incompat "Rev" [typ] []
     end
  | Exp.Dedup e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List typ' ->
        let cmp = type_compare "Dedup" typ' in
        let e' =
          Printf.sprintf "(Aux.dedup_list_stable %s ~compare:%s)"
            e' cmp
        in (e', typ, ctx)
     | _ -> incompat "Rev" [typ] []
     end
  | Exp.Append (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.List typ1', Type.List typ2') when Type.equal typ1' typ2' ->
        let e' = Printf.sprintf "(List.append %s %s)" e1' e2' in
        (e', typ1, ctx)
     | _ -> incompat "Append" [typ1; typ2] []
     end
  | Exp.Diff (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.List typ1', Type.List typ2') when Type.equal typ1' typ2' ->
        let eq = type_equal "Diff" typ1' in
        let e' =
          Printf.sprintf "(Aux.diff_list_stable %s %s ~equal:%s)"
            e1' e2' eq
        in (e', typ1, ctx)
     | _ -> incompat "Diff" [typ1; typ2] []
     end
  | Exp.Zip (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.List typ1', Type.List typ2') ->
        let e' = Printf.sprintf "(List.zip_exn %s %s)" e1' e2' in
        (e', Type.(List (Tuple [typ1; typ2])), ctx)
     | _ -> incompat "Zip" [typ1; typ2] []
     end
  | Exp.Assoc (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match typ2 with
     | Type.(List (Tuple (typ1' :: typ2' :: [])))
          when Type.equal typ1 typ1' ->
        let eq = type_equal "Assoc" typ1 in
        let e' =
          Printf.sprintf "(List.Assoc.find %s %s ~equal:%s)"
            e2' e1' eq
        in (e', typ2', ctx)
     | _ -> incompat "Assoc" [typ1; typ2] []
     end
  | Exp.Nothing -> ("None", Type.(Option Any), ctx)
  | Exp.Something e ->
     let (e', typ, _) = compile ctx e in
     let e' = Printf.sprintf "Some %s" e' in
     (e', Type.Option typ, ctx)
  | Exp.Option_get e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Option typ' ->
        let e' = Printf.sprintf "(Option.value_exn %s)" e' in
        (e', typ', ctx)
     | _ -> incompat "Option_get" [typ] []
     end
  | Exp.Rules_of -> ("(Map.data lan.rules)", Type.(List Rule), ctx)
  | _ -> failwith "unreachable"
and compile_bool ctx b = match b with
  | Exp.Bool b -> (Bool.to_string b, Type.Bool, ctx)
  | Exp.Not e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Bool ->
        let e' = Printf.sprintf "(not %s)" e' in
        (e', typ, ctx)
     | _ -> incompat "Not" [typ] [Type.Bool]
     end
  | Exp.And (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Bool, Type.Bool) ->
        let e' = Printf.sprintf "(%s && %s)" e1' e2' in
        (e', Type.Bool, ctx)
     | _ -> incompat "And" [typ1; typ2] [Type.Bool; Type.Bool]
     end
  | Exp.Or (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Bool, Type.Bool) ->
        let e' = Printf.sprintf "(%s || %s)" e1' e2' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Or" [typ1; typ2] [Type.Bool; Type.Bool]
     end
  | Exp.Eq (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     if Type.equal typ1 typ2 then
       let e' = Printf.sprintf "(%s %s %s)" (type_equal "Eq" typ1) e1' e2' in
       (e', Type.Bool, ctx)
     else incompat "Eq" [typ1; typ2] []
  | Exp.Is_member (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match typ2 with
     | Type.List typ2' when Type.equal typ1 typ2' ->
        let eq = type_equal "Is_member" typ1 in
        let e' = Printf.sprintf "(List.mem %s %s ~equal:%s)" e2' e1' eq in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_member" [typ1; typ2] [typ1; Type.List typ1]
     end
  | Exp.Is_nothing e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Option _ ->
        let e' = Printf.sprintf "(Option.is_none %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_nothing" [typ] []
     end
  | Exp.Is_something e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Option _ ->
        let e' = Printf.sprintf "(Option.is_some %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_something" [typ] []
     end
  | Exp.Is_empty e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List _ ->
        let e' = Printf.sprintf "(List.is_empty %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_empty" [typ] []
     end
  | Exp.Is_var e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_var %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_var" [typ] [Type.Term]
     end
  | Exp.Is_str e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_str %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_str" [typ] [Type.Term]
     end
  | Exp.Is_constructor e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_constructor %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_constructor" [typ] [Type.Term]
     end
  | Exp.Is_binding e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_binding %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_binding" [typ] [Type.Term]
     end
  | Exp.Is_subst e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_subst %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_subst" [typ] [Type.Term]
     end
  | Exp.Is_list e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_list %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_list" [typ] [Type.Term]
     end
  | Exp.Is_map e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_map %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_map" [typ] [Type.Term]
     end
  | Exp.Is_tuple e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(Language.Term.is_tuple %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_tuple" [typ] [Type.Term]
     end
  | Exp.Is_var_kind (e, k) ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' =
          Printf.sprintf
            {|
             begin match %s with
             | Language.Term.Var v -> Language.is_var_kind lan v %s
             | _ -> failwith \"Is_var_kind: expected var\"
             end
             |}
            e' k
        in (e', Type.Bool, ctx)
     | _ -> incompat "Is_var_kind" [typ] [Type.Term]
     end
  | Exp.Is_op_kind (e, k) ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.String ->
        let e' = Printf.sprintf "(Language.is_op_kind lan %s %s)" e' k in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_var_kind" [typ] [Type.String]
     end
  | Exp.Has_syntax s ->
     let e' = Printf.sprintf "(Map.mem lan.grammar \"%s\")" s in
     (e', Type.Bool, ctx)
