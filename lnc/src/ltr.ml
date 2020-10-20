open Core_kernel

module Type = struct
  type t =
    | Var of string
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
    | Arrow of t list [@@deriving equal, compare, sexp]

  let rec to_string = function
    | Var v -> "'" ^ v
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

  let rec vars t = match t with
    | Var _ -> [t]
    | Tuple ts
      | Arrow ts ->
       List.map ts ~f:vars
       |> List.concat
       |> List.dedup_and_sort ~compare
    | Option t
      | List t -> vars t
    | _ -> []

  let rec substitute t ((a, b) as sub) =
    let f t = substitute t sub in
    if equal t a then b else
      match t with
      | Var _
        | Lan
        | Syntax
        | Rule
        | Formula
        | Term
        | String
        | Bool
        | Int -> t
      | Tuple ts -> Tuple (List.map ts ~f)
      | Option t -> Option (f t)
      | List t -> List (f t)
      | Arrow ts -> Arrow (List.map ts ~f)
end

module Type_unify = struct
  module Solution = struct
    type t =
      | Sub of Type.t * Type.t
      | Soln of Type.t [@@deriving equal, compare, sexp]

    let is_sub = function
      | Sub _ -> true
      | _ -> false

    let is_soln = function
      | Soln _ -> true
      | _ -> false
  end

  module Solution_comparable = struct
    include Solution
    include Comparable.Make(Solution)
  end

  module Solution_set = Set.Make(Solution_comparable)

  let run ?(init_state = []) typs = match typs with
    | [] when List.is_empty init_state -> None
    | t :: [] when List.is_empty init_state -> Some t
    | _ ->
       let state = match typs with
         | t :: [] -> Solution_set.singleton (Solution.Soln t)
         | _ ->
            Aux.interleave_pairs_of_list typs
            |> List.map ~f:(fun (t1, t2) -> Solution.Sub (t1, t2))
            |> Solution_set.of_list
       in
       let state = match init_state with
         | [] -> state
         | pairs ->
            List.map pairs ~f:(fun (t1, t2) -> Solution.Sub (t1, t2))
            |> Solution_set.of_list
            |> Solution_set.union state
       in
       let add_sub state (t1, t2) = Set.add state (Solution.Sub (t1, t2)) in
       (* this is ugly, but should work in practice *)
       let toplevel = ref true in
       let add_soln state typ =
         if !toplevel
         then (toplevel := false; Set.add state (Solution.Soln typ))
         else state
       in
       let rec loop state = match Set.find state ~f:Solution.is_sub with
         | Some (Solution.Sub (t1, t2) as soln) ->
            let zip_and_loop state ts ts' = match List.zip ts ts' with
              | Unequal_lengths -> None
              | Ok subs -> List.fold subs ~init:state ~f:add_sub |> loop
            in
            let state' = Set.remove state soln in
            let open Type in
            begin match (t1, t2) with
            | (Lan, Lan)
              | (Syntax, Syntax)
              | (Rule, Rule)
              | (Formula, Formula)
              | (Term, Term)
              | (String, String)
              | (Bool, Bool)
              | (Int, Int) -> loop (add_soln state' t1)
            | (Tuple ts, Tuple ts')
              | (Arrow ts, Arrow ts') ->
               let state' = add_soln state' t1 in
               zip_and_loop state' ts ts'
            | (Option t1', Option t2')
              | (List t1', List t2') ->
               let state' = add_soln state' t1 in
               zip_and_loop state' [t1'] [t2']
            | (Var v1, Var v2) when String.equal v1 v2 -> loop state'
            | (_, Var _) -> add_sub state' (t2, t1) |> loop
            | (Var _, _) ->
               let tvars = vars t2 in
               if not (List.mem tvars t1 ~equal) then
                 let tvars =
                   Set.to_list state'
                   |> List.map ~f:(function
                          | Solution.Sub (t1, t2) -> vars t1 @ vars t2
                          | Solution.Soln t -> vars t)
                   |> List.concat
                   |> List.dedup_and_sort ~compare
                 in
                 if List.mem tvars t1 ~equal then
                   let sub = (t1, t2) in
                   Solution_set.map state ~f:(function
                       | Solution.Sub (t1, t2) ->
                          Solution.Sub (
                              substitute t1 sub,
                              substitute t2 sub)
                       | Solution.Soln t ->
                          Solution.Soln (substitute t sub))
                   |> loop
                 else loop state'
               else None
            | _ -> None
            end
         | _ -> Some state
       in
       Option.(
         loop state >>= fun state ->
         Set.find state ~f:Solution.is_soln >>= function
         | Solution.Soln t -> return t
         | _ -> failwith "unreachable")
end

module Exp = struct
  module Pattern = struct
    type t =
      | Wildcard
      | Var of string
      | Str of string
      | Term of term
      | Formula of formula
      | List of t list
      | Cons of t * t
      | Tuple of t list
      | Nothing
      | Something of t
    and term =
      | Term_nil
      | Term_var of string
      | Term_var_pat of t
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
      | Term_tuple of t
      | Term_union of t
      | Term_map_union of t
      | Term_zip of t * t
      | Term_fresh of t
    and subst =
      | Subst_pair of t * string
      | Subst_var of string
    and formula =
      | Formula_not of t
      | Formula_eq of t * t
      | Formula_prop of t * t
      | Formula_member of t * t
      | Formula_subset of t * t

    let rec to_string = function
      | Wildcard -> "_"
      | Var v -> v
      | Str s -> Printf.sprintf "\"%s\"" s
      | Term t -> string_of_term t
      | Formula f -> string_of_formula f
      | List ps ->
         Printf.sprintf "[%s]"
           (List.map ps ~f:to_string
            |> String.concat ~sep:", ")
      | Cons (p1, p2) ->
         Printf.sprintf "%s :: %s" (to_string p1) (to_string p2)
      | Tuple ps ->
         Printf.sprintf "(%s)"
           (List.map ps ~f:to_string
            |> String.concat ~sep:", ")
      | Nothing -> "none"
      | Something p -> Printf.sprintf "some(%s)" (to_string p)
    and string_of_term = function
      | Term_nil -> "$nil"
      | Term_var v -> "$" ^ v
      | Term_var_pat p -> "$!" ^ (to_string p)
      | Term_str s -> "$" ^ (Printf.sprintf "\"%s\"" s)
      | Term_constructor (p1, p2) ->
         Printf.sprintf "(%s %s)" (to_string p1) (to_string p2)
      | Term_binding (p1, p2) ->
         Printf.sprintf "(%s)%s" (to_string p1) (to_string p2)
      | Term_subst (p, substs) ->
         Printf.sprintf "%s[%s]" (to_string p)
           (List.map substs ~f:string_of_subst
            |> String.concat ~sep:", ")
      | Term_map_update (key, value, map) ->
         Printf.sprintf "[%s => %s]%s"
           (to_string key) (to_string value) (to_string map)
      | Term_map_domain p -> Printf.sprintf "$dom(%s)" (to_string p)
      | Term_map_range p -> Printf.sprintf "$range(%s)" (to_string p)
      | Term_cons (p1, p2) ->
         Printf.sprintf "$(%s :: %s)" (to_string p1) (to_string p2)
      | Term_list p -> Printf.sprintf "[%s...]" (to_string p)
      | Term_map (var, p) -> Printf.sprintf "{%s => %s}" var (to_string p)
      | Term_tuple p -> Printf.sprintf "<%s>" (to_string p)
      | Term_union p -> Printf.sprintf "$union(%s)" (to_string p)
      | Term_map_union p -> Printf.sprintf "$map_union(%s)" (to_string p)
      | Term_zip (p1, p2) ->
         Printf.sprintf "$zip(%s, %s)" (to_string p1) (to_string p2)
      | Term_fresh p -> Printf.sprintf "$fresh(%s)" (to_string p)
    and string_of_subst = function
      | Subst_pair (p, var) -> Printf.sprintf "%s/%s" (to_string p) var
      | Subst_var var -> Printf.sprintf "%s" var
    and string_of_formula = function
      | Formula_not p -> Printf.sprintf "&not(%s)" (to_string p)
      | Formula_eq (p1, p2) ->
         Printf.sprintf "&(%s = %s)" (to_string p1) (to_string p2)
      | Formula_prop (p1, p2) ->
         Printf.sprintf "&(%s %s)" (to_string p1) (to_string p2)
      | Formula_member (p1, p2) ->
         Printf.sprintf "&member(%s, %s)"
           (to_string p1) (to_string p2)
      | Formula_subset (p1, p2) ->
         Printf.sprintf "&subset(%s, %s)"
           (to_string p1) (to_string p2)
  end
  
  type t =
    (* builtin *)
    | Self
    | Unify of {
        normalize: bool;
        term_subs: t;
        formula_subs: t;
        candidates: t;
        proven: t;
      }
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
        recursive: bool;
        names: string list;
        args: (string * Type.t) list;
        ret: Type.t option;
        exp: t;
        body: t;
      }
    | Apply of t * t list
    | Ite of t * t * t
    | Seq of t * t
    | Select of {
        keep: bool;
        field: t;
        pattern: Pattern.t;
        body: t;
      }
    | Match of {
        exp: t;
        cases: (Pattern.t * t) list;
      }
    (* tuple operations *)
    | Tuple of t list
    (* list operations *)
    | List of t list
    | Cons of t * t
    | Head of t
    | Tail of t
    | Last of t
    | Nth of t * t
    | List_concat of t
    | Rev of t
    | Dedup of t
    | Append of t * t
    | Diff of t * t
    | Intersect of t * t
    | Zip of t * t
    | Assoc of t * t
    | Interleave_pairs of t
    | Length of t
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
    | Set_syntax_terms of {
        name: string;
        terms: t;
      }
    | Remove_syntax of string
    | Meta_var_of of string
    | Syntax_terms_of of string
    (* relation operations *)
    | New_relation of string * t
    | Relations_of
    | Set_relations of t
    | Remove_relation of string
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
    | Add_rules of t
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
    | Is_const_var of t
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
    | Starts_with of t * t
    | Ends_with of t * t
  and term = 
    | Term_nil
    | Term_var of string
    | Term_var_exp of t
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
    | Term_tuple of t
    | Term_union of t
    | Term_map_union of t
    | Term_zip of t * t
    | Term_fresh of t
  and subst =
    | Subst_pair of t * string
    | Subst_var of string * string
  and formula =
    | Formula_not of t
    | Formula_eq of t * t
    | Formula_prop of t * t
    | Formula_member of t * t
    | Formula_subset of t * t

  let rec to_string = function
    | Self -> "self"
    | Unify {normalize; term_subs; formula_subs; candidates; proven} ->
       let name_sub = if normalize then "unify_normalize" else "unify" in
       Printf.sprintf "%s(%s, %s, %s, %s)"
         name_sub
         (to_string term_subs)
         (to_string formula_subs)
         (to_string candidates)
         (to_string proven)
    | Var v -> v
    | Str s -> Printf.sprintf "\"%s\"" s
    | Str_concat (e1, e2) ->
       Printf.sprintf "%s ^ %s" (to_string e1) (to_string e2)
    | Uppercase e -> Printf.sprintf "uppercase(%s)" (to_string e)
    | Lowercase e -> Printf.sprintf "lowercase(%s)" (to_string e)
    | Int n -> Int.to_string n
    | Int_str e -> Printf.sprintf "int_str(%s)" (to_string e)
    | Bool_exp b -> string_of_boolean b
    | Let {recursive; names; args; ret; exp; body} ->
       let args_str = match args with
         | [] -> " "
         | _ ->
            List.map args ~f:(fun (a, t) ->
                Printf.sprintf "(%s: %s)"
                  a (Type.to_string t))
            |> String.concat ~sep:" "
            |> Printf.sprintf " %s"
       in
       let let_str = if recursive then "let rec" else "let" in
       let ret_typ = match ret with
         | None -> " "
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
         let_str names_str args_str ret_typ
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
       let op_str = if keep then ">>!" else ">>" in
       Printf.sprintf "%s %s %s >> (%s)"
         field_str op_str (Pattern.to_string pattern) (to_string body)
    | Match {exp; cases} ->
       let cases_str =
         List.map cases ~f:(fun (p, e) ->
             Printf.sprintf "%s -> (%s)"
               (Pattern.to_string p) (to_string e))
         |> String.concat ~sep:" | "
       in Printf.sprintf "match %s with %s" (to_string exp) cases_str
    | Tuple es ->
       Printf.sprintf "(%s)"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | List es ->
       Printf.sprintf "[%s%s]"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
         (if List.length es = 1 then "." else "")
    | Cons (e1, e2) ->
       Printf.sprintf "%s :: %s" (to_string e1) (to_string e2)
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
    | Intersect (e1, e2) ->
       Printf.sprintf "intersect(%s, %s)"
         (to_string e1) (to_string e2)
    | Zip (e1, e2) ->
       Printf.sprintf "zip(%s, %s)"
         (to_string e1) (to_string e2)
    | Assoc (e1, e2) ->
       Printf.sprintf "assoc(%s, %s)"
         (to_string e1) (to_string e2)
    | Interleave_pairs e ->
       Printf.sprintf "interleave_pairs(%s)" (to_string e)
    | Length e -> Printf.sprintf "length(%s)" (to_string e)       
    | Nothing -> "none"
    | Something e -> Printf.sprintf "some(%s)" (to_string e)
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
       Printf.sprintf "%s %s ::=%s%s."
         name meta_var extend_str
         (List.map terms ~f:to_string
          |> String.concat ~sep:" | ")
    | Set_syntax_terms {name; terms} ->
       Printf.sprintf "set_syntax(%s, %s)" name (to_string terms)
    | Remove_syntax name -> Printf.sprintf "remove_syntax(%s)" name
    | Meta_var_of name -> Printf.sprintf "meta_var(%s)" name
    | Syntax_terms_of name -> Printf.sprintf "syntax(%s)" name
    | New_relation (predicate, e) ->
       Printf.sprintf "add_relation(\"%s\" %s)" predicate (to_string e)
    | Relations_of -> "relations"
    | Set_relations e ->
       Printf.sprintf "set_relations(%s)" (to_string e)
    | Remove_relation predicate ->
       Printf.sprintf "remove_relation(\"%s\")" predicate
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
    | Add_rules e -> Printf.sprintf "add_rules(%s)" (to_string e)
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
       Printf.sprintf "(%s && %s)" (to_string e1) (to_string e2)
    | Or (e1, e2) ->
       Printf.sprintf "(%s || %s)" (to_string e1) (to_string e2)
    | Eq (e1, e2) ->
       Printf.sprintf "%s = %s"
         (to_string e1) (to_string e2)
    | Is_member (e1, e2) ->
       Printf.sprintf "member?(%s, %s)"
         (to_string e1) (to_string e2)
    | Is_nothing e ->
       Printf.sprintf "none?(%s)"
         (to_string e)
    | Is_something e ->
       Printf.sprintf "some?(%s)"
         (to_string e)
    | Is_empty e ->
       Printf.sprintf "empty?(%s)"
         (to_string e)
    | Is_var e ->
       Printf.sprintf "var?(%s)"
         (to_string e)
    | Is_const_var e ->
       Printf.sprintf "const_var?(%s)"
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
    | Starts_with (e1, e2) ->
       Printf.sprintf "starts_with?(%s, %s)" (to_string e1) (to_string e2)
    | Ends_with (e1, e2) ->
       Printf.sprintf "ends_with?(%s, %s)" (to_string e1) (to_string e2)
  and string_of_term = function
    | Term_nil -> "$nil"
    | Term_var v -> "$" ^ v
    | Term_var_exp e -> "$!" ^ (to_string e)
    | Term_str s -> Printf.sprintf "$\"%s\"" s
    | Term_constructor (name, e) ->
       Printf.sprintf "(%s %s)"
         (to_string name) (to_string e)
    | Term_binding (var, e) ->
       Printf.sprintf "(%s)%s"
         (to_string var) (to_string e)
    | Term_subst (e, substs) ->
       let substs_str =
         List.map substs ~f:string_of_subst
         |> String.concat ~sep:", "
       in Printf.sprintf "%s[%s]" (to_string e) substs_str
    | Term_map_update (key, value, map) ->
       Printf.sprintf "[%s => %s]%s"
         (to_string key) (to_string value) (to_string map)
    | Term_map_domain e -> Printf.sprintf "$dom(%s)" (to_string e)
    | Term_map_range e -> Printf.sprintf "$range(%s)" (to_string e)
    | Term_cons (e1, e2) ->
       Printf.sprintf "$(%s :: %s)"
         (to_string e1) (to_string e2)
    | Term_list e -> Printf.sprintf "[%s...]" (to_string e)
    | Term_map (key, value) ->
       Printf.sprintf "{%s => %s}"
         key (to_string value)
    | Term_tuple e -> Printf.sprintf "<%s>" (to_string e)
    | Term_union e -> Printf.sprintf "$union(%s)" (to_string e)
    | Term_map_union e -> Printf.sprintf "$map_union(%s)" (to_string e)
    | Term_zip (e1, e2) ->
       Printf.sprintf "$zip(%s, %s)"
         (to_string e1) (to_string e2)
    | Term_fresh e -> Printf.sprintf "$fresh(%s)" (to_string e)
  and string_of_subst = function
    | Subst_pair (e, var) -> Printf.sprintf "%s/%s" (to_string e) var
    | Subst_var (v, k) -> Printf.sprintf "%s: %s" v k
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
    mutable type_vars: String.Set.t;
  }

let ctx_singleton v typ =
  let type_env = String.Map.singleton v typ in
  let type_vars = String.Set.empty in
  {type_env; type_vars}

let fresh_type_var ctx =
  let rec aux i =
    let v = "T" ^ Int.to_string i in
    if Set.mem ctx.type_vars v
    then aux (succ i)
    else (ctx.type_vars <- Set.add ctx.type_vars v; Type.Var v)
  in aux 1

let typeof_var ctx v = match Map.find ctx.type_env v with
  | Some typ -> typ
  | None -> failwith (Printf.sprintf "var '%s' is unbound" v)

let is_reserved_name = function
  | "lan"
    | "lan_vars"
    | "lan_fresh_var" -> true
  | _ -> false

let reserved_name v =
  if is_reserved_name v then
    failwith
      (Printf.sprintf "cannot bind reserved var name %s" v)

let bind_var ctx v typ =
  reserved_name v;
  let type_env = Map.set ctx.type_env v typ in
  {ctx with type_env}

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
    | Type.Lan -> "L.equal"
    | Type.Syntax -> "C.equal"
    | Type.Rule -> "R.equal"
    | Type.Formula -> "F.equal"
    | Type.Term -> "T.equal"
    | Type.String -> "String.equal"
    | Type.Bool -> "Bool.equal"
    | Type.Int -> "Int.equal"
    | Type.List t -> Printf.sprintf "(List.equal %s)" (eq t)
    | Type.Var _
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
    | Type.Lan -> "L.compare"
    | Type.Syntax -> "C.compare"
    | Type.Rule -> "R.compare"
    | Type.Formula -> "F.compare"
    | Type.Term -> "T.compare"
    | Type.String -> "String.compare"
    | Type.Bool -> "Bool.compare"
    | Type.Int -> "Int.compate"
    | Type.List t -> Printf.sprintf "(List.compare %s)" (eq t)
    | Type.Var _
      | Type.Tuple _
      | Type.Option _
      | Type.Arrow _ -> no_compare t
  in eq t

let bind_var_pat ctx v typ =
  reserved_name v;
  let type_env = Map.set ctx.type_env v typ in
  {ctx with type_env}

let merge_ctx ctx1 ctx2 =
  let type_env =
    Map.merge_skewed ctx1.type_env ctx2.type_env
      ~combine:(fun ~key typ1 typ2 ->
        (* fixme: we need to distinguish between vars that were bound
         * in the pattern and vars that we captured from outside *)
        if Type.equal typ1 typ2 then typ1 else
          failwith
            (Printf.sprintf "incompatible types (%s, %s) for pattern var %s"
               (Type.to_string typ1) (Type.to_string typ2) key))
  in
  let ctx = {ctx1 with type_env} in
  ctx.type_vars <- Set.union ctx.type_vars ctx2.type_vars;
  ctx

let rec compile_pattern ctx expected_typ p = match p with
  | Exp.Pattern.Wildcard -> ("_", expected_typ, ctx)
  | Exp.Pattern.Var v -> (v, expected_typ, bind_var_pat ctx v expected_typ)
  | Exp.Pattern.Str s -> (Printf.sprintf "\"%s\"" s, Type.String, ctx)
  | Exp.Pattern.Term t -> compile_pattern_term ctx t
  | Exp.Pattern.Formula f -> compile_pattern_formula ctx f
  | Exp.Pattern.List ps ->
     begin match expected_typ with
     | Type.List typ ->
        let (ps', typs, ctxs) =
          List.map ps ~f:(compile_pattern ctx typ)
          |> List.unzip3
        in
        let typ' = match typs with
          | [] -> Some expected_typ
          | _ -> Type_unify.run typs
        in
        begin match typ' with
        | None -> incompat "List pattern" typs []
        | Some _ ->
           let p' =
             Printf.sprintf "[%s]"
               (String.concat ps' ~sep:"; ")
           in
           let ctx = match ctxs with
             | [] -> ctx
             | _ ->
                let init = List.hd_exn ctxs in
                List.fold (List.tl_exn ctxs) ~init ~f:(fun ctx ctx' ->
                    merge_ctx ctx ctx')
           in (p', expected_typ, ctx)
        end
     | _ ->
        failwith
          (Printf.sprintf
             "List pattern: incompatible with expected type %s"
             (Type.to_string expected_typ))
     end
  | Exp.Pattern.Cons (p1, p2) ->
     begin match expected_typ with
     | Type.List typ ->
        let (p1', typ1, ctx1) = compile_pattern ctx typ p1 in
        let (p2', typ2, ctx2) = compile_pattern ctx expected_typ p2 in
        begin match typ2 with
        | Type.List typ'
              when Option.is_some (Type_unify.run [typ; typ']) ->
           let p' = Printf.sprintf "((%s) :: (%s))" p1' p2' in
           (p', expected_typ, merge_ctx ctx1 ctx2)             
        | _ -> incompat "Cons pattern" [typ1; typ2] [typ; expected_typ]
        end
     | _ ->
        failwith
          (Printf.sprintf
             "Cons pattern: incompatible with expected type %s"
             (Type.to_string expected_typ))
     end
  | Exp.Pattern.Tuple ps ->
     let incompat' () =
       failwith
         (Printf.sprintf
            "Tuple pattern: incompatible with expected type %s"
            (Type.to_string expected_typ))
     in
     begin match expected_typ with
     | Type.Tuple typs ->
        begin match List.zip ps typs with
        | Ok ps_typs ->
           let (ps', typs', ctxs) =
             List.map ps_typs ~f:(fun (p, typ) ->
                 compile_pattern ctx typ p)
             |> List.unzip3
           in
           if List.equal Type.equal typs typs' then
             let p' =
               Printf.sprintf "(%s)"
                 (String.concat ps' ~sep:", ")
             in
             let ctx =
               let init = List.hd_exn ctxs in
               List.fold (List.tl_exn ctxs) ~init ~f:(fun ctx ctx' ->
                   merge_ctx ctx ctx')
             in (p', expected_typ, ctx)
           else incompat "Tuple pattern" typs' typs
        | Unequal_lengths -> incompat' ()
        end
     | _ -> incompat' ()
     end
  | Exp.Pattern.Nothing ->
     begin match expected_typ with
     | Type.Option _ -> ("None", expected_typ, ctx)
     | _ ->
        failwith
          (Printf.sprintf
             "Nothing pattern: incompatible with expected type %s"
             (Type.to_string expected_typ))
     end
  | Exp.Pattern.Something p ->
     begin match expected_typ with
     | Type.Option typ' ->
        let (p', typ, ctx) = compile_pattern ctx typ' p in
        begin match Type_unify.run [typ'; typ] with
        | None -> incompat "Something pattern" [typ] [typ']
        | Some _ ->
           let p' = Printf.sprintf "(Some (%s))" p' in
           (p', expected_typ, ctx)
        end
     | _ ->
        failwith
          (Printf.sprintf
             "Something pattern: incompatible with expected type %s"
             (Type.to_string expected_typ))
     end
and compile_pattern_term ctx t = match t with
  | Exp.Pattern.Term_nil -> ("T.Nil", Type.Term, ctx)
  | Exp.Pattern.Term_var v ->
     let p' = Printf.sprintf "(T.Var \"%s\")" v in
     (p', Type.Term, ctx)
  | Exp.Pattern.Term_var_pat p ->
     let (p', typ, ctx) = compile_pattern ctx Type.String p in
     begin match typ with
     | Type.String ->
        let p' = Printf.sprintf "(T.Var %s)" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_var_pat" [typ] [Type.String]
     end
  | Exp.Pattern.Term_str s ->
     let p' = Printf.sprintf "(T.Str \"%s\")" s in
     (p', Type.Term, ctx)
  | Exp.Pattern.Term_constructor (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.String p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.(List Term) p2 in
     begin match (typ1, typ2) with
     | (Type.String, Type.(List Term)) ->
        let p' =
          Printf.sprintf
            "(T.(Constructor {name = %s; args = %s}))"
            p1' p2'
        in (p', Type.Term, merge_ctx ctx1 ctx2)
     | _ ->
        incompat "Term_constructor pattern"
          [typ1; typ2] Type.[String; List Term]
     end
  | Exp.Pattern.Term_binding (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.String p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.Term p2 in
     begin match (typ1, typ2) with
     | (Type.String, Type.Term) ->
        let ctx = merge_ctx ctx1 ctx2 in
        let p' = Printf.sprintf "(T.Binding {var = %s; body = %s})" p1' p2' in
        (p', Type.Term, ctx)
     | _ ->
        incompat "Term_binding pattern"
           [typ1; typ2] Type.[String; Term]
     end     
  | Exp.Pattern.Term_subst (p, substs) ->
     let (p', typ, ctx) = compile_pattern ctx Type.Term p in
     begin match typ with
     | Type.Term ->
        let (substs', substs_ctx) =
          List.map substs ~f:(compile_pattern_subst ctx)
          |> List.unzip
        in
        let ctx =
          let init = List.hd_exn substs_ctx in
          List.fold (List.tl_exn substs_ctx) ~init ~f:(fun ctx ctx' ->
              merge_ctx ctx ctx')
        in
        let p' =
          Printf.sprintf
            "(T.Subst {body = %s; substs = [%s]})"
            p' (String.concat substs' ~sep:"; ")
        in (p', Type.Term, ctx)
     | _ -> incompat "Term_subst pattern (body)" [typ] Type.[Term]
     end
  | Exp.Pattern.Term_map_update (key, value, map) ->
     let (key', key_typ, key_ctx) = compile_pattern ctx Type.Term key in
     let (value', value_typ, value_ctx) = compile_pattern ctx Type.Term value in
     let (map', map_typ, map_ctx) = compile_pattern ctx Type.Term map in
     begin match (key_typ, value_typ, map_typ) with
     | (Type.Term, Type.Term, Type.Term) ->
        let ctx = merge_ctx (merge_ctx key_ctx value_ctx) map_ctx in
        let p' =
          Printf.sprintf "(T.Map_update {key = %s; value = %s; map = %s})"
            key' value' map'
        in (p', Type.Term, ctx)
     | _ ->
        incompat "Term_map_update pattern"
          [key_typ; value_typ; map_typ] Type.[Term; Term; Term]
     end
  | Exp.Pattern.Term_map_domain p ->
     let (p', typ, ctx) = compile_pattern ctx Type.Term p in
     begin match typ with
     | Type.Term ->
        let p' = Printf.sprintf "(T.Map_domain (%s))" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_map_domain pattern" [typ] Type.[Term]
     end
  | Exp.Pattern.Term_map_range p ->
     let (p', typ, ctx) = compile_pattern ctx Type.Term p in
     begin match typ with
     | Type.Term ->
        let p' = Printf.sprintf "(T.Map_range (%s))" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_map_range pattern" [typ] Type.[Term]
     end
  | Exp.Pattern.Term_cons (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.Term p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.Term p2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let ctx = merge_ctx ctx1 ctx2 in
        let p' = Printf.sprintf "(T.Cons (%s, %s))" p1' p2' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_cons pattern" [typ1; typ2] Type.[Term; Term]
     end
  | Exp.Pattern.Term_list p ->
     let (p', typ, ctx) = compile_pattern ctx Type.Term p in
     begin match typ with
     | Type.Term ->
        let p' = Printf.sprintf "(T.List (%s))" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_list pattern" [typ] Type.[Term]
     end
  | Exp.Pattern.Term_map (var, p) ->
     let (p', typ, ctx) = compile_pattern ctx Type.Term p in
     begin match typ with
     | Type.Term ->
        let ctx = merge_ctx ctx (ctx_singleton var Type.String) in
        let p' = Printf.sprintf "(T.Map {key = %s; value = %s})" var p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_map pattern (value)" [typ] Type.[Term]
     end
  | Exp.Pattern.Term_tuple p ->
     let (p', typ, ctx) = compile_pattern ctx Type.(List Term) p in
     begin match typ with
     | Type.(List Term) ->
        let p' = Printf.sprintf "(T.Tuple (%s))" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_tuple pattern" [typ] Type.[List Term]
     end
  | Exp.Pattern.Term_union p ->
     let (p', typ, ctx) = compile_pattern ctx Type.(List Term) p in
     begin match typ with
     | Type.(List Term) ->
        let p' = Printf.sprintf "(T.Union (%s))" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_union pattern" [typ] Type.[List Term]
     end
  | Exp.Pattern.Term_map_union p ->
     let (p', typ, ctx) = compile_pattern ctx Type.(List Term) p in
     begin match typ with
     | Type.(List Term) ->
        let p' = Printf.sprintf "(T.Map_union (%s))" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_map_union pattern" [typ] Type.[List Term]
     end
  | Exp.Pattern.Term_zip (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.Term p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.Term p2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let ctx = merge_ctx ctx1 ctx2 in
        let p' = Printf.sprintf "(T.Zip (%s, %s))" p1' p2' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_zip pattern" [typ1; typ2] Type.[Term; Term]
     end
  | Exp.Pattern.Term_fresh p ->
     let (p', typ, ctx) = compile_pattern ctx Type.Term p in
     begin match typ with
     | Type.Term ->
        let p' = Printf.sprintf "(T.Fresh (%s))" p' in
        (p', Type.Term, ctx)
     | _ -> incompat "Term_fresh pattern" [typ] Type.[Term]
     end
and compile_pattern_subst ctx s = match s with
  | Exp.Pattern.Subst_pair (p, var) ->
     let (p', typ, ctx) = compile_pattern ctx Type.Term p in
     let ctx = merge_ctx ctx (ctx_singleton var Type.Term) in
     let p' = Printf.sprintf "(T.Subst_pair (%s, %s))" p' var in
     (p', ctx)
  | Exp.Pattern.Subst_var var ->
     let p' = Printf.sprintf "(T.Subst_var (%s, _))" var in
     let ctx =
       merge_ctx ctx
         (ctx_singleton var Type.(List (Tuple [Term; Term])))
     in (p', ctx)
and compile_pattern_formula ctx f = match f with
  | Exp.Pattern.Formula_not p ->
     let (p', typ, ctx) = compile_pattern ctx Type.Formula p in
     begin match typ with
     | Type.Formula ->
        let p' = Printf.sprintf "(F.Not %s)" p' in
        (p', typ, ctx)
     | _ -> incompat "Formula_not pattern" [typ] [Type.Formula]
     end
  | Exp.Pattern.Formula_eq (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.Term p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.Term p2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let p' = Printf.sprintf "(F.Eq (%s, %s))" p1' p2' in
        (p', Type.Formula, merge_ctx ctx1 ctx2)
     | _ -> incompat "Formula_eq pattern" [typ1; typ2] [Type.Term; Type.Term]
     end
  | Exp.Pattern.Formula_prop (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.String p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.(List Term) p2 in
     begin match (typ1, typ2) with
     | (Type.String, Type.(List Term)) ->
        let p' =
          Printf.sprintf
            "(F.(Prop {predicate = %s; args = %s}))"
            p1' p2'
        in (p', Type.Formula, merge_ctx ctx1 ctx2)
     | _ ->
        incompat "Formula_prop pattern"
          [typ1; typ2] [Type.String; Type.(List Term)]
     end
  | Exp.Pattern.Formula_member (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.Term p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.Term p2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let p' =
          Printf.sprintf
            "(F.(Member {element = %s; collection = %s}))"
            p1' p2'
        in (p', Type.Formula, merge_ctx ctx1 ctx2)
     | _ -> incompat "Formula_member pattern" [typ1; typ2] [Type.Term; Type.Term]
     end
  | Exp.Pattern.Formula_subset (p1, p2) ->
     let (p1', typ1, ctx1) = compile_pattern ctx Type.Term p1 in
     let (p2', typ2, ctx2) = compile_pattern ctx Type.Term p2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let p' = Printf.sprintf "(F.(Subset {sub = %s; super = %s}))" p1' p2' in
        (p', Type.Formula, merge_ctx ctx1 ctx2)
     | _ -> incompat "Formula_subset pattern" [typ1; typ2] [Type.Term; Type.Term]
     end

let rec compile ctx e = match e with
  | Exp.Self -> ("self", typeof_var ctx "self", ctx)
  | Exp.Unify {normalize; term_subs; formula_subs; candidates; proven} ->
     let (term_subs', term_subs_typ, _) = compile ctx term_subs in
     let term_subs_typ_exp = Type.(List (Tuple [Term; Term])) in
     begin match Type_unify.run [term_subs_typ_exp; term_subs_typ] with
     | Some typ when Type.equal typ term_subs_typ_exp ->
       let (formula_subs', formula_subs_typ, _) = compile ctx formula_subs in
       let formula_subs_typ_exp = Type.(List (Tuple [Formula; Formula])) in
       begin match Type_unify.run [formula_subs_typ_exp; formula_subs_typ] with
       | Some typ when Type.equal typ formula_subs_typ_exp ->
          let (candidates', candidates_typ, _) = compile ctx candidates in
          let candidates_typ_exp = Type.(List Formula) in
          begin match Type_unify.run [candidates_typ_exp; candidates_typ] with
          | Some typ when Type.equal typ candidates_typ_exp ->
             let (proven', proven_typ, _) = compile ctx proven in
             let proven_typ_exp = Type.(List Formula) in
             begin match Type_unify.run [proven_typ_exp; proven_typ] with
             | Some typ when Type.equal typ proven_typ_exp ->
                let term_sub_soln =
                  Printf.sprintf
                    "(List.map (%s) ~f:(fun (a, b) -> S.Term_sub (a, b)))"
                    term_subs'
                in
                let formula_sub_soln =
                  Printf.sprintf
                    "(List.map (%s) ~f:(fun (a, b) -> S.Formula_sub (a, b)))"
                    formula_subs'
                in
                let candidates_soln =
                  Printf.sprintf
                    "(List.map (%s) ~f:(fun a -> S.Candidate a))"
                    candidates'
                in
                let proven_soln =
                  Printf.sprintf
                    "(List.map (%s) ~f:(fun a -> S.Proven a))"
                    proven'
                in
                let set =
                  Printf.sprintf
                    "(U.Solution_set.of_list (%s @ %s @ %s @ %s))"
                   term_sub_soln formula_sub_soln candidates_soln proven_soln
                in                   
                let e' =
                  Printf.sprintf
                    {|
                     (List.fold_right (Set.to_list (U.run ~normalize:%s %s lan))
                     ~init:([], []) ~f:(fun s (c, p) ->
                     match s with
                     | S.Candidate f -> (f :: c, p)
                     | S.Proven f -> (c, f :: p)
                     | _ -> (c, p)))
                     |} (Bool.to_string normalize) set
                in
                (e', Type.(Tuple [List Formula; List Formula]), ctx)
             | _ ->
                incompat "Unify (proven)" [proven_typ] [proven_typ_exp]
             end             
          | _ ->
             incompat "Unify (candidates)"
               [candidates_typ] [candidates_typ_exp]
          end
       | _ ->
          incompat "Unify (formula_subs)"
            [formula_subs_typ] [formula_subs_typ_exp]
          end
     | _ ->
        incompat "Unify (term_subs)" [term_subs_typ] [term_subs_typ_exp]
     end     
  | Exp.Var v -> (v, typeof_var ctx v, ctx)
  | Exp.Str s -> (Printf.sprintf "\"%s\"" s, Type.String, ctx)
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
  | Exp.Let {recursive; names; args; ret; exp; body} ->
     (* don't allow users to bind special
      * names used internally by the compiler *)
     List.iter names ~f:reserved_name;
     List.iter args ~f:(fun (v, _) -> reserved_name v);
     (* don't allow duplicate names in the args *)
     let type_env_exp = match String.Map.of_alist args with
       | `Ok m -> m
       | `Duplicate_key a -> 
          failwith
            (Printf.sprintf "Let: duplicate arg %s" a)
     in
     (* bind the name in the expression if it's recursive *)
     let type_env_exp =
       if not (recursive) then type_env_exp else
         match ret with
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
       in {ctx with type_env}
     in
     let (exp', exp_typ, _) = compile ctx_exp exp in
     let ctx_body = match ret with
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
          else if not (List.is_empty args) then
            let typs = List.map args ~f:snd in
            bind_var ctx (List.hd_exn names) (Type.Arrow (typs @ [exp_typ]))
          else bind_var ctx (List.hd_exn names) exp_typ
       | Some typ ->
          match Type_unify.run [exp_typ; typ] with
          | None -> incompat "Let" [exp_typ] [typ]
          | Some _ ->
             let typs = List.map args ~f:snd in
             bind_var ctx (List.hd_exn names) (Type.Arrow (typs @ [typ]))
     in
     let let_str = if recursive then "let rec" else "let" in
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
        let typs'' = List.take typs' (len - 1) in
        let init_state = List.zip_exn typs'' typs in
        begin match Type_unify.run [] ~init_state with
        | None -> incompat "Apply (args)" typs typs''
        | Some _ ->
           let e' =
             Printf.sprintf "(%s %s)" e'
               (String.concat es' ~sep:" ")
           in (e', List.last_exn typs', ctx)
        end
     | _ -> incompat "Apply (function)" [typ] []
     end
  | Exp.Ite (b, e1, e2) ->
     let (b', b_typ, _) = compile ctx b in
     begin match b_typ with
     | Type.Bool ->
        let (e1', typ1, _) = compile ctx e1 in
        let (e2', typ2, _) = compile ctx e2 in
        begin match Type_unify.run [typ1; typ2] with
        | None -> incompat "Ite" [typ1; typ2] []
        | Some typ ->
           let e' = Printf.sprintf "if %s then %s else %s" b' e1' e2' in
           (e', typ, ctx)
        end
     | _ -> incompat "Ite" [b_typ] [Type.Bool]
     end
  | Exp.Seq (e1, e2) ->
     let (e1', typ1, ctx1) = compile ctx e1 in
     let (e2', typ2, ctx2) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Lan, Type.Lan) ->
        let e' =
          Printf.sprintf
            {|
             let lan = %s in
             lan_vars :=
             List.map (Map.data lan.rules) ~f:R.vars
             |> List.concat
             |> L.Term_set.of_list;
             %s
             |}
            e1' e2'
        in (e', Type.Lan, ctx2)
     | _ -> incompat "Seq" [typ1; typ2] Type.[Lan; Lan]
     end
  | Exp.Select {keep; field; pattern; body} ->
     let (field', field_typ, _) = compile ctx field in
     begin match field_typ with
     | Type.List typ' ->
        let (pat', pat_typ, pat_ctx) = compile_pattern ctx typ' pattern in
        let matching_concl = match (typ', pat_typ) with
          | (Type.Rule, Type.Formula) -> true
          | _ -> false
        in          
        if matching_concl || Type.equal typ' pat_typ then
          let pat_ctx = bind_var pat_ctx "self" typ' in
          let (body', body_typ, body_ctx) = compile pat_ctx body in
          let (body', body_typ) = match body_typ with
            | Type.Option typ -> (body', typ)
            | typ -> (Printf.sprintf "Some (%s)" body', typ)
          in
          if keep && not (Type.equal typ' body_typ) then
            incompat "Select (body)" [body_typ] [typ']
          else
            let p' =
              let keep_var = if matching_concl then "self" else "x" in
              let keep_str =
                if keep
                then Printf.sprintf "Some (%s)" keep_var
                else "None"
              in
              let match_str =
                if matching_concl
                then "R.(self.conclusion)"
                else "self"
              in
              Printf.sprintf
                {|
                 (List.filter_map %s ~f:(fun self ->
                 match %s with
                 | %s -> %s
                 | x -> %s))
                 |} field' match_str pat' body' keep_str
            in (p', Type.(List body_typ), ctx)
        else incompat "Select (pattern)" [pat_typ] [typ']
     | _ -> incompat "Select (field)" [field_typ] []
     end
  | Exp.Match {exp; cases} ->
     let (exp', exp_typ, _) = compile ctx exp in
     let (ps', es', typs) =
       List.map cases ~f:(fun (p, e) ->
           let (p', _, pat_ctx) = compile_pattern ctx exp_typ p in
           let (e', typ, _) = compile pat_ctx e in
           (p', e', typ))
       |> List.unzip3
     in
     begin match Type_unify.run typs with
     | None -> incompat "Match" typs []
     | Some typ ->
        let cases_str =
          List.map (List.zip_exn ps' es') ~f:(fun (p', e') ->
              Printf.sprintf "(%s) -> (%s)" p' e')
          |> String.concat ~sep:" | "
        in
        let e' = Printf.sprintf "(match %s with %s)" exp' cases_str in
        (e', typ, ctx)
     end
  | Exp.Tuple es ->
     let (es', typs, _) = List.map es ~f:(compile ctx) |> List.unzip3 in
     let e' = Printf.sprintf "(%s)" (String.concat es' ~sep:", ") in
     (e', Type.Tuple typs, ctx)
  | Exp.List es ->
     let (es', typs, _) = List.map es ~f:(compile ctx) |> List.unzip3 in
     let typ = match List.hd typs with
       | None -> fresh_type_var ctx
       | Some typ -> typ
     in
     if List.for_all typs ~f:(Type.equal typ) then
       let e' = Printf.sprintf "[%s]" (String.concat es' ~sep:"; ") in
       (e', Type.(List typ), ctx)
     else incompat "List" typs []
  | Exp.Cons (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match typ2 with
     | Type.(List typ')
          when Option.is_some (Type_unify.run [typ1; typ']) ->
        let e' = Printf.sprintf "((%s) :: (%s))" e1' e2' in
        (e', Type.(List typ1), ctx)
     | _ -> incompat "Cons" [typ1; typ2] []
     end
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
     | _ -> incompat "Concat" [typ] []
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
     | (Type.List typ1', Type.List typ2') ->
        begin match Type_unify.run [typ1'; typ2'] with
        | None -> incompat "Append" [typ1; typ2] []
        | Some typ' ->
           let e' = Printf.sprintf "(List.append %s %s)" e1' e2' in
           (e', Type.List typ', ctx)
        end
     | _ -> incompat "Append" [typ1; typ2] []
     end
  | Exp.Diff (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.List typ1', Type.List typ2') ->
        begin match Type_unify.run [typ1'; typ2'] with
        | None -> incompat "Diff" [typ1; typ2] []
        | Some typ' ->
           let eq = type_equal "Diff" typ1' in
           let e' =
             Printf.sprintf "(Aux.diff_list_stable %s %s ~equal:%s)"
               e1' e2' eq
           in (e', Type.List typ', ctx)
        end
     | _ -> incompat "Diff" [typ1; typ2] []
     end
  | Exp.Intersect (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.List typ1', Type.List typ2') ->
        begin match Type_unify.run [typ1'; typ2'] with
        | None -> incompat "Intersect" [typ1; typ2] []
        | Some typ' ->
           let eq = type_equal "Intersect" typ1' in
           let e' =
             Printf.sprintf "(Aux.intersect_list_stable %s %s ~equal:%s)"
               e1' e2' eq
           in (e', Type.List typ', ctx)
        end
     | _ -> incompat "Intersect" [typ1; typ2] []
     end
  | Exp.Zip (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.List typ1', Type.List typ2') ->
        let e' = Printf.sprintf "(List.zip_exn %s %s)" e1' e2' in
        (e', Type.(List (Tuple [typ1'; typ2'])), ctx)
     | _ -> incompat "Zip" [typ1; typ2] []
     end
  | Exp.Assoc (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match typ2 with
     | Type.(List (Tuple [typ1'; typ2']))
          when Type.equal typ1 typ1' ->
        let eq = type_equal "Assoc" typ1 in
        let e' =
          Printf.sprintf "(List.Assoc.find %s %s ~equal:%s)"
            e2' e1' eq
        in (e', Type.Option typ2', ctx)
     | _ -> incompat "Assoc" [typ1; typ2] []
     end
  | Exp.Interleave_pairs e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List typ' ->
        let e' = Printf.sprintf "(Aux.interleave_pairs_of_list (%s))" e' in
        (e', Type.(List (Tuple [typ'; typ'])), ctx)
     | _ -> incompat "Interleave_pairs" [typ] []
     end
  | Exp.Length e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.List typ' ->
        let e' = Printf.sprintf "(List.length (%s))" e' in
        (e', Type.Int, ctx)
     | _ -> incompat "Length" [typ] []
     end
  | Exp.Nothing ->
     let typ = fresh_type_var ctx in
     ("None", Type.Option typ, ctx)
  | Exp.Something e ->
     let (e', typ, _) = compile ctx e in
     let e' = Printf.sprintf "(Some (%s))" e' in
     (e', Type.Option typ, ctx)
  | Exp.Option_get e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Option typ' ->
        let e' = Printf.sprintf "(Option.value_exn %s)" e' in
        (e', typ', ctx)
     | _ -> incompat "Option_get" [typ] []
     end
  | Exp.New_term t -> compile_term ctx t
  | Exp.Vars_of e ->
     let (e', typ, _) = compile ctx e in
     let e' = match typ with
       | Type.Term -> Printf.sprintf "(T.vars %s)" e'
       | Type.Formula -> Printf.sprintf "(F.vars %s)" e'
       | Type.Rule -> Printf.sprintf "(R.vars %s)" e'
       | _ -> incompat "Vars_of" [typ] []
     in (e', Type.(List Term), ctx)
  | Exp.Fresh_var v ->
     let e' = Printf.sprintf "(lan_fresh_var \"%s\")" v in
     (e', Type.Term, ctx)
  | Exp.Unbind e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.unbind %s)" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Unbind" [typ] [Type.Term]
     end
  | Exp.Bound_of e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' =
          Printf.sprintf
            {|
             begin match %s with
             | T.(Binding {var; body}) -> var
             | _ -> failwith "Bound_of: expected binding"
             end
             |} e'
        in (e', Type.String, ctx)
     | _ -> incompat "Bound_of" [typ] [Type.Term]
     end
  | Exp.Substitute (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     let e' = match typ2 with
       | Type.(List (Tuple [Term; Term])) ->
          begin match typ1 with
          | Type.Term ->
             Printf.sprintf "(T.substitute %s %s)" e1' e2'
          | Type.Formula ->
             Printf.sprintf "(F.substitute %s %s)" e1' e2'
          | Type.Rule ->
             Printf.sprintf "(R.substitute %s %s)" e1' e2'
          | _ -> incompat "Substitute" [typ1] []
          end
       | _ -> incompat "Substitute" [typ2] [Type.(List (Tuple [Term; Term]))]
     in (e', typ1, ctx)
  | Exp.Var_overlap (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let e' = Printf.sprintf "(T.var_overlap %s %s)" e1' e2' in
        (e', Type.(List Term), ctx)
     | _ -> incompat "Var_overlap" [typ1; typ2] []
     end
  | Exp.Ticked e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.ticked %s)" e' in
        (e', typ, ctx)
     | Type.(List Term) ->
        let e' = Printf.sprintf "(List.map %s ~f:T.ticked)" e' in
        (e', typ, ctx)
     | _ -> incompat "Ticked" [typ] [Type.Term]
     end
  | Exp.Ticked_restricted (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.(List Term)) ->
        let e' =
          Printf.sprintf "(T.ticked_restricted %s %s)"
            e1' e2'
        in (e', typ1, ctx)
     | _ ->
        incompat "Ticked_restricted"
          [typ1; typ2] [Type.Term; Type.(List Term)]
     end
  | Exp.New_syntax {extend; name; meta_var; terms} ->
     let (terms', term_typs, _) =
       List.map terms ~f:(compile ctx)
       |> List.unzip3
     in
     if List.for_all term_typs ~f:(Type.(equal Term)) then
       let terms' =
         Printf.sprintf "(L.Term_set.of_list [%s])"
           (String.concat terms' ~sep:"; ")
       in
       let new_cat =
         Printf.sprintf
           {|
            (C.{name = "%s"; meta_var = "%s"; terms = %s}
            |> C.deuniquify_terms)
            |}
           name meta_var terms'
       in
       let e' =
         if extend then
           Printf.sprintf
             {|
              {lan with grammar =
              (match Map.find lan.grammar "%s" with
              | None ->
              Map.set lan.grammar "%s" %s
              | Some c ->
              let terms = L.Term_set.union C.(c.terms) %s in
              let c = C.{c with meta_var = "%s"; terms} |> C.deuniquify_terms in
              Map.set lan.grammar "%s" c)}
              |} name name new_cat terms' meta_var name
         else
           Printf.sprintf
             "{lan with grammar = (Map.set lan.grammar \"%s\" %s)}"
             name new_cat
       in (e', Type.Lan, ctx)
     else incompat "New_syntax" term_typs []
  | Exp.Set_syntax_terms {name; terms} ->
     let (e', typ, _) = compile ctx terms in
     begin match Type_unify.run Type.[List Term; typ] with
     | Some Type.(List Term) ->
        let e' =
          Printf.sprintf
            {|
             {lan with grammar =
             (match Map.find lan.grammar "%s" with
             | None -> failwith "Set_syntax_terms: grammar %s doesn't exist"
             | Some c ->
             let terms = match %s with
             | [] -> failwith "Set_syntax_terms: list cannot be empty"
             | terms -> L.Term_set.of_list terms
             in
             let c = {c with terms} |> C.deuniquify_terms in
             Map.set lan.grammar "%s" c)}
             |} name name e' name
        in (e', Type.Lan, ctx)
     | _ -> incompat "Set_syntax_terms" [typ] Type.[List Term]
     end
  | Exp.Remove_syntax s ->
     let e' =
       Printf.sprintf
         {|
          {lan with grammar =
          Map.remove lan.grammar "%s"}
          |} s
     in (e', Type.Lan, ctx)
  | Exp.Meta_var_of s ->
     let e' =
       Printf.sprintf
         {|
          ((fun (c: C.t) ->  c.meta_var)
          (Map.find_exn lan.grammar "%s"))
          |} s
     in (e', Type.String, ctx)
  | Exp.Syntax_terms_of s ->
     let e' =
       Printf.sprintf
         {|
          ((fun (c: C.t) ->
          c.terms |> Set.to_list |> List.map ~f:(T.uniquify ~underscore:false))
          (Map.find_exn lan.grammar "%s"))
          |} s
     in (e', Type.(List Term), ctx)
  | Exp.New_relation (name, e) ->
     let (e', typ, _) = compile ctx e in
     begin match Type_unify.run Type.[List Term; typ] with
     | Some Type.(List Term) ->
        let e' =
          Printf.sprintf
            "{lan with relations = Map.set lan.relations \"%s\" %s}"
            name e'
        in (e', Type.Lan, ctx)
     | _ -> incompat "New_relation" [typ] Type.[List Term]
     end
  | Exp.Relations_of ->
     let e' = Printf.sprintf "(Map.to_alist lan.relations)" in
     (e', Type.(List (Tuple [String; List Term])), ctx)
  | Exp.Set_relations e ->
     let (e', typ, _) = compile ctx e in
     let typ' = Type.(List (Tuple [String; List Term])) in
     begin match Type_unify.run Type.[typ'; typ] with
     | Some Type.(List (Tuple [String; List Term])) ->
        let e' =
          Printf.sprintf
            "{lan with relations = String.Map.of_alist_exn (%s)}" e'
        in (e', Type.Lan, ctx)           
     | _ -> incompat "Set_relations" [typ] [typ']
     end
  | Exp.Remove_relation name ->
     let e' =
       Printf.sprintf
         "{lan with relations = Map.remove lan.relations \"%s\"}"
         name
     in (e', Type.Lan, ctx)
  | Exp.New_formula f -> compile_formula ctx f
  | Exp.Uniquify_formulae {formulae; hint_map; hint_var} ->
     let (formulae', formulae_typ, _) = compile ctx formulae in
     let (hint_map', hint_map_typ, _) = compile ctx hint_map in
     begin match (formulae_typ, hint_map_typ) with
     | (Type.(List Formula), Type.(List (Tuple [String; List String]))) ->
        let e' =
          Printf.sprintf
            "(L.uniquify_formulae %s ~hint_map:%s ~hint_var:\"%s\")"
            formulae' hint_map' hint_var
        in
        let typ' =
          Type.(
            Tuple
              [List Formula;
               List (Tuple [Term; List Term])])
        in (e', typ', ctx)
     | _ ->
        incompat "Uniquify_formulae"
          [formulae_typ; hint_map_typ]
          Type.[List Formula; List (Tuple [String; List String])]
     end
  | Exp.New_rule {name; premises; conclusion} ->
     let (name', name_typ, _) = compile ctx name in
     let (premises', premise_typs, _) =
       List.map premises ~f:(compile ctx)
       |> List.unzip3
     in
     let (conclusion', conclusion_typ, _) = compile ctx conclusion in
     let check_prems = function
       | Type.Formula
         | Type.(List Formula)
         | Type.(List (Var _)) (* fixme: this is a hack *)
         | Type.(Option Formula) -> true
       | _ -> false
     in
     if List.for_all premise_typs ~f:check_prems then
       match name_typ with
       | Type.String ->
          begin match conclusion_typ with
          | Type.Formula ->
             let premises' = match premises with
               | [] -> "[]"
               | _ -> 
                  List.zip_exn premises' premise_typs
                  |> List.map ~f:(fun (p, typ) ->
                         match typ with
                         | Type.Formula ->
                            Printf.sprintf "[%s]" p
                         | Type.(List Formula)
                           | Type.(List (Var _)) -> p
                         | Type.(Option Formula) ->
                            Printf.sprintf
                              "(List.filter_map [%s] ~f:(fun x -> x))" p
                         | _ -> failwith "unreachable")
                  |> String.concat ~sep:" @ "
                  |> Printf.sprintf "(%s)"
             in
             let e' =
               Printf.sprintf
                 "(R.{name = %s; premises = %s; conclusion = %s})"
                 name' premises' conclusion'
             in (e', Type.Rule, ctx)
          | _ ->
             incompat "New_rule (conclusion)"
               [conclusion_typ] [Type.Formula]
          end
       | _ -> incompat "New_rule (name)" [name_typ] [Type.String]
     else incompat "New_rule (premises)" premise_typs []
  | Exp.Rule_name e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Rule ->
        let e' =
          Printf.sprintf
            "((fun (r: R.t) -> r.name) %s)" e'
        in (e', Type.String, ctx)
     | _ -> incompat "Rule_name" [typ] [Type.Rule]
     end
  | Exp.Rule_premises e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Rule ->
        let e' =
          Printf.sprintf
            "((fun (r: R.t) -> r.premises) %s)" e'
        in (e', Type.(List Formula), ctx)
     | _ -> incompat "Rule_premises" [typ] [Type.Rule]
     end
  | Exp.Rule_conclusion e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Rule ->
        let e' =
          Printf.sprintf
            "((fun (r: R.t) -> r.conclusion) %s)" e'
        in (e', Type.Formula, ctx)
     | _ -> incompat "Rule_conclusion" [typ] [Type.Rule]
     end
  | Exp.Rules_of -> ("(Map.data lan.rules)", Type.(List Rule), ctx)
  | Exp.Add_rule e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Rule ->  
        let e' =
          Printf.sprintf
            {|
             {lan with rules =
             let (r: R.t) = %s in
             Map.add_exn lan.rules r.name r}
             |} e'
        in (e', Type.Lan, ctx)
     | _ -> incompat "Add_rule" [typ] [Type.Rule]
     end
  | Exp.Add_rules e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.(List Rule) ->  
        let e' =
          Printf.sprintf
            {|
             {lan with rules =
             (List.fold (%s) ~init:lan.rules ~f:(fun m (r: R.t) ->
             Map.add_exn m r.name r))}
             |} e'
        in (e', Type.Lan, ctx)
     | _ -> incompat "Add_rule" [typ] [Type.Rule]
     end
  | Exp.Set_rules e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.(List Rule) ->
        let e' =
          Printf.sprintf
            {|
             {lan with rules =
             String.Map.of_alist_exn
             (List.map %s ~f:(fun (r: R.t) -> (r.name, r)))}
             |} e'
        in (e', Type.Lan, ctx)
     | _ -> incompat "Set_rules" [typ] [Type.(List Rule)]
     end
  | Exp.New_hint {extend; name; elements} ->
     let elements' =
       List.map elements ~f:(fun (k, v) ->
           Printf.sprintf "(\"%s\", [%s])" k
             (List.map v ~f:(fun v ->
                  Printf.sprintf "\"%s\"" v)
              |> String.concat ~sep:"; "))
       |> String.concat ~sep:"; "
       |> Printf.sprintf "[%s]"
     in
     let new_hint =
       Printf.sprintf
         {|
          H.{
          name = "%s";
          elements =
          List.fold %s ~init:String.Map.empty ~f:(fun m (k, v) ->
          Map.set m k v)}
          |} name elements'
     in
     let e' =
       if extend then
         Printf.sprintf
           {|
            {lan with hints =
            (match Map.find lan.hints "%s" with
            | None -> Map.set lan.hints "%s" %s
            | Some h ->
            let elements =
            List.fold %s ~init:h.elements ~f:(fun m (k, v) ->
            Map.set m k v)
            in
            let h = H.{h with elements} in
            Map.set lan.hints "%s" h)}
            |} name name new_hint elements' name
       else Printf.sprintf "(Map.set lan.hints \"%s\" %s)" name new_hint
     in (e', Type.Lan, ctx)
  | Exp.Lookup_hint name ->
     let e' =
       Printf.sprintf
         {|
          begin match Map.find lan.hints "%s" with
          | None -> []
          | Some h -> Map.to_alist h.elements
          end
          |} name
     in (e', Type.(List (Tuple [String; List String])), ctx)
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
        let e' = Printf.sprintf "((%s) && (%s))" e1' e2' in
        (e', Type.Bool, ctx)
     | _ -> incompat "And" [typ1; typ2] Type.[Bool; Bool]
     end
  | Exp.Or (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Bool, Type.Bool) ->
        let e' = Printf.sprintf "((%s) || (%s))" e1' e2' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Or" [typ1; typ2] Type.[Bool; Bool]
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
        let e' = Printf.sprintf "(T.is_var %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_var" [typ] [Type.Term]
     end
  | Exp.Is_const_var e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' =
          Printf.sprintf
            "(match %s with T.Var v -> L.is_const_var lan v | _ -> false)" e'
        in (e', Type.Bool, ctx)
     | _ -> incompat "Is_const_var" [typ] [Type.Term]
     end
  | Exp.Is_str e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.is_str %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_str" [typ] [Type.Term]
     end
  | Exp.Is_constructor e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.is_constructor %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_constructor" [typ] [Type.Term]
     end
  | Exp.Is_binding e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.is_binding %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_binding" [typ] [Type.Term]
     end
  | Exp.Is_subst e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.is_subst %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_subst" [typ] [Type.Term]
     end
  | Exp.Is_list e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.is_list %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_list" [typ] [Type.Term]
     end
  | Exp.Is_map e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.is_map %s)" e' in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_map" [typ] [Type.Term]
     end
  | Exp.Is_tuple e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.is_tuple %s)" e' in
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
             | T.Var v -> L.is_var_kind lan v "%s"
             | _ -> failwith "Is_var_kind: expected var"
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
        let e' = Printf.sprintf "(L.is_op_kind lan %s \"%s\")" e' k in
        (e', Type.Bool, ctx)
     | _ -> incompat "Is_var_kind" [typ] [Type.String]
     end
  | Exp.Has_syntax s ->
     let e' = Printf.sprintf "(Map.mem lan.grammar \"%s\")" s in
     (e', Type.Bool, ctx)
  | Exp.Starts_with (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.String, Type.String) ->
        let e' =
          Printf.sprintf
            "(String.is_prefix (%s) ~prefix:(%s))" e1' e2'
        in (e', Type.Bool, ctx)
     | _ -> incompat "Starts_with" [typ1; typ2] Type.[String; String]
     end
  | Exp.Ends_with (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.String, Type.String) ->
        let e' =
          Printf.sprintf
            "(String.is_suffix (%s) ~suffix:(%s))" e1' e2'
        in (e', Type.Bool, ctx)
     | _ -> incompat "Ends_with" [typ1; typ2] Type.[String; String]
     end
and compile_term ctx t = match t with
  | Exp.Term_nil -> ("T.Nil", Type.Term, ctx)
  | Exp.Term_var v ->     
     let e' = Printf.sprintf "(T.Var \"%s\")" v in
     (e', Type.Term, ctx)
  | Exp.Term_var_exp e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.String ->
        let e' = Printf.sprintf "(T.Var (%s))" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_var_exp" [typ] [Type.String]
     end
  | Exp.Term_str s ->
     let e' = Printf.sprintf "(T.Str \"%s\")" s in
     (e', Type.Term, ctx)
  | Exp.Term_constructor (name, args) ->
     let (name', name_typ, _) = compile ctx name in
     let (args', args_typ, _) = compile ctx args in
     begin match Type_unify.run Type.[List Term; args_typ] with
     | Some Type.(List Term) ->
        begin match name_typ with
        | Type.String ->
           let e' =
             Printf.sprintf
               "(T.(Constructor {name = %s; args = %s}))"
               name' args'
           in (e', Type.Term, ctx)
        | _ -> incompat "Term_constructor (name)" [name_typ] Type.[String]
        end
     | _ -> incompat "Term_constructor (args)" [args_typ] Type.[List Term]
     end
  | Exp.Term_binding (var, body) ->
     let (var', var_typ, _) = compile ctx var in
     let (body', body_typ, _) = compile ctx body in
     begin match (var_typ, body_typ) with
     | (Type.String, Type.Term) ->
        let e' =
          Printf.sprintf
            "(T.(Binding {var = %s; body = %s}))"
            var' body'
        in (e', Type.Term, ctx)
     | _ ->
        incompat "Term_binding"
          [var_typ; body_typ] [Type.String; Type.Term]
     end
  | Exp.Term_subst (e, substs) ->
     let (e', typ, _) = compile ctx e in
     let substs' = List.map substs ~f:(compile_subst ctx) in
     begin match typ with
     | Type.Term ->
        let e' =
          Printf.sprintf
            "(T.(Subst {body = %s; substs = %s}))" e'
            (Printf.sprintf "[%s]"
               (String.concat substs' ~sep:"; "))
        in (e', Type.Term, ctx)
     | _ -> incompat "Term_subst" [typ] [Type.Term]
     end
  | Exp.Term_map_update (key, value, map) ->
     let (key', key_typ, _) = compile ctx key in
     let (value', value_typ, _) = compile ctx value in
     let (map', map_typ, _) = compile ctx map in
     begin match (key_typ, value_typ, map_typ) with
     | (Type.Term, Type.Term, Type.Term) ->
        let e' =
          Printf.sprintf
            "(T.(Map_update {key = %s; value = %s; map = %s}))"
            key' value' map'
        in (e', Type.Term, ctx)
     | _ ->
        incompat "Term_map_update"
          [key_typ; value_typ; map_typ]
          [Type.Term; Type.Term; Type.Term]
     end
  | Exp.Term_map_domain e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.Map_domain %s)" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_map_domain" [typ] [Type.Term]
     end
  | Exp.Term_map_range e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.Map_range %s)" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_map_range" [typ] [Type.Term]
     end
  | Exp.Term_cons (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let e' = Printf.sprintf "(T.Cons (%s, %s))" e1' e2' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_cons" [typ1; typ2] [Type.Term; Type.Term]
     end
  | Exp.Term_list e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.List %s)" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_list" [typ] [Type.Term]
     end
  | Exp.Term_map (key, e) ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' =
          Printf.sprintf
            "(T.(Map {key = \"%s\"; value = %s}))"
            key e'
        in (e', Type.Term, ctx)
     | _ -> incompat "Term_map" [typ] [Type.Term]
     end
  | Exp.Term_tuple e ->
     let (e', typ, _) = compile ctx e in
     begin match Type_unify.run Type.[List Term; typ] with
     | Some (Type.(List Term)) ->
        let e' = Printf.sprintf "(T.Tuple (%s))" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_tuple" [typ] Type.[List Term]
     end
  | Exp.Term_union e ->
     let (e', typ, _) = compile ctx e in
     begin match Type_unify.run Type.[List Term; typ] with
     | Some (Type.(List Term)) ->
        let e' = Printf.sprintf "(T.Union (%s))" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_union" [typ] Type.[List Term]
     end
  | Exp.Term_map_union e ->
     let (e', typ, _) = compile ctx e in
     begin match Type_unify.run Type.[List Term; typ] with
     | Some (Type.(List Term)) ->
        let e' = Printf.sprintf "(T.Map_union (%s))" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_map_union" [typ] Type.[List Term]
     end
  | Exp.Term_zip (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let e' = Printf.sprintf "(T.Zip (%s, %s))" e1' e2' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_zip" [typ1; typ2] [Type.Term; Type.Term]
     end
  | Exp.Term_fresh e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        let e' = Printf.sprintf "(T.Fresh %s)" e' in
        (e', Type.Term, ctx)
     | _ -> incompat "Term_fresh" [typ] [Type.Term]
     end
and compile_subst ctx subst = match subst with
  | Exp.Subst_pair (e, var) ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Term ->
        Printf.sprintf
          "(T.Subst_pair (%s, %s))"
          e' var
     | _ -> incompat "Subst_pair" [typ] [Type.Term]
     end
  | Exp.Subst_var (v, kind) ->
     Printf.sprintf
       "(T.Subst_var (%s, %s))"
       v kind
and compile_formula ctx f = match f with
  | Exp.Formula_not e ->
     let (e', typ, _) = compile ctx e in
     begin match typ with
     | Type.Formula ->
        let e' = Printf.sprintf "(F.Not %s)" e' in
        (e', Type.Formula, ctx)
     | _ -> incompat "Formula_not" [typ] [Type.Formula]
     end
  | Exp.Formula_eq (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let e' = Printf.sprintf "(F.Eq (%s, %s))" e1' e2' in
        (e', Type.Formula, ctx)
     | _ -> incompat "Formula_eq" [typ1; typ2] [Type.Term; Type.Term]
     end
  | Exp.Formula_prop (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.String, Type.(List Term)) ->
        let e' =
          Printf.sprintf
            "(F.(Prop {predicate = %s; args = %s}))"
            e1' e2'
        in (e', Type.Formula, ctx)
     | _ -> incompat "Formula_prop" [typ1; typ2] Type.[String; List Term]
     end
  | Exp.Formula_member (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let e' =
          Printf.sprintf
            "(F.(Member {element = %s; collection = %s}))"
            e1' e2'
        in (e', Type.Formula, ctx)
     | _ -> incompat "Formula_member" [typ1; typ2] [Type.Term; Type.Term]
     end
  | Exp.Formula_subset (e1, e2) ->
     let (e1', typ1, _) = compile ctx e1 in
     let (e2', typ2, _) = compile ctx e2 in
     begin match (typ1, typ2) with
     | (Type.Term, Type.Term) ->
        let e' = Printf.sprintf "(F.(Subset {sub = %s; super = %s}))" e1' e2' in
        (e', Type.Formula, ctx)
     | _ -> incompat "Formula_subset" [typ1; typ2] [Type.Term; Type.Term]
     end

let generate_caml e =
  (* we don't need to bind 'lan' or any of the
   * helpers, since users are forbidden from
   * shadowing these definitions + L-Tr doesn't 
   * provide any ability to refer to them *)
  let type_env = String.Map.empty in
  let type_vars = String.Set.empty in
  let ctx = {type_env; type_vars} in
  let (s, typ, _) = compile ctx e in
  match typ with
  | Type.Lan ->
     Printf.sprintf
       {|
        open Core_kernel
        open Lang_n_change
        
        module L = Language
        module T = L.Term
        module F = L.Formula
        module R = L.Rule
        module G = L.Grammar
        module C = G.Category
        module H = L.Hint
        module U = Unify
        module S = U.Solution
        
        let transform (lan: L.t) =
        let lan_vars =
        Map.data lan.rules
        |> List.map ~f:R.vars
        |> List.concat
        |> L.Term_set.of_list
        |> ref
        in
        let lan_fresh_var v =
        let rec aux i =
        let var = T.Var (v ^ Int.to_string i) in
        if Set.mem !lan_vars var
        then aux (succ i)
        else (lan_vars := Set.add !lan_vars var; var)
        in aux 1
        in
        let lan = %s in
        let rules = Map.map lan.rules ~f:R.normalize_vars in
        {lan with rules}
        |} s
  | _ -> incompat "Toplevel" [typ] [Type.Lan]
