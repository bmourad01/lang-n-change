open Core_kernel

module Type = struct
  type t =
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
    | List of t [@@deriving equal]

  let rec to_string = function
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
        recursive: bool;
        name: string;
        args: (string * Type.t) list;
        exp: t;
        body: t;
      }
    | Apply of t * t list
    | Ite of boolean * t * t
    | Seq of t * t
    | Select of {
        keep: bool;
        field: t;
        pattern: t;
        body: t;
      }
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
    | Uniquify_term of t
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
    | Rule of {
        name: t;
        premises: t;
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
    | Not of boolean
    | And of boolean * boolean
    | Or of boolean * boolean
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
       Printf.sprintf "(%s ^ %s)"
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
    | Let {recursive; name; args; exp; body} ->
       let args_str = match args with
         | [] -> " "
         | _ ->
            List.map args ~f:(fun (a, t) ->
                Printf.sprintf "(%s: %s)"
                  a (Type.to_string t))
            |> String.concat ~sep:" "
       in
       let let_str = if recursive then "let rec" else "let" in
       Printf.sprintf "%s %s%s= %s in %s"
         let_str name args_str (to_string exp) (to_string body)
    | Apply (e, args) ->
       Printf.sprintf "%s(%s)" (to_string e)
         (List.map args ~f:to_string
          |> String.concat ~sep:", ")
    | Ite (b, e1, e2) ->
       Printf.sprintf "if %s then %s else %s"
         (string_of_boolean b) (to_string e1) (to_string e2)
    | Seq (e1, e2) ->
       Printf.sprintf "%s; %s"
         (to_string e1) (to_string e2)
    | Select {keep; field; pattern; body} ->
       let field_str = to_string field in
       let field_str = if keep then field_str ^ "!" else field_str in
       Printf.sprintf "%s[%s]: {%s}"
         field_str (to_string pattern) (to_string body)
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
       Printf.sprintf "append(%s, %s)"
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
    | New_term t -> "$" ^ string_of_term t
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
    | Uniquify_term e -> Printf.sprintf "uniquify(%s)" (to_string e)
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
       Printf.sprintf "uniquify(%s, \"%s\", \"%s\")"
         (to_string formulae) (to_string hint_map) hint_var
    | Rule {name; premises; conclusion} ->
       Printf.sprintf "[%s] {\n  %s\n---------------------\n  %s\n}"
         (to_string name) (to_string premises) (to_string conclusion)
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
    | Not b -> Printf.sprintf "not(%s)" (string_of_boolean b)
    | And (b1, b2) ->
       Printf.sprintf "and(%s, %s)"
         (string_of_boolean b1) (string_of_boolean b2)
    | Or (b1, b2) ->
       Printf.sprintf "or(%s, %s)"
         (string_of_boolean b1) (string_of_boolean b2)
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
    | Term_nil -> "nil"
    | Term_var v -> v
    | Term_str s -> Printf.sprintf "\"%s\"" s
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
    | Term_map_domain e -> Printf.sprintf "dom(%s)" (to_string e)
    | Term_map_range e -> Printf.sprintf "range(%s)" (to_string e)
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
       Printf.sprintf "union(%s)"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | Term_map_union es ->
       Printf.sprintf "map_union(%s)"
         (List.map es ~f:to_string
          |> String.concat ~sep:", ")
    | Term_zip (e1, e2) ->
       Printf.sprintf "zip(%s, %s)"
         (to_string e1) (to_string e2)
    | Term_fresh e -> Printf.sprintf "fresh(%s)" (to_string e)
  and string_of_formula = function
    | Formula_not e -> Printf.sprintf "$not(%s)" (to_string e)
    | Formula_eq (e1, e2) ->
       Printf.sprintf "%s = %s"
         (to_string e1) (to_string e2)
    | Formula_prop (e1, e2) ->
       Printf.sprintf "%s %s"
         (to_string e1) (to_string e2)
    | Formula_member (e1, e2) ->
       Printf.sprintf "$member %s %s"
         (to_string e1) (to_string e2)
    | Formula_subset (e1, e2) ->
       Printf.sprintf "$subset %s %s"
         (to_string e1) (to_string e2)
end
