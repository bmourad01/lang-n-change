open Core_kernel

module L = Language
module T = L.Term
module P = L.Predicate
module F = L.Formula
module R = L.Rule
module C = L.Grammar.Category

module Solution = struct
  type t =
    | Term_sub of T.t * T.t
    | Formula_sub of F.t * F.t
    | Candidate of F.t
    | Proven of F.t [@@deriving equal, compare, sexp]

  let to_string = function
    | Term_sub (t1, t2) ->
       Printf.sprintf "t[%s => %s]" (T.to_string t1) (T.to_string t2)
    | Formula_sub (f1, f2) ->
       Printf.sprintf "f[%s => %s]" (F.to_string f1) (F.to_string f2)
    | Candidate f -> Printf.sprintf "?%s" (F.to_string f)
    | Proven f -> Printf.sprintf "!%s" (F.to_string f)

  let is_term_sub = function
    | Term_sub _ -> true
    | _ -> false

  let is_formula_sub = function
    | Formula_sub _ -> true
    | _ -> false

  let is_candidate = function
    | Candidate _ -> true
    | _ -> false

  let is_proven = function
    | Proven _ -> true
    | _ -> false
end

module Solution_comparable = struct
  include Solution
  include Comparable.Make(Solution)
end

module Solution_set = Set.Make(Solution_comparable)

type t = Solution_set.t

let create fs =
  Set.to_list fs
  |> List.map ~f:(fun f -> Solution.Candidate f)
  |> Solution_set.of_list

let is_valid t =
  Set.exists t ~f:(fun s ->
      Solution.is_term_sub s
      || Solution.is_formula_sub s)
  |> not

exception Incompatible_terms of T.t * T.t
exception Incompatible_formulae of F.t * F.t
exception Unprovable_formula of F.t

let run ?(normalize = false) state (lan: L.t) =
  let rec fresh vars = function
    | T.Var v ->
      let var = T.Var (v ^ "'") in 
      if Set.mem !vars var
      then fresh vars var
      else (vars := Set.add !vars var; var)
    | _ -> failwith "unreachable"
  in
  let principal = match Map.find lan.hints "principal" with
    | None -> invalid_arg "'principal' hint is required"
    | Some principal -> principal
  in
  let mode = match Map.find lan.hints "mode" with
    | None -> invalid_arg "'mode' hint is required"
    | Some mode -> mode
  in
  let subsets = L.subset_categories lan in
  let principals predicate args =
    match Map.find principal.elements predicate with
    | None -> []
    | Some desc ->
       match List.zip desc args with
       | Unequal_lengths -> []
       | Ok l ->
          List.filter_map l ~f:(fun (m, t) ->
              Option.some_if (String.equal m "yes") t)
  in
  let inputs predicate args =
    match Map.find mode.elements predicate with
    | None -> []
    | Some desc ->
       match List.zip desc args with
       | Unequal_lengths -> []
       | Ok l ->
          List.filter_map l ~f:(fun (m, t) ->
              Option.some_if (String.equal m "inp") t)
  in
  let is_provable = function
    (* only propositions can be provable
     * using the inference rule system *)
    | Solution.Candidate F.(Prop {predicate; args}) ->
       let rec matches_pattern ts =
         List.exists ts ~f:(function
             | T.Nil
               | T.Constructor _
               | T.Cons _ -> true
             | T.Tuple ts -> matches_pattern ts
             | _ -> false)
       in principals predicate args |> matches_pattern
    | _ -> false
  in
  let rec loop state =
    let zip_and_loop state incompat ts ts' =
      List.zip ts ts'
      |> (function
          | Ok subs -> subs 
          | Unequal_lengths -> incompat ())
      |> List.fold ~init:state ~f:(fun state (t1, t2) ->
             Set.add state (Solution.Term_sub (t1, t2)))
      |> loop
    in
    match Set.find state ~f:Solution.is_term_sub with
    (* apply all term substitutions before we
     * attempt to prove additional formulae *)
    | Some ((Solution.Term_sub (t1, t2)) as tsub) ->
       let incompat () = raise (Incompatible_terms (t1, t2)) in
       (* if both terms are variables then check if
        * they belong to syntactic categories which
        * are compatible with each other *)
       begin match (t1, t2) with
       | (T.Var v1, T.Var v2) ->
          begin match (L.kind_of_var lan v1, L.kind_of_var lan v2) with
          | (None, _) | (_, None) -> ()
          | (Some c1, Some c2) ->
             if String.equal c1 c2 then () else
               match (Map.find subsets c1, Map.find subsets c2) with
               | (Some c1', _) when String.equal c1' c2 -> ()
               | (_, Some c2') when String.equal c2' c1 -> ()
               | _ -> incompat ()
          end
       | _ -> ()
       end;
       (* add new substitutions and continue the loop *)
       let state' = Set.remove state tsub in
       begin match (t1, t2) with
       | (T.Map _, _)
         | (_, T.Map _)
         | (T.List _, _)
         | (_, T.List _) ->
          (* these shouldn't appear in formulae *)
          incompat () 
       | (T.Constructor c1, T.Constructor c2) ->
          if String.equal c1.name c2.name
          then zip_and_loop state' incompat c1.args c2.args
          else incompat ()
       | (T.Cons (element, lst), T.Cons (element', lst')) ->
          let ts = [element; lst] in
          let ts' = [element'; lst'] in
          zip_and_loop state' incompat ts ts'
       | (T.Tuple ts, T.Tuple ts')
         | (T.Union ts, T.Union ts')
         | (T.Map_union ts, T.Map_union ts') ->
          zip_and_loop state' incompat ts ts'
       | (T.Zip (t1, t2), T.Zip (t1', t2')) ->
          zip_and_loop state' incompat [t1; t2] [t1'; t2']
       | (T.Binding b1, T.Binding b2) ->
          loop (Set.add state' (Solution.Term_sub (b1.body, b2.body)))
       | (T.Subst s1, T.Subst s2) ->
          loop (Set.add state' (Solution.Term_sub (s1.body, s2.body)))
       | (T.Map_update u1, T.Map_update u2) ->
          let l1 = [u1.key; u1.value; u1.map] in
          let l2 = [u2.key; u2.value; u2.map] in
          zip_and_loop state' incompat l1 l2
       | (T.(Cons (Tuple [t1; t2], lst)), T.Map_update u) ->
          let l1 = [t1; t2; lst] in
          let l2 = [u.key; u.value; u.map] in
          zip_and_loop state' incompat l1 l2
       | (T.Map_update u, T.(Cons (Tuple [t1; t2], lst))) ->
          let l1 = [u.key; u.value; u.map] in
          let l2 = [t1; t2; lst] in
          zip_and_loop state' incompat l1 l2
       | (T.Var v1, T.Var v2) when String.equal v1 v2 -> loop state'
       | (T.Var v1, T.Var v2)
            when not (String.equal v1 v2)
                 && L.is_const_var lan v1
                 && L.is_const_var lan v2 -> incompat ()
       | (t, (T.Var v as var))
            when L.is_const_var lan v
                 || not (T.is_var t) ->
          loop (Set.add state' (Solution.Term_sub (var, t)))
       | ((T.Var v as var), t) ->
          let vars = T.vars t in
          if not (L.is_const_var lan v)
             && not (List.mem vars var ~equal:T.equal) then
            let vars =
              Set.to_list state'
              |> List.map ~f:(function
                     | Solution.Term_sub (t1, t2) -> T.vars t1 @ T.vars t2
                     | Solution.Formula_sub _ -> []
                     | Solution.Candidate f
                       | Solution.Proven f -> F.vars f)
              |> List.concat
              |> L.Term_set.of_list
            in
            (* if the variable appears in the set of
             * solutions, then apply the substitution
             * to the set and keep it in the set *)
            if Set.mem vars var then
              let sub = [(var, t)] in
              Solution_set.map state ~f:(function
                  | Solution.Term_sub (t1, t2) ->
                     let t1 = T.substitute t1 sub in
                     let t2 = T.substitute t2 sub in
                     Solution.Term_sub (t1, t2)
                  | Solution.Formula_sub (f1, f2) ->
                     let f1 = F.substitute f1 sub in
                     let f2 = F.substitute f2 sub in
                     Solution.Formula_sub (f1, f2)
                  | Solution.Candidate f ->
                       Solution.Candidate (F.substitute f sub)
                  | Solution.Proven f ->
                     Solution.Proven (F.substitute f sub))
              |> loop
            else loop state'
          else incompat ()
       | _ -> loop state'
       end
    | _ ->
       (* next we try to find a formula
        * substitution in the set and use
        * them to produce new term substitutions *)
       match Set.find state ~f:Solution.is_formula_sub with
       | Some ((Solution.Formula_sub (f1, f2)) as fsub) ->
          let incompat () = raise (Incompatible_formulae (f1, f2)) in
          let state = Set.remove state fsub in
          begin match (f1, f2) with
          | (F.Not f1, F.Not f2) ->
             loop (Set.add state (Solution.Formula_sub (f1, f2)))
          | (F.Eq (t1, t2), F.Eq (t1', t2')) ->
             zip_and_loop state incompat [t1; t2] [t1'; t2']
          | (F.Prop p1, F.Prop p2) when P.equal p1.predicate p2.predicate ->
             zip_and_loop state incompat p1.args p2.args
          | (F.Member m1, F.Member m2) ->
             let ts = [m1.element; m1.collection] in
             let ts' = [m2.element; m2.collection] in
             zip_and_loop state incompat ts ts'
          | (F.Subset s1, F.Subset s2) ->
             let ts = [s1.sub; s1.super] in
             let ts' = [s2.sub; s2.super] in
             zip_and_loop state incompat ts ts'
          | _ -> incompat ()
          end
       | _ ->
          (* finally, try to find a formula that
           * is provable given the set of inference rules
           * and collect new candidate formulae as well
           * as new formula substitutions *)
          match Set.find state ~f:is_provable with
          | Some ((Solution.Candidate (F.Prop p as f) as candidate)) ->
             (* collect all mentioned variables in
              * the set so we can manage conflicts *)
             let vars =
               Set.to_list state
               |> List.map ~f:(function
                      | Solution.Candidate f
                        | Solution.Proven f -> F.vars f
                      | _ -> [])
               |> List.concat
               |> List.filter ~f:(function
                      | T.Var v -> not (L.is_const_var lan v)
                      | _ -> false)
               |> L.Term_set.of_list
             in
             (* find the first rule where we can unify
              * or give up if we cannot prove the formula *)
             let rec prove = function
               | [] -> raise (Unprovable_formula f)
               | state' :: rest ->
                  try
                    loop state'
                  with
                  | Incompatible_terms _
                    | Incompatible_formulae _ -> prove rest
             in
             let state =
               Set.(add (remove state candidate) (Solution.Proven f))
             in
             (* construct candidate states for each rule *)
             List.map (Map.data lan.rules) ~f:(fun r ->
                 let vars = ref vars in
                 let make_sub = function
                   | (T.Var v) as var ->
                      if not (L.is_const_var lan v) && Set.mem !vars var
                      then [(var, fresh vars var)]
                      else []
                   | _ -> []
                 in
                 let subs = List.map (R.vars r) ~f:make_sub |> List.concat in
                 let r = R.substitute r subs in
                 let init =
                   Set.add state (Solution.Formula_sub (r.conclusion, f))
                 in
                 List.fold r.premises ~init ~f:(fun state f ->
                     Set.add state (Solution.Candidate f)))
             |> prove
          (* we've reached the fixed point,
           * so there's nothing left to prove *)
          | _ -> state
  in
  if normalize then
    (* find pairs of formula with the same predicate names
     * and equal inputs, then perform a substitution on the
     * outputs for the set of solutions (using unification).
     
     * the algorithm terminates when such pairs no 
     * longer exist within the set of solutions,
     * but if cycles for input/output variables are
     * present then the algorithm may diverge *)
    let rec loop' state =
      let rec find = function
        | [] -> None
        | f :: fs ->
           match f with
           | Solution.Candidate (F.Prop p)
             | Solution.Proven (F.Prop p) ->
              let ins = inputs p.predicate p.args in
              let rec find' = function
                | [] -> None
                | f' :: fs' ->
                   match f' with
                   | Solution.Candidate (F.Prop p')
                     | Solution.Proven (F.Prop p')
                        when P.equal p.predicate p'.predicate ->
                      let ins' = inputs p'.predicate p'.args in
                      if List.equal T.equal ins ins' then
                        Some (Solution.Formula_sub (F.Prop p', F.Prop p))
                      else find' fs'
                   | _ -> find' fs'
              in begin match find' Set.(to_list (remove state f)) with
                 | None -> find fs
                 | Some s -> Some s
                 end
           | _ -> find fs
      in match find (Set.to_list state) with
         | None -> state
         | Some s -> Set.add state s |> loop |> loop'
    in loop' state
  else loop state
