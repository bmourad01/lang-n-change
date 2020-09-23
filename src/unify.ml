open Core_kernel

module L = Language
module T = L.Term
module P = L.Predicate
module F = L.Formula
module R = L.Rule
module C = L.Grammar.Category

type t = L.Formula_set.t

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

exception Incompatible_terms of T.t * T.t
exception Incompatible_formulae of F.t * F.t
exception Unprovable_formula of F.t

let unify t (lan: L.t) =
  let state =
    Set.to_list t
    |> List.map ~f:(fun f -> Solution.Candidate f)
    |> Solution_set.of_list
  in
  let rec fresh vars = function
    | T.Var v ->
      let var = T.Var (v ^ "`") in 
      if Set.mem !vars var
      then fresh vars var
      else (vars := Set.add !vars var; var)
    | _ -> failwith "unreachable"
  in
  let subsets = L.subset_categories lan in
  let is_provable = function
    | Solution.Candidate F.(Prop {predicate; args}) ->
       (* todo: reason about principal args *)
       true
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
       | (T.Constructor c1, T.Constructor c2) ->
          if String.equal c1.name c2.name
          then zip_and_loop state' incompat c1.args c2.args
          else incompat ()
       | (T.Binding b1, T.Binding b2) ->
          loop (Set.add state' (Solution.Term_sub (b1.body, b2.body)))
       | (T.Var v1, T.Var v2) when String.equal v1 v2 ->
          loop state'
       | (T.Var v1, T.Var v2)
            when not (String.equal v1 v2)
                 && L.is_const_var lan v1
                 && L.is_const_var lan v2 -> incompat ()
       | (t, ((T.Var v) as var))
            when L.is_const_var lan v
                 || not (T.is_var t) ->
          loop (Set.add state' (Solution.Term_sub (var, t)))
       | (((T.Var v) as var), t) ->
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
            let state =
              if Set.mem vars var then
                let sub = [(var, t)] in
                Solution_set.map state ~f:(function
                    | Solution.Term_sub (t1, t2) ->
                       let t1 = T.substitute t1 sub in
                       let t2 = T.substitute t2 sub in
                       Solution.Term_sub (t1, t2)
                    | (Solution.Formula_sub _) as f -> f
                    | Solution.Candidate f ->
                       Solution.Candidate (F.substitute f sub)
                    | Solution.Proven f ->
                       Solution.Proven (F.substitute f sub))
              else state'
            in loop state
          else incompat ()
       | _ -> loop state'
       end
    | _ ->
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
          match Set.find state ~f:is_provable with
          | Some ((Solution.Candidate f) as candidate) ->
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
             let formula_sub_of_rule (r: R.t) =
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
               (Solution.Formula_sub (r.conclusion, f), r.premises)
             in
             let rec prove state = function
               | [] -> raise (Unprovable_formula f)
               | (fsub, prems) :: rest ->
                  let state' =
                    let init = Set.add state fsub in
                    List.fold prems ~init ~f:(fun state f ->
                        Set.add state (Solution.Candidate f))
                  in
                  try
                    loop state'
                  with
                  | Incompatible_terms _
                    | Incompatible_formulae _ -> prove state rest
             in
             prove
               Set.(add (remove state candidate) (Solution.Proven f))
               (List.map (Map.data lan.rules) ~f:formula_sub_of_rule)
          | _ -> state
  in
  Set.to_list (loop state)
  |> List.filter_map ~f:(function
         | Solution.Proven f -> Some f
         | _ -> None)
  |> L.Formula_set.of_list
