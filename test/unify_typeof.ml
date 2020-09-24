open Core_kernel
open Lang_n_change

module L = Language
module T = L.Term
module P = L.Predicate
module F = L.Formula
module R = L.Rule
module U = Unify
module S = U.Solution

let () =
  let lan = Parse_language.parse Sys.argv.(1) in
  let subsets = L.subset_categories lan in
  let rec fresh vars = function
    | T.Var v ->
      let var = T.Var (v ^ "`") in 
      if Set.mem !vars var
      then fresh vars var
      else (vars := Set.add !vars var; var)
    | _ -> failwith "unreachable"
  in
  List.iter (L.reduction_rules_of lan) ~f:(fun r ->
      let lhs = match r.conclusion with
        | F.Prop p ->
           let lhs = List.hd_exn p.args in
           begin match lhs with
           | T.Constructor _ -> lhs
           | T.(Tuple ((Constructor _ as t) :: _)) -> t
           | _ ->
              invalid_arg
                (Printf.sprintf "bad lhs of step %s"
                   (T.to_string lhs))
           end
        | _ ->
           invalid_arg
             (Printf.sprintf "bad conclusion of step %s"
                (F.to_string r.conclusion))
      in
      let rhs = match r.conclusion with
        | F.Prop p ->
           let rhs = List.last_exn p.args in
           begin match rhs with
           | T.Constructor _ -> Some rhs
           | T.(Tuple ((Constructor _ as t) :: _)) -> Some t
           | _ -> None
           end
        | _ ->
           invalid_arg
             (Printf.sprintf "bad conclusion of step %s"
                (F.to_string r.conclusion))
      in
      let typeof_for_op op =
        List.find_map (L.typing_rules_of lan) ~f:(fun r ->
            match r.conclusion with
            | F.Prop p ->
               let arg = List.nth_exn p.args 1 in
               begin match arg with
               | T.Constructor c'
                      when String.equal op c'.name ->
                  Some r.conclusion
               | _ -> None
               end                 
            | _ -> None)
      in
      let typeof_for_op_substituted c_args p_args t =
        let arg = List.nth_exn p_args 1 in
        match arg with
        | T.Constructor c' ->
           let sub = List.zip_exn c'.args c_args in
           [List.hd_exn p_args;
            t;
            List.last_exn p_args]
           |> List.map ~f:(fun t -> T.substitute t sub)
        | _ -> failwith "unreachable"
      in
      let start_typeof = match lhs with
        | T.Constructor c ->
           typeof_for_op c.name
           |> (function
               | Some (F.Prop p) ->
                  let args = typeof_for_op_substituted c.args p.args lhs in
                  F.Prop {p with args}
               | _ ->
                  invalid_arg
                    (Printf.sprintf "no typing rule found for %s"
                       (T.to_string lhs)))
        | _ -> failwith "unreachable"
      in
      let state =
        L.Formula_set.singleton start_typeof
        |> U.create
      in
      let state = U.run state lan in
      let lhs_state_vars =
        List.map (Set.to_list state) ~f:(function
            | S.Candidate f 
              | S.Proven f -> F.vars f
            | _ -> [])
        |> List.concat
        |> L.Term_set.of_list
      in
      let start_rhs =
        let vars = ref lhs_state_vars in
        let new_term ?(typ = None) t =
          if T.is_var t && Set.mem !vars t then
            fresh vars t
          else
            match typ with
            | Some (T.Constructor c1, T.Constructor c2) ->
               if not (List.equal T.equal c1.args c2.args) then
                 let sub = List.zip_exn c2.args c1.args in
                 T.substitute t sub
               else t
            | _ -> t
        in
        (* let find_formula t = match t with
         *   | T.Var _ ->
         *      List.find_map (Set.to_list state) ~f:(function
         *          | S.Candidate ((F.Prop p) as f)
         *            | S.Proven ((F.Prop p) as f) ->
         *             Option.some_if
         *               (P.(equal p.predicate Builtin.typeof)
         *                && T.equal t (List.nth_exn p.args 1)) f
         *          | _ -> None)
         *   | T.Constructor c ->
         *      begin match typeof_for_op c.name with
         *      | Some (F.Prop p) ->
         *         let args = typeof_for_op_substituted c.args p.args in
         *         Some (F.Prop {p with args})
         *      | _ -> None
         *      end
         *   | _ -> None
         * in *)
        match rhs with
        | Some ((T.Constructor c) as rhs) ->
           begin match typeof_for_op c.name with
           | Some (F.Prop p) ->
              let compare = T.compare in
              let vars_rhs =
                T.vars_dup rhs
                |> Aux.dedup_list_stable ~compare
              in
              let arg = List.nth_exn p.args 1 in
              let vars_arg =
                T.vars_dup arg
                |> Aux.dedup_list_stable ~compare
              in
              let sub = List.zip_exn vars_arg vars_rhs in
              let sub =
                List.filter sub ~f:(fun (t1, t2) ->
                    match (t1, t2) with
                    | (T.Var v1, T.Var v2) ->
                       begin match (L.kind_of_var lan v1, L.kind_of_var lan v2) with
                       | (None, _) | (_, None) -> true
                       | (Some c1, Some c2) ->
                          if String.equal c1 c2 then true else
                            match (Map.find subsets c1, Map.find subsets c2) with
                            | (Some c1', _) -> String.equal c1' c2
                            | (_, Some c2') -> String.equal c2' c1
                            | _ -> false
                       end
                    | _ -> false)
              in
              let typ =
                new_term (List.nth_exn p.args 2) 
                  ~typ:(Some (rhs, arg))
              in
              let args =
                List.map [List.hd_exn p.args; rhs; typ] ~f:(fun t ->
                    T.substitute t sub)
              in Some (F.Prop {p with args})
           | _ ->
              invalid_arg
                (Printf.sprintf "no typing rule found for %s"
                   (T.to_string rhs))
           end
        | _ -> None
      in
    let state = match start_rhs with
      | None -> state
      | Some start_rhs ->
         let state' = U.create (L.Formula_set.singleton start_rhs) in
         let state' = U.run state' lan in
         U.run (Set.union state state') lan ~normalize:true
    in
    Printf.printf "===========================================\n\n%s\n\nSOLUTION:\n\n" (R.to_string r);
    Set.iter state ~f:(fun s ->
        Printf.printf "%s\n" (Unify.Solution.to_string s));
    Printf.printf "\n\n")
