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
  let mode = match Map.find lan.hints "mode" with
    | None -> invalid_arg "'mode' hint is required"
    | Some mode -> mode
  in
  let outputs predicate args =
    match Map.find mode.elements predicate with
    | None -> []
    | Some desc ->
       match List.zip desc args with
       | Unequal_lengths -> []
       | Ok l ->
          List.filter_map l ~f:(fun (m, t) ->
              Option.some_if (String.equal m "out") t)
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
           | T.Constructor _
             | T.Subst _ -> Some rhs
           | T.(Tuple ((Constructor _ as t) :: _))
             | T.(Tuple ((Subst _ as t) :: _)) -> Some t
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
           let t1 = T.substitute (List.hd_exn p_args) sub in
           let t3 = T.substitute (List.last_exn p_args) sub in
           [t1; t; t3]
        | _ -> failwith "unreachable"
      in
      let start_lhs = match lhs with
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
        L.Formula_set.singleton start_lhs
        |> U.create
      in
      let state = U.run state lan in
      let lhs_vars =
        List.map (Set.to_list state) ~f:(function
            | S.Candidate f 
              | S.Proven f -> F.vars f
            | _ -> [])
        |> List.concat
        |> L.Term_set.of_list
      in
      let lhs_vars_ref = ref lhs_vars in
      let start_rhs =
        let find_formula t = match t with
          | T.Var _ ->
             List.find_map (Set.to_list state) ~f:(function
                 | S.Candidate ((F.Prop p) as f)
                   | S.Proven ((F.Prop p) as f) ->
                    Option.some_if
                      (P.(equal p.predicate Builtin.typeof)
                       && T.equal t (List.nth_exn p.args 1)) f
                 | _ -> None)
          | T.Constructor c ->
             begin match typeof_for_op c.name with
             | Some (F.Prop p) ->
                let args = typeof_for_op_substituted c.args p.args t in
                Some (F.Prop {p with args})
             | _ -> None
             end
          | _ -> None
        in
        match rhs with
        | Some ((T.Subst s) as rhs) ->
           let open Option.Let_syntax in
           let%bind body_kind = match s.body with
             | T.Var v -> L.kind_of_var lan v
             | T.Constructor c -> L.kind_of_op lan c.name
             | _ -> None
           in           
           begin match find_formula s.body with
           | Some (F.Prop p1) ->
              let rec aux res = function
                | [] -> Some res
                | T.Subst_pair (term, var) :: rest ->
                   let%bind term_kind = match term with
                     | T.Var v -> L.kind_of_var lan v
                     | T.Constructor c -> L.kind_of_op lan c.name
                     | _ -> None
                   in
                   let%bind _ =
                     if String.equal body_kind term_kind then
                       return ()
                     else
                       match (Map.find subsets body_kind,
                              Map.find subsets term_kind) with
                       | (Some body_kind', _)
                            when String.equal body_kind' term_kind ->
                          return ()
                       | (_, Some term_kind')
                            when String.equal body_kind term_kind' ->
                          return ()
                       | _ -> None
                   in
                   begin match find_formula term with 
                   | Some (F.Prop p2) ->
                      let assume = List.hd_exn p2.args in
                      let typ = List.last_exn p2.args in
                      aux ((T.Var var, typ, assume, term) :: res) rest
                   | _ ->
                      invalid_arg
                        (Printf.sprintf "no typing rule found for %s"
                           (T.to_string term))
                   end
                (* for now we won't try to reason about
                 * substitution variables since that requires
                 * a more sophisticated analysis *)
                | T.Subst_var _ :: _ -> None
              in
              let%bind assumptions = aux [] s.substs in
              let make_assume t =
                let rec aux map = function
                  | [] -> map
                  | (key, value, _, _) :: rest ->
                     aux T.(Map_update {key; value; map}) rest
                in aux t assumptions
              in
              let assume = List.hd_exn p1.args in
              let%bind assume' = match assume with
                | T.Var _ -> return (make_assume assume)
                | T.Map_update m -> return (make_assume m.map)
                | T.(Tuple ((Var _ as t) :: _)) -> return (make_assume t)
                | T.(Tuple (Map_update m :: _)) -> return (make_assume m.map)
                | _ -> None
              in
              let fs =
                let init = [] in
                List.fold assumptions ~init ~f:(fun fs (_, typ, assume, t) ->
                    let args = [assume; t; typ] in
                    F.(Prop {p1 with args}) :: fs)
              in
              let args = [
                  assume';
                  List.nth_exn p1.args 1;
                  List.last_exn p1.args;
                ] in
              let fs = F.(Prop {p1 with args}) :: fs in
              let args = [assume; rhs; List.last_exn p1.args] in
              return (F.(Prop {p1 with args}) :: fs)
           | _ ->
              invalid_arg
                 (Printf.sprintf "no typing rule found for %s"
                    (T.to_string s.body))
           end
        | Some ((T.Constructor c) as rhs) ->
           begin match typeof_for_op c.name with
           | Some (F.Prop p) ->
              let args = typeof_for_op_substituted c.args p.args rhs in
              Some [F.Prop {p with args}]
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
         (* uniquify the outputs *)
         let sub =
           List.filter_map start_rhs ~f:(function
               | F.Prop {predicate; args} ->
                  Some (outputs predicate args)
               | _ -> None)
           |> List.concat
           |> List.map ~f:T.vars
           |> List.concat
           |> List.dedup_and_sort ~compare:T.compare
           |> List.filter_map ~f:(fun t ->
                  if Set.mem !lhs_vars_ref t
                  then Some (t, fresh lhs_vars_ref t)
                  else None)
         in
         let start_rhs =
           List.map start_rhs ~f:(fun f ->
               F.substitute f sub)
         in
         let state' = U.create (L.Formula_set.of_list start_rhs) in
         let state = Set.union state state' in
         let state = U.run state lan in
         U.run state lan ~normalize:true
    in
    Printf.printf "===========================================\n\n%s\n\nSOLUTION:\n\n" (R.to_string r);
    Set.iter state ~f:(fun s ->
        Printf.printf "%s\n" (Unify.Solution.to_string s));
    Printf.printf "\n\n")
