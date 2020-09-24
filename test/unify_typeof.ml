open Core_kernel
open Lang_n_change

module L = Language
module T = L.Term
module F = L.Formula
module R = L.Rule

let () =
  let lan = Parse_language.parse Sys.argv.(1) in
  List.iter (L.reduction_rules_of lan) ~f:(fun r ->
      let lhs = match r.conclusion with
        | F.Prop p ->
           let lhs = List.hd_exn p.args in
           begin match lhs with
           | T.Constructor _ -> lhs
           | T.(Tuple (((Constructor _) as t) :: _)) -> t
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
      (* let rhs = match r.conclusion with
       *   | F.Prop p ->
       *      let rhs = List.last_exn p.args in
       *      begin match rhs with
       *      | T.Constructor _ -> rhs
       *      | T.(Tuple (((Constructor _) as t) :: _)) -> t
       *      | _ ->
       *         invalid_arg
       *           (Printf.sprintf "bad rhs of step %s"
       *              (T.to_string rhs))
       *      end
       *   | _ ->
       *      invalid_arg
       *        (Printf.sprintf "bad conclusion of step %s"
       *           (F.to_string r.conclusion))
       * in *)
      let start_typeof = match lhs with
        | T.Constructor c ->
           List.find_map (Map.data lan.rules) ~f:(fun r ->
               if R.is_typing_rule r then
                 begin match r.conclusion with
                 | F.Prop p ->
                    let arg = List.nth_exn p.args 1 in
                    begin match arg with
                    | T.Constructor c'
                         when String.equal c.name c'.name ->
                       Some r.conclusion
                    | _ -> None
                    end                 
                 | _ -> None
                 end
               else None)
           |> (function
               | Some (F.Prop p) ->
                  let arg = List.nth_exn p.args 1 in
                  begin match arg with
                  | T.Constructor c' ->
                     let sub = List.zip_exn c.args c'.args in
                     let args =
                       [List.hd_exn p.args;
                        lhs;
                        List.last_exn p.args]
                       |> List.map ~f:(fun t -> T.substitute t sub)
                     in F.Prop {p with args}
                  | _ -> failwith "unreachable"
                  end
               | _ ->
                  invalid_arg
                    (Printf.sprintf "no typing rule found for %s"
                       (T.to_string lhs)))
        | _ -> failwith "unreachable"
    in
    let state =
      L.Formula_set.singleton start_typeof
      |> Unify.create
    in
    let state = Unify.run state lan in
    Printf.printf "===========================================\n%s\n\n" (R.to_string r);
    Set.iter state ~f:(fun s ->
        Printf.printf "%s\n" (Unify.Solution.to_string s));
    Printf.printf "\n")
