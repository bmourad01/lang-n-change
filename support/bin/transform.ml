
     open Core_kernel
     open Lang_n_change
     
     module L = Language
     module T = L.Term
     module F = L.Formula
     module R = L.Rule
     module G = L.Grammar
     module C = G.Category
     module H = L.Hint
     
     let transform (lan: L.t) =
     let lan_vars = ref (Map.data lan.rules |> List.map ~f:R.vars |> List.concat |> L.Term_set.of_list) in
     let lan_fresh_var v =
     let rec aux i =
     let var = T.Var (v ^ Int.to_string i) in
     if Set.mem !lan_vars var
     then aux (succ i)
     else (lan_vars := Set.add !lan_vars var; var)
     in aux 1
     in
     
             {lan with rules =
             String.Map.of_alist_exn
             (List.map 
               (List.filter_map (Map.data lan.rules) ~f:(fun self ->
               match R.(self.conclusion) with
               | (F.(Prop {predicate = "step"; args = [(T.(Constructor {name = op; args = args})); rhs]})) -> let exprs = 
               (List.filter_map 
          ((fun (c: C.t) ->
          c.terms |> Set.to_list |> List.map ~f:T.uniquify)
          (Map.find_exn lan.grammar "Expression"))
           ~f:(fun self ->
               match self with
               | (T.(Constructor {name = opp; args = exprs})) -> if (String.equal opp op) then Some exprs else None
               | x -> None))
                in if (List.is_empty exprs) then None else let v_res = (lan_fresh_var "v") in let exprs = (List.hd_exn exprs) in let emap = (List.zip_exn exprs args) in let new_args = 
               (List.filter_map emap ~f:(fun self ->
               match self with
               | (expr, arg) -> (Some (T.ticked expr))
               | x -> None))
                in let new_target = if (not (List.mem args rhs ~equal:T.equal)) then v_res else rhs in Some (R.{name = ((fun (r: R.t) -> r.name) self); premises = (
               (List.filter_map emap ~f:(fun self ->
               match self with
               | (expr, arg) -> if ((T.is_var arg) && (not (List.mem (T.vars rhs) arg ~equal:T.equal))) then None else Some (F.(Prop {predicate = "step"; args = [(T.ticked expr); arg]}))
               | x -> None))
                @ (List.filter_map [if (not (List.mem args rhs ~equal:T.equal)) then None else Some (F.(Prop {predicate = "step"; args = [rhs; v_res]}))] ~f:(fun x -> x)) @ ((fun (r: R.t) -> r.premises) self)); conclusion = (F.(Prop {predicate = "step"; args = [(T.(Constructor {name = op; args = new_args})); new_target]}))})
               | x -> (Some self)))
                ~f:(fun (r: R.t) -> (r.name, r)))}
             
     
