open Core_kernel

module type S = sig
  type t

  val compare: t -> t -> int
  val sexp_of_t: t -> Sexp.t
end

module Make(Vertex: S)(Edge: S) = struct
  type vertex = Vertex.t
  type edge = Edge.t

  module V = struct
    include Vertex
    include Comparator.Make(Vertex)
  end
  
  module E = struct
    include Edge
    include Comparator.Make(Edge)
  end

  type edges = Set.M(E).t Map.M(V).t
  type m = edges Map.M(V).t
  type t = {succs: m; preds: m}

  let empty' = Map.empty (module V)
  let empty = {succs = empty'; preds = empty'}

  let vertices g = Map.keys g.succs
  let has_vertex g v = Map.mem g.succs v
  
  let has_edge g v1 e v2 = match Map.find g.succs v1 with
    | None -> false
    | Some m ->
       match Map.find m v2 with
       | Some es -> Set.mem es e
       | None -> false

  let has_some_edge g v1 v2 = match Map.find g.succs v1 with
    | None -> false
    | Some m ->
       match Map.find m v2 with
       | Some es -> not (Set.is_empty es)
       | None -> false
  
  let collect m v = match Map.find m v with
    | None -> []
    | Some m' ->
       Map.to_alist m'
       |> List.map ~f:(fun (v, es) -> (v, Set.to_list es))

  let successors g v = collect g.succs v
  let predecessors g v = collect g.preds v

  let find m v f =
    collect m v
    |> List.map ~f:(fun (v, es) -> List.map es ~f:(fun e -> (v, e)))
    |> List.concat
    |> List.find ~f:(fun (v, e) -> f v e)

  let find_successor g v ~f = find g.succs v f
  let find_predecessor g v ~f = find g.preds v f                     

  let insert_vertex' g v = match Map.add g ~key:v ~data:empty' with
    | `Ok g -> g | `Duplicate -> g
  
  let insert_vertex g v =
    let succs = insert_vertex' g.succs v in
    let preds = insert_vertex' g.preds v in
    {succs; preds}

  let make_edge e = Set.singleton (module E) e
  
  let insert_edge' m v1 e v2 =
    let m' = Map.find_exn m v1 in
    let m' = match Map.find m' v2 with
      | Some es -> Map.set m' ~key:v2 ~data:Set.(add es e)
      | None -> Map.set m' ~key:v2 ~data:(make_edge e)
    in Map.set m ~key:v1 ~data:m'

  let insert_edge g v1 e v2 =
    let g = insert_vertex g v1 in
    let g = insert_vertex g v2 in
    let succs = insert_edge' g.succs v1 e v2 in
    let preds = insert_edge' g.preds v2 e v1 in
    {succs; preds}

  let insert_edge_symmetric g v1 e v2 =  
    let g = insert_edge g v1 e v2 in
    insert_edge g v2 e v1

  let remove_vertex g v =
    let succs = Map.remove g.succs v in
    let preds = Map.remove g.preds v in
    let succs = Map.map succs ~f:(fun m -> Map.remove m v) in
    let preds = Map.map preds ~f:(fun m -> Map.remove m v) in
    {succs; preds}

  let remove_edge' m v1 e v2 = match Map.find m v1 with
    | None -> m
    | Some m' ->
       match Map.find m' v2 with
       | None -> m
       | Some es ->
          let es = Set.remove es e in
          let m' =
            if Set.is_empty es
            then Map.remove m' v2
            else Map.set m' ~key:v2 ~data:es
          in Map.set m ~key:v1 ~data:m'

  let remove_edge g v1 e v2 =
    let succs = remove_edge' g.succs v1 e v2 in
    let preds = remove_edge' g.preds v2 e v1 in
    {succs; preds}
  
  let remove_edge_symmetric g v1 e v2 =  
    let g = remove_edge g v1 e v2 in
    remove_edge g v2 e v1

  let filter' m v ~f = match Map.find m v with
    | None -> m 
    | Some m' ->
       let f' = f in
       let data =
         Map.mapi m' ~f:(fun ~key ~data ->
             Set.filter data ~f:(f' key))
       in Map.set m ~key:v ~data

  let filter_preds g v ~f =
    let preds = filter' g.preds v ~f in
    {g with preds}
  
  let filter_succs g v ~f =
    let succs = filter' g.succs v ~f in
    {g with succs}

  let exists_dfs g start ~f =
    let rec aux v s =
      if f v then (true, s) else
        let rec aux2 s = function
          | [] -> (false, s)
          | (v, _) :: vs ->
             if Set.mem s v then aux2 s vs else
               let (res, s) = aux v Set.(add s v) in
               if res then (res, s) else aux2 s vs
        in aux2 s (successors g v)
    in aux start Set.(singleton (module V) start) |> fst

  let exists_bfs g start ~f =
    let q = Queue.singleton start in
    let rec aux s = match Queue.dequeue q with
      | Some v ->
         if f v then true else
           let succs =
             List.map (successors g v) ~f:fst
             |> List.filter ~f:(fun v -> not (Set.mem s v))
           in
           let s = List.fold succs ~init:s ~f:(fun s v -> Set.add s v) in
           Queue.enqueue_all q succs; aux s
      | None -> false
    in aux Set.(singleton (module V) start)

  let traverse_dfs_pre g start =
    let rec aux v s res =
      let res = v :: res in
      List.fold (successors g v) ~init:(s, res) ~f:(fun (s, res) (v, _) ->
          if Set.mem s v then (s, res) else aux v Set.(add s v) res)
    in aux start Set.(singleton (module V) start) [] |> snd |> List.rev

  let traverse_dfs_post_aux g dir start =
    let rec aux v s res =
      let (s, res) =
        List.fold (dir g v) ~init:(s, res) ~f:(fun (s, res) (v, _) ->
            if Set.mem s v then (s, res) else aux v Set.(add s v) res)
      in (s, v :: res)
    in aux start Set.(singleton (module V) start) [] |> snd |> List.rev

  let traverse_dfs_post g start =
    traverse_dfs_post_aux g successors start

  let traverse_bfs g start =
    let q = Queue.singleton start in
    let rec aux s res = match Queue.dequeue q with
      | Some v ->
         let succs =
           List.map (successors g v) ~f:fst
           |> List.filter ~f:(fun v -> not (Set.mem s v))
         in
         let s = List.fold succs ~init:s ~f:Set.add in
         Queue.enqueue_all q succs;
         aux s ((List.rev succs) @ res)
      | None -> (s, res)
    in aux Set.(singleton (module V) start) [start] |> snd |> List.rev
  
  let topological_sort g =
    let open Option.Let_syntax in
    let rec visit v sp st res =
      if not Set.(mem sp v) then Some (sp, res)
      else if Set.mem st v then None
      else
        let st = Set.add st v in
        let rec aux sp res = function
          | [] -> Some (sp, res)
          | (v, _) :: vs ->
             let%bind (sp, res) = visit v sp st res in
             aux sp res vs
        in
        let%map (sp, res) = aux sp res (successors g v) in
        (Set.remove sp v, v :: res)
    in
    let st = Set.empty (module V) in
    let rec loop sp res = match Set.choose sp with
      | Some v ->
         let%bind (sp, res) = visit v sp st res in
         loop sp res
      | None -> Some res
    in loop Set.(of_list (module V) (vertices g)) []
  
  let is_cyclic g = Option.is_none (topological_sort g)

  type dominators =
    < dominance_frontier: vertex -> vertex list;
      dominators: vertex -> vertex list;
      immediate_dominator_of: vertex -> vertex option;
      immediately_dominated_by: vertex -> vertex list;
      is_dominating: vertex -> vertex -> bool;
      is_immediately_dominating: vertex -> vertex -> bool;
      is_in_dominance_frontier: vertex -> vertex -> bool;
      is_strictly_dominating: vertex -> vertex -> bool;
      strict_dominators: vertex -> vertex list >

  let dominators_aux g start dir dir' =
    let post = traverse_dfs_post_aux g dir' start in
    let nums = List.foldi post ~init:empty' ~f:(fun i m v -> Map.set m v i) in
    let num = Map.find nums in
    let rec intersect idom v1 v2 = match V.compare v1 v2 with
      | 0 -> Some v1
      | _ ->
         let open Option.Let_syntax in
         let%bind n1 = num v1 in
         let%bind n2 = num v2 in
         let rec aux v1 n1 v2 n2 =
           if n1 >= n2 then return (v1, n1) else
             let%bind v1' = Map.find idom v1 in
             let%bind n1' = num v1' in
             aux v1' n1' v2 n2
         in
         let%bind (v1, n1) = aux v1 n1 v2 n2 in
         let%bind (v2, _) = aux v2 n2 v1 n1 in
         intersect idom v1 v2
    in
    let rec compute_idom idom =
      let rec aux idom changed = function
        | [] -> (idom, changed)
        | v :: vs when V.compare v start = 0 -> aux idom changed vs
        | v :: vs ->
           let l = dir g v in
           if List.is_empty l then aux idom changed vs else
             let new_idom acc (v, _) = match Map.find idom v with
               | None -> acc
               | Some _ ->
                  match acc with
                  | None -> Some v
                  | Some v' -> intersect idom v v'
             in match List.fold l ~init:None ~f:new_idom with
                | None -> aux idom changed vs
                | Some v' ->
                   let (idom, changed) = match Map.find idom v with
                     | None -> (Map.set idom v v', true)
                     | Some v'' ->
                        match V.compare v' v'' with
                        | 0 -> (idom, false)
                        | _ -> (Map.set idom v v', true)
                   in aux idom changed vs
      in match aux idom false (List.rev post) with
         | (idom, true) -> compute_idom idom
         | (idom, false) -> idom
    in
    let st = Set.singleton (module V) in
    let idom = Map.singleton (module V) start start in
    let idom = compute_idom idom in
    let idom = Map.remove idom start in
    let idoms =
      List.fold post ~init:empty' ~f:(fun idoms v ->
          match Map.find idom v with
          | None -> idoms
          | Some v' ->
             match Map.find idoms v' with
             | None -> Map.set idoms v' (st v)
             | Some s -> Map.set idoms v' (Set.add s v))
    in
    let doms = 
      List.fold post ~init:empty' ~f:(fun doms v ->
          let rec aux doms runner =
            let doms = match Map.find doms v with
              | None -> Map.set doms v (st runner)
              | Some s -> Map.set doms v (Set.add s runner)
            in match Map.find idom runner with
               | None -> doms
               | Some runner' ->
                  match V.compare runner runner' with
                  | 0 -> doms
                  | _ -> aux doms runner'
          in aux doms v)
    in                    
    let df =
      List.fold post ~init:empty' ~f:(fun df v ->
          let l = dir g v in
          match List.length l with
          | n when n < 2 -> df
          | _ ->
             match Map.find idom v with
             | None -> df
             | Some v' ->
                List.fold l ~init:df ~f:(fun df (runner, _) ->
                    let rec aux df runner = match V.compare runner v' with
                      | 0 -> df
                      | _ ->
                         let df = match Map.find df runner with
                           | None -> Map.set df runner (st v)
                           | Some s -> Map.set df runner (Set.add s v)
                         in match Map.find idom runner with
                            | None -> df
                            | Some runner' -> aux df runner'
                    in aux df runner))
    in
    object (self)
      val idom = idom
      val idoms = idoms
      val doms = doms
      val df = df

      method immediate_dominator_of = Map.find idom

      method immediately_dominated_by v = match Map.find idoms v with
        | None -> []
        | Some s -> Set.to_list s

      method is_immediately_dominating v1 v2 = match Map.find idoms v1 with
        | None -> false
        | Some s -> Set.mem s v2

      method dominators v = match Map.find doms v with
        | None -> []
        | Some s -> Set.to_list s

      method is_dominating v1 v2 = match Map.find doms v2 with
        | None -> false
        | Some s -> Set.mem s v1

      method strict_dominators v = match Map.find doms v with
        | None -> []
        | Some s -> Set.(to_list (remove s v))

      method is_strictly_dominating v1 v2 = match V.compare v1 v2 with
        | 0 -> false
        | _ -> self#is_dominating v1 v2

      method dominance_frontier v = match Map.find df v with
        | None -> []
        | Some s -> Set.to_list s

      method is_in_dominance_frontier v1 v2 = match Map.find df v1 with
        | None -> false
        | Some s -> Set.mem s v2
    end

  let dominators_of g start =
    dominators_aux g start predecessors successors
  
  let post_dominators_of g start =
    dominators_aux g start successors predecessors
end
