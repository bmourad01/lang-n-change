open Base

module type S = sig
  type t

  val compare: t -> t -> int
  val sexp_of_t: t -> Sexp.t
end

module Make:
functor (Vertex: S)(Edge: S) ->
sig
  type t
  type vertex = Vertex.t
  type edge = Edge.t
  
  val empty: t
  val vertices: t -> vertex list
  val has_vertex: t -> vertex -> bool
  val has_edge: t -> vertex -> edge -> vertex -> bool
  val has_some_edge: t -> vertex -> vertex -> bool
  val successors: t -> vertex -> (vertex * edge list) list  
  val predecessors: t -> vertex -> (vertex * edge list) list

  val find_successor: t
                      -> vertex
                      -> f:(vertex -> edge -> bool)
                      -> (vertex * edge) option
  
  val find_predecessor: t
                        -> vertex
                        -> f:(vertex -> edge -> bool)
                        -> (vertex * edge) option
  
  val insert_vertex: t -> vertex -> t
  val insert_edge: t -> vertex -> edge -> vertex -> t
  val insert_edge_symmetric: t -> vertex -> edge -> vertex -> t
  val remove_vertex: t -> vertex -> t
  val remove_edge: t -> vertex -> edge -> vertex -> t
  val remove_edge_symmetric: t -> vertex -> edge -> vertex -> t
  val filter_preds: t -> vertex -> f:(vertex -> edge -> bool) -> t
  val filter_succs: t -> vertex -> f:(vertex -> edge -> bool) -> t
  val exists_dfs: t -> vertex -> f:(vertex -> bool) -> bool
  val exists_bfs: t -> vertex -> f:(vertex -> bool) -> bool
  val traverse_dfs_pre: t -> vertex -> vertex list
  val traverse_dfs_post: t -> vertex -> vertex list
  val traverse_bfs: t -> vertex -> vertex list
  val topological_sort: t -> vertex list option
  val is_cyclic: t -> bool

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

  val dominators_of: t -> vertex -> dominators
  val post_dominators_of: t -> vertex -> dominators
end
