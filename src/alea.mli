module Comparable :
  sig
    type t = string
    val compare : t -> t -> int
    val hash : t -> int
    val equal : t -> t -> bool
  end
module ToDot :
  sig
    type t = Graph.Imperative.Digraph.ConcreteBidirectional(Comparable).t
    module V :
      sig
        type t = Comparable.t
        val compare : t -> t -> int
        val hash : t -> int
        val equal : t -> t -> bool
        type label = Comparable.t
        val create : label -> t
        val label : t -> label
      end
    type vertex = V.t
    module E :
      sig
        type t = Comparable.t * Comparable.t
        val compare : t -> t -> int
        val src : t -> vertex
        val dst : t -> vertex
        type label = unit
        val create : vertex -> label -> vertex -> t
        val label : t -> label
      end
    type edge = E.t
    val is_directed : bool
    val is_empty : t -> bool
    val nb_vertex : t -> int
    val nb_edges : t -> int
    val out_degree : t -> vertex -> int
    val in_degree : t -> vertex -> int
    val mem_vertex : t -> vertex -> bool
    val mem_edge : t -> vertex -> vertex -> bool
    val mem_edge_e : t -> edge -> bool
    val find_edge : t -> vertex -> vertex -> edge
    val find_all_edges : t -> vertex -> vertex -> edge list
    val succ : t -> vertex -> vertex list
    val pred : t -> vertex -> vertex list
    val succ_e : t -> vertex -> edge list
    val pred_e : t -> vertex -> edge list
    val iter_vertex : (vertex -> unit) -> t -> unit
    val fold_vertex : (vertex -> 'a -> 'a) -> t -> 'a -> 'a
    val iter_edges : (vertex -> vertex -> unit) -> t -> unit
    val fold_edges : (vertex -> vertex -> 'a -> 'a) -> t -> 'a -> 'a
    val iter_edges_e : (edge -> unit) -> t -> unit
    val fold_edges_e : (edge -> 'a -> 'a) -> t -> 'a -> 'a
    val map_vertex : (vertex -> vertex) -> t -> t
    val iter_succ : (vertex -> unit) -> t -> vertex -> unit
    val iter_pred : (vertex -> unit) -> t -> vertex -> unit
    val fold_succ : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val fold_pred : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val iter_succ_e : (edge -> unit) -> t -> vertex -> unit
    val fold_succ_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val iter_pred_e : (edge -> unit) -> t -> vertex -> unit
    val fold_pred_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val create : ?size:int -> unit -> t
    val clear : t -> unit
    val copy : t -> t
    val add_vertex : t -> vertex -> unit
    val remove_vertex : t -> vertex -> unit
    val add_edge : t -> vertex -> vertex -> unit
    val add_edge_e : t -> edge -> unit
    val remove_edge : t -> vertex -> vertex -> unit
    val remove_edge_e : t -> edge -> unit
    val r : int ref
    val init : unit -> unit
    val edge_attributes : 'a * 'b -> 'c list
    val default_edge_attributes : 'a -> 'b list
    val get_subgraph : 'a -> 'b option
    val vertex_attributes : 'a -> [> `Shape of [> `Box ] ] list
    val default_vertex_attributes : 'a -> 'b list
    val graph_attributes : 'a -> 'b list
  end
module MyDot :
  sig
    val fprint_graph : Format.formatter -> ToDot.t -> unit
    val output_graph : out_channel -> ToDot.t -> unit
  end
module HashName :
  sig
    val float : float -> float
    val initr : int -> unit
    val int : int -> int
    type tree = Node of bool * tree * tree | Nil of bool
    val current : tree ref
    val is_in : string -> bool
    val add_immut : string -> tree -> tree
    val add : string -> unit
    val init : unit -> unit
    val newname : int -> string
    val new_name : int -> string
  end
module MyGraph :
  sig
    type t = Graph.Imperative.Digraph.ConcreteBidirectional(Comparable).t
    module V :
      sig
        type t = Comparable.t
        val compare : t -> t -> int
        val hash : t -> int
        val equal : t -> t -> bool
        type label = Comparable.t
        val create : label -> t
        val label : t -> label
      end
    type vertex = V.t
    module E :
      sig
        type t = Comparable.t * Comparable.t
        val compare : t -> t -> int
        val src : t -> vertex
        val dst : t -> vertex
        type label = unit
        val create : vertex -> label -> vertex -> t
        val label : t -> label
      end
    type edge = E.t
    val is_directed : bool
    val is_empty : t -> bool
    val nb_vertex : t -> int
    val nb_edges : t -> int
    val out_degree : t -> vertex -> int
    val in_degree : t -> vertex -> int
    val mem_vertex : t -> vertex -> bool
    val mem_edge : t -> vertex -> vertex -> bool
    val mem_edge_e : t -> edge -> bool
    val find_edge : t -> vertex -> vertex -> edge
    val find_all_edges : t -> vertex -> vertex -> edge list
    val succ : t -> vertex -> vertex list
    val pred : t -> vertex -> vertex list
    val succ_e : t -> vertex -> edge list
    val pred_e : t -> vertex -> edge list
    val iter_vertex : (vertex -> unit) -> t -> unit
    val fold_vertex : (vertex -> 'a -> 'a) -> t -> 'a -> 'a
    val iter_edges : (vertex -> vertex -> unit) -> t -> unit
    val fold_edges : (vertex -> vertex -> 'a -> 'a) -> t -> 'a -> 'a
    val iter_edges_e : (edge -> unit) -> t -> unit
    val fold_edges_e : (edge -> 'a -> 'a) -> t -> 'a -> 'a
    val map_vertex : (vertex -> vertex) -> t -> t
    val iter_succ : (vertex -> unit) -> t -> vertex -> unit
    val iter_pred : (vertex -> unit) -> t -> vertex -> unit
    val fold_succ : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val fold_pred : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val iter_succ_e : (edge -> unit) -> t -> vertex -> unit
    val fold_succ_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val iter_pred_e : (edge -> unit) -> t -> vertex -> unit
    val fold_pred_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
    val create : ?size:int -> unit -> t
    val clear : t -> unit
    val copy : t -> t
    val add_vertex : t -> vertex -> unit
    val remove_vertex : t -> vertex -> unit
    val add_edge : t -> vertex -> vertex -> unit
    val add_edge_e : t -> edge -> unit
    val remove_edge : t -> vertex -> vertex -> unit
    val remove_edge_e : t -> edge -> unit
  end

val alea : int -> int -> int -> float -> MyGraph.t * string

val hexa_to_binaire : string -> string
val binaire_to_hexa : string -> string

module MyParsor : 
sig
  val parse : string -> MyGraph.t
  val parse_bounding_box_and_clusters : string -> MyGraph.t * string * Graph.Dot.clusters_hash
end

module type Build = 
  sig
    module G : Graph.Sig.G
    val empty : unit -> G.t
    val add_vertex : G.t -> G.V.t -> unit
    val add_edge : G.t -> G.V.t -> G.V.t -> unit
    val copy : G.t -> G.t
  end

module type Elem = 
sig
  type t
  val init : int -> unit
  val next_item : int -> t
end

module StringElem : Elem with type t = string

module Buildtest : 
sig
  module G : Graph.Sig.G with type V.t = string
  val empty : unit -> G.t
  val add_vertex : G.t -> string -> unit
  val add_edge : G.t -> string -> string -> unit
  val copy : G.t -> G.t
end

module AleaDag :
  functor (B : Build) ->
    functor (L : Elem with type t = B.G.V.t) ->
      sig
	val alea : int -> int -> int -> int -> float -> B.G.t * B.G.V.t
      end
