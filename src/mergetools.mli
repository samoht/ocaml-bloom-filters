module type DataStructure =
sig
  type t
  type u
  val nb_max : int
  val build_next : u list -> t -> u
  val build_next_l : u list -> t list -> u
  val build_union : u list -> u
  val test_belong : t -> u -> bool
end
  
  
module MergeTools :
  functor (B : Alea.Build) ->
    functor (D : DataStructure with type t = B.G.V.t) ->
sig
  type v = (int * D.u) list
  type t = {ancestor : B.G.t ; bf : v ; border : v}
  type retour = Some of (B.G.t) | None
  val empty_state : unit -> t
  (**[add nl sB g] is the function that outputs the global state of A where [nl] is the list of nodes in the difference between g and the graph of the ancestors of B and [sB] is the state of B and [g] is the graph of ancestors of a node A
  *)
  val add : B.G.V.t list -> t -> B.G.t -> t
  (**[get_history il sA g bf border] is a function called by A that computes a part of the difference between B and A where [il] is a list of nodes from which we look for nodes in the difference and [sA] is the global state of A and [g] is a graph of nodes we already know in the difference (the newly found nodes will be added to this node) and [bf] is a bloomfilter containing nodes of B we are trying to find in the ancestors of A and [border] is the border of the bloomfilter
  *)
  val get_history_multi : B.G.V.t list -> B.G.t list -> D.u -> D.u -> (B.G.t * (B.G.V.t list))
  val get_history : B.G.V.t list -> t -> B.G.t -> D.u -> D.u -> (B.G.t * (B.G.V.t list))
  val iter_graphe_from_high : (B.G.V.t -> unit) -> B.G.t -> B.G.V.t -> unit
  val unif_graphe : B.G.t -> B.G.t -> unit
  val increase_high :  t ->  B.G.V.t list -> B.G.V.t -> t
  val increase_width : t -> ( D.u -> D.u -> B.G.V.t list -> (B.G.V.t list * B.G.t)) -> B.G.V.t -> t

end
     
