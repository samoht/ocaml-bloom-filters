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
  type t = {ancestor : B.G.t , bf : v , border : v}
  (*add nl bf border g :
    -g is the graph of ancestors of a node A;
    -bf and border are the bloomfilter list and border list of B : one of the parent of A
    -nl is the list of nodes in the difference between g and the graph of the ancestors of B
    then the function outputs the bloomfilter list and border list of A
  *)
  val add : B.G.V.t list -> v -> v -> B.G.t -> (v * v)
  (*
    get_history il ancestor g bf border
    -il is a list of nodes from which we look for nodes in the difference
    -ancestor is the graph of ancestors of A if A is calling get_history
    -g is a graph of nodes we already know in the difference (the newly found nodes will be added to this node)
    -bf and border are the last bloomfilter and border from B, the node trying to merge with A 
  *)
  val get_history : B.G.V.t list -> B.G.t -> B.G.t -> D.u -> D.u -> (B.G.t * (B.G.V.t list))
  val iter_graphe_from_high : (B.G.V.t -> unit) -> B.G.t -> B.G.V.t -> unit
  val unif_graphe : B.G.t -> B.G.t -> unit
end
     
