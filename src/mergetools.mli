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
  val add : B.G.V.t list -> v -> v -> B.G.t -> (v * v)
  val get_history : B.G.V.t list -> B.G.t -> B.G.t -> D.u -> D.u -> (B.G.t * (B.G.V.t list))
end
     
