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
  type v
  type t
  val empty_state : unit -> t
  (** [next_ring il ia bf bd] is the function that computes the list
      of the next interesting nodes and the ring of nodes where [il]
      is the list of previous interesting nodes and [ia] is the
      ancestors list of the interesting nodes and [bf] is the current
      bloomfilter and [bd] the current border*)
  val next_ring : B.G.V.t list -> B.G.t list -> D.u -> D.u -> (B.G.t * (B.G.V.t list))
  (** [increase_high s old_hd_l new_hd] is the function that computes
      the state of new_hd where [s] is the state corresponding to the
      union of new_hd's fathers and [old_hd_l] is the list of new_hd's
      fathers and [new_hd] is new_hd *)
  val increase_high :  t ->  B.G.V.t list -> B.G.V.t -> t
  (** [increase_width s f hd] is the function that computes the state
      of the union of nodes where [s] was the state of the first nodes and
      [f] is the callback function and [hd] is the next node to be added
      to the state *)
  val increase_width : t -> ( D.u -> D.u -> B.G.V.t list -> (B.G.V.t list * B.G.t)) -> B.G.V.t -> t

end
      
