module type DataSig =
sig
  (** type t is the type of the data we are trying to store *)
  type t
  (** type u is the type of the storage that are used *)
  type u
  val name : t -> string
  val nb_max : int
  (** [merge lu lt] is a function that computes the union of storages
      and add some new data where [lu] is the storages we want to unite
      and [lt] the data we want to add *)
  val merge : u list -> t list -> u
  (** [mem e s] tests the membership where [e] is the data and [s] is
      the storage *)
  val mem : t -> u -> bool
end
exception No_more_bf
  
module Make :
  functor (B : Graph.Sig.I) ->
    functor (D : DataSig with type t = B.V.t) ->
sig
  type v = (int * D.u) list
  (** type t is the main type, it contains the ancestor dag of the set
      of nodes it represents as well as the datastructure *)
  type t
  val empty_state : unit -> t
  val get_ancestor : t -> B.t
  val get_bf : t -> v
  (** [next_ring il ia bf bd] is the function that computes the list
      of the next interesting nodes and the ring of nodes where [il]
      is the list of previous interesting nodes and [ia] is the
      ancestors list of the interesting nodes and [bf] is the current
      bloomfilter and [bd] the current border*)
  val next_ring : B.V.t list -> B.t list -> D.u -> D.u -> (B.t * (B.V.t list))
  (** [increase_high s old_hd_l new_hd] is the function that computes
      the state of new_hd where [s] is the state corresponding to the
      union of new_hd's fathers and [old_hd_l] is the list of new_hd's
      fathers and [new_hd] is new_hd *)
  val increase_high :  t ->  B.V.t list -> B.V.t -> t
  (** [increase_width s f hd] is the function that computes the state
      of the union of nodes where [s] was the state of the first nodes and
      [f] is the callback function and [hd] is the next node to be added
      to the state *)
  val increase_width : t -> ( D.u -> D.u -> B.V.t list -> (B.V.t list * B.t)) -> B.V.t -> t * int

end
      
module Compteur :
sig
  val b1 : bool ref
  val b2 : bool ref
  val b3 : bool ref
  val l1 : (float list) ref
  val l2 : (float list) ref
  val l3 : (float list) ref
end
