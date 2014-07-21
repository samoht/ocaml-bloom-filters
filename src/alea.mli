(** The signature of the element that can be used as nodes of the Dag
    generated
*)
module HashName :
sig
  val init : unit -> unit
  val new_name : int -> string
end

module type Elem = 
sig
  type t
  (** [init n] initializes the Random element generator where [n] is a seed
  *)
  val init : int -> unit
  (** [next_item n] gives back a new element where [n] is the size of the new element
  *)
  val next_item : int -> t
end

(** StringElem is a module with signature Elem that generates strings
*)
module StringElem : Elem with type t = string

module Make :
  functor (B : Graph.Sig.I) ->
    functor (L : Elem with type t = B.V.t) ->
sig
	(** [alea n h t seed p] is the function that produces a dag
	    and the biggest element of this dag where [n] is the
	    number of nodes of the dag and [h] is the high of the dag
	    and [t] is the size of the element in the dag and [seed]
	    is the seed used to initialize the element generator and
	    [p] is the probability that a node of high i is the son of
	    a node of high (i-1)
	*)
	val alea : int -> int -> int -> int -> float -> B.t * B.V.t
      end
