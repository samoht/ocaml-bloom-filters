module type Setable =
sig
  type t
  val equal : t -> t -> bool
end

module Set :
  functor (A : Setable) -> Mergetools.DataStructure with type t = A.t with type u = A.t list
