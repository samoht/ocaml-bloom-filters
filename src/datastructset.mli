module type SetSig =
sig
  type t
  val equal : t -> t -> bool
end

module Make :
  functor (A : Setable) -> Mergetools.DataStructure with type t = A.t with type u = A.t list
