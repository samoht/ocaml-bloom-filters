module type HashSig =
sig
  type t
  val h : string array -> t -> unit
  val size : int
  val size_hash : int
end
  
module BloomFilter :
  functor (H : HashSig) -> Mergetools.DataStructure with type t = H.t with type u = string array
