module type HashSig =
sig
  val h : string array -> string -> unit
  val size : int
end
  
module BloomFilter :
  functor (H : HashSig) -> Mergetools.DataStructure with type t = string with type u = string array
