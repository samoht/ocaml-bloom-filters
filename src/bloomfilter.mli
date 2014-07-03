module Make :
  functor (H : Hash.HashSig with type u = string array) -> Mergetools.DataSig with type t = H.t with type u = string array
