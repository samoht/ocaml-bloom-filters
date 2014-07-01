module Truc = Mergetools.MergeTools(Alea.Buildtest)(Bloomfilter.BloomFilter(Hash.Hash_multi));;

module ToSet = 
struct
  type t = string
  let equal = (=)
end

module Test = Mergetools.MergeTools(Alea.Buildtest)(Datastructset.Set(ToSet));;

module Bf = Bloomfilter.BloomFilter(Hash.Hash_multi);;


