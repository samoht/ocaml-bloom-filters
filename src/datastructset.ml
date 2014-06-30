module type Setable = 
sig
  type t
  val equal : t -> t -> bool
end

module Set (A : Setable) =
struct
  type t = A.t
  type u = A.t list
  let nb_max = 300
  let rec vide_l (l : u list) (accu : u) : u= match l with
    |p::q -> 
      begin
	match p with
	|t::r -> vide_l ((r)::q) (t::accu) 
	|[] -> vide_l (q) (accu)
      end
    |[] -> accu
  let build_next l elem =
    vide_l l [elem]
  let build_next_l l lelem = 
    match lelem with
    |p::q -> 
      begin
	let rep_part = build_next l p in
	let rec add l accu = match l with
	  |p::q -> add q (p::accu)
	  |[] -> accu
	in
	add q rep_part
      end
    |[] -> 
      vide_l l []
  let build_union l =
    vide_l l []
  let rec test_belong elem set = match set with
    |p::q -> if (A.equal p elem) then true else (test_belong elem q)
    |[] -> false
end
