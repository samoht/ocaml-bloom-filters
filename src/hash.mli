module type HashSig =
sig
  (** type u is the store in which element are hashed*)
  type u
  (** type t is the type of the element we want to hash *)
  type t
  val name : t -> string
  val size : int
  val size_hash : int
  val create : unit -> u
  (** [h store elem] modifies the store by adding the hashed values of elem*)

  val print_compte : unit -> unit
  val h : u -> t -> unit
end

module Hash_multi : HashSig with type t = string with type u = string array
module Hash_magnus : HashSig with type t = string with type u = string array
