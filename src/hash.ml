module type HashSig =
sig
  type u
  type t
  val size : int
  val size_hash : int
  val create : unit -> u
  val h : u -> t -> unit
end

module Hash_multi  =
struct
  type u = string array
  type t = string
  let size = 20;;

  let size_hash = 320
  let theta = Array.make 20 0. ;;

for i = 0 to 19 do
  theta.(i) <- 0.00001 +. Random.float 0.99999
done;;

let get_number_from_binary_string s j l= 
  let n = String.length s in
  let compt = ref 1 in
  let rep = ref 0 in 
  for i = j to (j + l -1) do
    if (i < n && s.[i] <> '0') then (rep := !rep + !compt);
    compt := 2 * !compt;
  done;
  (*Printf.printf "%s -> %d\n" (String.sub s j l) (!rep);*)
  !rep;;

let compute_hash m k th = 
  
  let r = float_of_int k in
  let t = r *. th in
  let f = t -. ( float_of_int (int_of_float (t))) in
  let mf = (float_of_int m) *. f in
  let res = int_of_float mf in
  (*Printf.printf "m : %d\tr : %f\tt : %f\tf : %f\tmf : %f\tres : %d\n" m r t f mf res;*)
  res;;

let a_to_c a i =
  let n = Array.length a in
  let rep =ref 0 in
  let compt = ref 1 in
  for j = 0 to 7 do
    if (i+j < n && a.(i+j)) then (rep := !rep + !compt);
    compt := !compt * 2
  done;
  char_of_int (!rep);;

let a_to_s a = 
  let n = Array.length a in
  let m = n/8 in
  let rep = String.make m ' ' in
  for i = 0 to (m-1) do 
    rep.[i] <- a_to_c a (i*8)
  done;
  rep;;

let hash_multi size theta nb_on s =
  if s <> "" then
    begin
      let n = String.length s in
      let m = n/16 in
      let r = n mod 16 in
      let p = if (r = 0) then m else (m+1) in
  (*Printf.printf "p : %d\n" p;*)
      if (p = 0) then 
	begin
	  Printf.printf "WARNING DIVIDING BY 0\n";
	  Printf.printf "n : %d ; m : %d ; r : %d ; p : %d\n" n m r p;
	end;
      
      flush stdout;
      (*Printf.printf "sizeelem : %d\n" sizeelem;*)
      let rep = Array.make size false in
      let seed = ref 0 in
      (*let max_seed = expo2 sizeelem in*)
      (*Printf.printf "max_seed : %d\n" max_seed;*)
      flush stdout;
      let first = ref 0 in
      for i = 0 to (p-1) do
    (*Printf.printf "tour : %d\n" i ;*)
	flush stdout;
	let k = get_number_from_binary_string s (i*16) 16 in
	flush stdout;
	let s = compute_hash size k theta in
	(*Printf.printf "seed : %d --- s : %d\n" !seed s;*)
	flush stdout;
	if (i = 0) then (first := s);
	seed := (!seed + s) mod size
      done;
  (*Printf.printf "seed : %d\n" (!seed);*)
      flush stdout;
      let cur = ref (!seed) in
      (*Printf.printf "first : %d ; seed : %d\n" (!first) (!seed);*)
      for i = 0 to nb_on do
	rep.(!cur) <- true;
	cur := (!cur + !first) mod size
      done;
      a_to_s (rep)
    end
  else
    begin
      let rep = Array.make size false in
      a_to_s (rep)
    end
;;

let apply_hash_factor size nb_on theta_tbl arr s = 
  let n = Array.length theta_tbl in
  for i = 0 to (n-1) do
    arr.(i) <- hash_multi (size) theta_tbl.(i) nb_on s
  done;;

let h = apply_hash_factor size_hash 3 theta;;
let create () =  
  let rep = Array.make size (String.make (size_hash / 8) (char_of_int 0)) in
  for i = 0 to (size-1) do
    rep.(i) <- String.make (size_hash / 8) (char_of_int 0)
  done;
  rep
end
