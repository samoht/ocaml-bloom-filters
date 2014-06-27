module type HashSig =
sig
  val h : string array -> string -> unit
  val size : int
end
  
module BloomFilter (H : HashSig) =
  struct
    type t = string
    type u = string array
    let nb_max = 200
    let add_char c1 c2 = 
      let aux = Array.make 8 0 in
      let r1 = ref (int_of_char c1) in
      let r2 = ref (int_of_char c2) in
      for i = 7 downto 0 do
	aux.(i)<- min 1 (((!r1) mod 2) + ((!r2) mod 2));
	r1 := !r1 /2;
	r2 := !r2 /2;
      done;
      let rep =ref 0 in
      let compt = ref 1 in
      for i = 7 downto 0 do
	rep := aux.(i) * !compt + !rep;
	compt := 2 * !compt;
      done;
      char_of_int (!rep)
    
    let add s1 s2 = 
      let m1 = String.length s1 in
      let m2 = String.length s2 in
      if (m1 <> m2) then
	() 
      else 
	begin
	  for i = 0 to (m1-1) do
	    let newc = add_char s1.[i] s2.[i] in
	    s2.[i] <- newc;
	  done
	end
    
    let binaire_char c = 
      let aux = String.make 8 '0' in
      let r = ref (int_of_char c) in
      for i = 7 downto 0 do
	let a = (!r) mod 2 in
	aux.[i] <- char_of_int (48 + a);
	r := !r /2;
      done;
      aux
    let binaire_string_p s = 
      let rep = ref "" in
      for i = 0 to (String.length (s) -1) do
	rep := !rep ^"|"^ (binaire_char s.[i])
      done;
      !rep
    
    let binaire_string s = 
      let rep = ref "" in
      for i = 0 to (String.length (s) -1) do
	rep := !rep ^ (binaire_char s.[i])
      done;
      !rep

    let test_under_c c1 c2 = 
      let r1 = ref (int_of_char c1) in
      let r2 = ref (int_of_char c2) in
      let i = ref 0 in
      let cont = ref true in
      while (!i < 8 && !cont) do
	let v1 =  (!r1) mod 2 in
	let v2 =  (!r2) mod 2 in
	cont := (v1 <= v2);
	r1 := !r1 /2;
	r2 := !r2 /2;
	incr i;
      done;
      !cont
	
    let test_under_s s1 s2 = 
      let n = String.length s1 in
      let i = ref 0 in
      while (!i < n && test_under_c (s1.[!i]) (s2.[!i])) do
	i := !i +1;
      done;
      !i = n

    let build_next l s =
      let n = H.size in
      let rep = Array.make n "" in
      H.h rep s;
      let build_parents_iter p = 
	for i = 0 to (n-1) do
	  add (p.(i)) (rep.(i))
	done;
      in
      List.iter build_parents_iter l;
      if (rep.(0) = "") then (Printf.printf "CREATION NUL\n");
      flush stdout;
      rep

    let build_union l =
      let n = H.size in
      let rep = Array.make n "" in
      H.h rep "";
      let build_parents_iter p = 
	for i = 0 to (n-1) do
	  add (p.(i)) (rep.(i))
	done;
      in
      List.iter build_parents_iter l;
      if (rep.(0) = "") then (Printf.printf "UNION NUL alors que %d\n" (List.length l));
      flush stdout;
      rep
    let test_belong s b = 
      let n = Array.length b in
      let rep = Array.make n "" in
      flush stdout;
      H.h rep s;
      flush stdout;
      let i = ref 0 in
      while (!i < n && test_under_s (rep.(!i)) (b.(!i))) do
	incr i
      done;
      !i = n;;
    let build_next_l l1 l2 = 
      match l2 with
      |p::q -> 
	begin
	  let rep = ref (build_next l1 p) in
	  let rec aux l = match l with
	    |p::q -> 
	      begin
		rep := build_next [!rep] p ; 
		aux q
	      end
	    |[] -> ()
	  in
	  aux q;
	  !rep
	end
      |[] -> build_union l1
    ;;
  end
