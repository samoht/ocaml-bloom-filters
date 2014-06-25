
open Alea;;
open MyGraph;;
(*open Cryptokit;;
open Hash;;*)


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
  char_of_int (!rep);;

let add s1 s2 = 
  let m1 = String.length s1 in
  let m2 = String.length s2 in
  if (m1 <> m2) then
    () 
  else 
    begin
      for i = 0 to (m1-1) do
	let newc =add_char s1.[i] s2.[i] in
	s2.[i] <- newc;
      done
    end
;;

let rec split l a1 a2 = match l with
  |(a,b)::q ->  split q (a::a1) (b::a2)
  |[] -> (a1,a2)
;;

let binaire_char c = 
  let aux = String.make 8 '0' in
  let r = ref (int_of_char c) in
  for i = 7 downto 0 do
    let a = (!r) mod 2 in
    aux.[i] <- char_of_int (48 + a);
    r := !r /2;
  done;
  aux;;
let binaire_string_p s = 
  let rep = ref "" in
  for i = 0 to (String.length (s) -1) do
    rep := !rep ^"|"^ (binaire_char s.[i])
  done;
  !rep;;

let binaire_string s = 
  let rep = ref "" in
  for i = 0 to (String.length (s) -1) do
    rep := !rep ^ (binaire_char s.[i])
  done;
  !rep;;
(*l : list of the bf of parents of the node with name s, a : array oh hash function*)
let build_next_bf a l s = 
  let n = Array.length a in
  let rep = Array.make n "" in
  for i = 0 to (n-1) do
    rep.(i) <- a.(i) s
  done;
  let build_parents_iter p = 
    for i = 0 to (n-1) do
      add (p.(i)) (rep.(i))
    done;
  in
  List.iter build_parents_iter l;
  rep;;

(*the same but only one hash function h that changes all the bf*)
let build_next_bf_s h (l : string array list) (s : string) (size: int) =
  let n = size in
  let rep = Array.make n "" in
  h rep s;
  let build_parents_iter p = 
    for i = 0 to (n-1) do
      add (p.(i)) (rep.(i))
    done;
  in
  List.iter build_parents_iter l;
  if (rep.(0) = "") then (Printf.printf "CREATION NUL\n");
  flush stdout;
  rep;;

let build_union_bf_s h l size = 
  let n = size in
  let rep = Array.make n "" in
  h rep "";
  let build_parents_iter p = 
    for i = 0 to (n-1) do
      add (p.(i)) (rep.(i))
    done;
  in
  List.iter build_parents_iter l;
  if (rep.(0) = "") then (Printf.printf "UNION NUL alors que %d\n" (List.length l));
  flush stdout;
  rep;;

let max_l l = 
  let rep = ref min_int in
  let rec aux li = match li with
    |p::q -> if (p > !rep) then (rep := p ; aux q) else aux q
    |[] -> ()
  in
  aux l;
  !rep;;

let som_l l = 
  let rep = ref 0 in
  let rec aux li = match li with
    |p::q -> (rep := !rep +p) ; aux q
    |[] -> ()
  in
  aux l;
  !rep;;
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
  !cont;;

let test_under_s s1 s2 = 
  let n = String.length s1 in
  let i = ref 0 in
  while (!i < n && test_under_c (s1.[!i]) (s2.[!i])) do
    i := !i +1;
  done;
  !i = n;;

let test_belong a (*array of hash functions*) s (*string to test*) b (*bloom filter*) =
  let i = ref 0 in
  let n = Array.length a in
  while (!i < n && test_under_s (a.(!i) s) (b.(!i))) do
    incr i
  done;
  !i = n;;

let test_belong_s h s b debug=
  let n = Array.length b in
  let rep = Array.make n "" in
  if (debug) then (Printf.printf "10\n");
  flush stdout;
  h rep s;
  if (debug) then (Printf.printf "11\n");
  flush stdout;
  let i = ref 0 in
  while (!i < n && test_under_s (rep.(!i)) (b.(!i))) do
    incr i
  done;
  (*if (!i < n) then (Printf.printf "wrong test\t:%s\n\t%s\n" (binaire_string_p rep.(!i)) (binaire_string_p b.(!i)));*)
  !i = n;;
let compute_hist_diff g e1 e2 = 
  let ae1 = Hashtbl.create 10 in
  let rec visitee1 node = 
    if (Hashtbl.mem ae1 node) then 
      ()
    else 
      begin
	Hashtbl.add ae1 node true;
	MyGraph.iter_pred (visitee1) g node 
      end
  in
  visitee1 e1;
  let visited = Hashtbl.create 10 in
  let rep = ref 0 in
  let rec monte_rep node = 
    if (Hashtbl.mem visited node) then 
      ()
    else
      begin
	Hashtbl.add visited node true;
	if (Hashtbl.mem ae1 node) then
	  incr rep
	else
	  begin
	    incr rep;
	    MyGraph.iter_pred monte_rep g node
	  end
      end
  in
  monte_rep e2;
  !rep;;

let merge_opt nodel h size nb_max pere_bf_l = 
  let rep = ref pere_bf_l in
  let rec add_one l = match l with
    |p::q ->
      begin
	match (!rep) with
	|(nb,bf)::r -> 
	  begin
	    if (nb+1 > nb_max) then
	      begin
		let a = build_next_bf_s h [] p size in
		rep := (1,a) :: (!rep);
		add_one q
	      end
	    else
	      begin
		let a = build_next_bf_s h [bf] p size in
		rep := (nb+1,a) :: r;
		add_one q
	      end
	  end
	|[] -> rep := [1,build_next_bf_s h [] p size]; add_one q
      end
    |[] -> ()
  in
  add_one nodel;
  !rep;;

let build_next_bf_s_liste h l1 l2 size = 
  match l2 with
  |p::q -> 
    begin
      let rep = ref (build_next_bf_s h l1 p size) in
      let rec aux l = match l with
	|p::q -> 
	  begin
	    rep := build_next_bf_s h [!rep] p size ; 
	    aux q
	  end
	|[] -> ()
      in
      aux q;
      !rep
    end
  |[] -> build_union_bf_s h l1 size
;;
let build_next_border h bf parent_list size current_border =
  let rep = ref (current_border) in
  let nb_added = ref 0 in
  let one_elem node = 
    if ((test_belong_s h node bf false) || (false)) then 
      ()
    else
      begin
	rep := build_next_bf_s h [!rep] node size;
	nb_added := !nb_added + 1
      end
  in
  List.iter one_elem parent_list;
  !nb_added,!rep;;

let print_ss_bf cout bf =
  let n = Array.length bf in
  for i = 0 to (n-1) do
    Printf.fprintf cout ("%d\n") i;
    Printf.fprintf cout ("%s\n") (binaire_string bf.(i));
    flush cout;
  done;;

let merge_opt_2 nodel h size nb_max pere_bf_l border_bf_l g = 
  let rep = ref pere_bf_l in
  let repf = ref border_bf_l in
  let rec add_one l = match l with
    |p::q ->
      begin
	match (!rep) with
	|(nb,bf)::r -> 
	  begin
	    if (nb+1 > nb_max) then
	      begin
		let a = build_next_bf_s h [] p size in
		rep := (1,a) :: (!rep);
		let b = build_next_bf_s_liste h [] (MyGraph.pred g p) size in
		repf := (1,b) :: (!repf);
		add_one q;
	      end
	    else
	      begin
		let a = build_next_bf_s h [bf] p size in
		rep := (nb+1,a) :: r;
		begin
		  match (!repf) with
		  |[] -> failwith "empty border with non empty bf"
		  |(nb_border,border)::queue -> 
		    begin
		      let n,b= build_next_border h a (MyGraph.pred g p) size (border) in
		      repf := (nb_border +n, b)::queue
		    end;
		end;
		add_one q;
	      end
	  end
	|[] -> 
	  begin
	    Printf.printf "DÉBUT DE LA PILE %s\n" (binaire_to_hexa p);
	    rep := [1,build_next_bf_s h [] p size]; repf := [1,build_next_bf_s h [] p size]; add_one q
	  end
      end
    |[] -> ()
  in
  add_one nodel;
  !rep,!repf;;


let merge (s :string )  (parent_bf_l : (int * string array) list list) h size nb_max=
  let toadd = ref parent_bf_l in
  let beg = ref (build_next_bf_s h [] s size) in
  let som =ref 0 in
  let rec tete (l : (int * string array) list list) (accu_bf : string array list) (accu_size : int list) (accu_reste : (int * string array) list list) = match l with
    |p::q -> 
      begin
	match p with 
	|t::r -> tete q ((snd (t))::accu_bf) ((fst (t))::accu_size) (if r =  [] then (accu_reste) else ((r)::accu_reste))
	|[] -> failwith "no head"
      end
    |[] -> accu_bf,accu_size,accu_reste
  in
  let a,b,c = tete parent_bf_l [] [] [] in
  if (max_l b >nb_max) then 
    begin
      Printf.printf "WE NEED A NEW ONE\n";
      flush stdout;
      som := 1;
    end
  else
    begin
      beg := (build_next_bf_s h a s size);
      toadd := c;
      som := (som_l b) +1
    end;
  let rec next_layer l accu_sol accu_nb accu_reste = match l with
    |p::q -> 
      begin
	match (p) with
	|t::[] -> next_layer q ((snd t)::accu_sol) ((fst t) :: accu_nb) (accu_reste)
	|t::r::fin -> next_layer q ((snd t)::accu_sol) ((fst t) :: accu_nb) ((r::fin)::accu_reste)
	|[] -> next_layer q (accu_sol) accu_nb (accu_reste)
      end
    |[] -> accu_sol,accu_nb,accu_reste
  in
  if ((!beg).(0) = "") then (Printf.printf "WARNING\n");
  let rep = ref [(!som,!beg)] in
  let cont = ref true in
  while (!cont) do
    let d,f,e = next_layer (!toadd) [] [] [] in
    toadd := e;
    if (som_l f <> 0) then (if (d = []) then (Printf.printf "d is empty\n") ;rep := (som_l f,build_union_bf_s h (d) size):: (!rep));
    if (!toadd = []) then (cont := false);
  done;
  List.rev (!rep);;
    


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

let expo2 m = 
  let rep = ref 1 in
  for i = 1 to m do
    rep := 2 * !rep
  done;
  !rep;;

let to_string_size n m =
  let rep = String.make n '0' in
  let c= ref m in
  for i = 0 to (n-1) do
    let a = (!c) mod 256 in
    rep.[i] <- char_of_int a;
    c := !c / 256
  done;
  rep;;
let compute_hash m k th = 
  
  let r = float_of_int k in
  let t = r *. th in
  let f = t -. ( float_of_int (int_of_float (t))) in
  let mf = (float_of_int m) *. f in
  let res = int_of_float mf in
  (*Printf.printf "m : %d\tr : %f\tt : %f\tf : %f\tmf : %f\tres : %d\n" m r t f mf res;*)
  res;;

let multi_mod a b m = 
  let rep = ref a in
  for i = 2 to b do
    rep := (!rep + a) mod m
  done;
  !rep;;

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

let string_to_binaire_mod s i l m =
  let compt =ref 1 in
  let rep = ref 0 in
  for j = i to (i+l-1) do
    (*Printf.printf "%c : 2^(%d)[%d] = %d\n" s.[i] (j-i) m (!compt);*)
    if (s.[j] = '1') then (rep := (!rep + !compt) mod m);
    compt := (2 * !compt) mod m;
    
(*    Printf.printf "!rep : %d\n" (!rep);*)

  done;
  !rep;;
let get_a_b s size = 
  let m = String.length s in
  let a = string_to_binaire_mod s 0 (m/2) (size) in
  let b = string_to_binaire_mod s (m/2) (m/2) (size) in
  a,b;;
 
let hash_magnus size nb_on arr s =
  let m = String.length s in
  let n = Array.length arr in
  let a = string_to_binaire_mod s 0 (m/2) (size) in
  let b = string_to_binaire_mod s (m/2) (m/2) (size) in
  let aux = Array.make n ([||]) in
  let compt = ref 0 in
  for i = 0 to (n-1) do
    aux.(i) <- Array.make size false;
    for j = 0 to (nb_on-1) do
      let next = (a + (!compt) * b) mod size in
      aux.(i).(next) <- true;
      incr compt
    done;
    arr.(i) <- a_to_s (aux.(i));
    (*Printf.printf "Just computed : %s\n" (binaire_string_p arr.(i));*)
  done;
;;
  

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
      let sizeelem = size / p in
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

let print_bf bf =
  let n = Array.length bf in
  Printf.printf ("<bf>\n");
  for i = 0 to (n-1) do
    Printf.printf ("%s\n") (binaire_string bf.(i))
  done;
  Printf.printf ("<\\bf>\n");;
  
let print_bf_l cout bf_l =
  let rec eval l i = match l with
    |(nb,bf)::q -> 
      begin
	Printf.fprintf cout "Number : %d\n" i;
	Printf.fprintf cout "size : %d\n" nb;
	print_ss_bf cout bf;
	eval q (i+1)
      end
    |[] -> ()
  in
  eval bf_l 0;;

let prob p m k q = 
  let pf = float_of_int p in
  let mf = float_of_int m in
  let kf = float_of_int k in
  let qf = float_of_int q in
  (1. -. ((pf -. mf) /. pf)**(kf))**(mf*.qf)
;;

(*simulation complete du run d'un graphe de commig*)

let unif_graphe g g2 =
  let forall_vertex elem = 
    MyGraph.add_vertex g elem
  in
  let forall_edge deb fin = 
    MyGraph.add_edge g deb fin
  in
  MyGraph.iter_vertex forall_vertex g2;
  MyGraph.iter_edges forall_edge g2;;

let rec get_l i l accu= match l with
  |p::q -> (if i = 0 then (p,(accu@q)) else get_l (i-1) q (p::accu))
  |[] -> failwith "i too big"
;;

let give_history h bf ancestor current debug= 
  let rep = MyGraph.create () in
  let unfinished = ref [] in
  let already_visited = Hashtbl.create 10 in
  let rec visite node = 
    if (Hashtbl.mem already_visited node) then () 
    else
      begin
	Hashtbl.add already_visited node true;
	if (debug) then (Printf.printf "a9");
	let is_in = test_belong_s h node bf debug in
	if (debug) then (Printf.printf "b9");
	MyGraph.add_vertex rep node;
	let iter_son c = 
	  MyGraph.add_edge rep node c
	in
	MyGraph.iter_succ iter_son ancestor node;
	if (not is_in) then 
	  begin
	    if (MyGraph.pred ancestor node = []) then (unfinished := node :: !unfinished);
	    MyGraph.iter_pred visite ancestor node
	  end;
      end
  in
  visite current;
  (rep,!unfinished);;
      
let rec remove e l = match l with
  |p::q -> if (e = p) then q else (p::(remove e q))
  |[] -> []
;;

let give_history_2 h bf ancetre g node_list border debug=
  let node_of_interest = ref [] in
  let in_border = ref [] in
  let in_bf = ref [] in
  let explored = Hashtbl.create 10 in
  let explored_down = Hashtbl.create 10 in

  let rec explore_one boul node = 
    if debug then (Printf.printf "Explore called on %s with already explored %s\n" (binaire_to_hexa node) (if Hashtbl.mem explored node then "true" else "false"));
    if boul then
      begin
	if (Hashtbl.mem explored node) then
	  ()
	else 
	  begin
	    if (debug) then
	      begin
		Printf.printf "Exploring up node %s\n" (binaire_to_hexa node)
	      end;
	    
	    Hashtbl.add explored node true;
	    let is_in_bf = test_belong_s h node bf false in
	    if (is_in_bf) then 
	      begin
		if (debug) then
		  begin
		    Printf.printf "node_in bf : %s\n" (binaire_to_hexa node);
		  end;
		found_in_bf node;
	      end
	    else
	      begin
		let is_in_border = test_belong_s h node border false in
		if (is_in_border) then 
		  begin
		    
		    if (debug) then
		      begin
			Printf.printf "node_in border\n";
			print_ss_bf stdout border;
		      end;
		    found_in_border node
		  end
	        else 
		  begin
		    if (debug) then
		      begin
			Printf.printf "ni dans bf no dans border\n";
			MyGraph.iter_pred (fun x -> Printf.printf "gonna visit : %s\n" (binaire_to_hexa x)) ancetre node
		      end;
		    MyGraph.iter_pred (explore_one false) (ancetre) node;
		  end
	      end
	  end
      end
    else 
      begin
	if (Hashtbl.mem explored node) then
	  ()
	else
	  begin
	    if (MyGraph.mem_vertex g node) then 
	      ()
	    else
	      begin
		if (debug) then
		  begin
		    Printf.printf "Exploring up node %s\n" (binaire_to_hexa node);
		  end;
		Hashtbl.add explored node true;
		let is_in_bf = test_belong_s h node bf false in
		if (is_in_bf) then 
		  begin
		    if (debug) then
		      begin
			Printf.printf "node_in bf : %s\n" (binaire_to_hexa node);
		      end;
		    found_in_bf node
		  end
		else
		  begin
		    let is_in_border = test_belong_s h node border false in
		    if (is_in_border) then 
		      begin
			if (debug) then
			  begin
			    Printf.printf "node_in border\n";
			  end;
			found_in_border node
		      end
		    else 
		      begin
			if (debug) then
			  begin
			    Printf.printf "node ni dans border ni dans bf\n";
			    MyGraph.iter_pred (fun x -> Printf.printf "gonna visit : %s\n" (binaire_to_hexa x)) ancetre node
			  end;
			MyGraph.iter_pred (explore_one false) (ancetre) node;
		      end
		  end
	      end
	  end
      end
  and found_in_bf node = 
    in_bf := node :: (!in_bf);
  and found_in_border node = 
    in_border := node :: (!in_border);
  in
  List.iter (explore_one true) node_list;
  let rec deal_with_bf node = 
     if Hashtbl.mem explored_down node then () else
       begin
	 if (debug) then (Printf.printf "Going down : %s\n" (binaire_to_hexa node));
	Hashtbl.add explored_down node true;
	MyGraph.add_vertex g node;
	let add_edges_with_son son = 
	  MyGraph.add_edge g node son
	in
	MyGraph.iter_succ add_edges_with_son (ancetre) node;
	MyGraph.iter_succ deal_with_bf (ancetre) node
      end
  in
  let mark_down = Hashtbl.create 10 in
  let rec deal_with_border (node : string) = 
    if Hashtbl.mem mark_down node then
      ()
    else
      begin
	Hashtbl.add mark_down node true;
	let son = MyGraph.succ ancetre node in
	let rec keep_in_graphe l ing outg= match l with
	  |p::q -> (if (MyGraph.mem_vertex g p) then (keep_in_graphe q (p::ing) outg) else (keep_in_graphe q ing (p::outg)))
	  |[] -> (ing,outg)
	in
	let son_in,son_out = keep_in_graphe son [] [] in
	if (son_in <> []) then
	  begin
	    MyGraph.add_vertex g node;
	    List.iter (fun x -> MyGraph.add_edge g node x) son_in;
	    node_of_interest := (node) :: (!node_of_interest);
	  end;
	List.iter deal_with_border son_out;
      end
  in
  List.iter (deal_with_bf) (!in_bf);
  List.iter (deal_with_border) (!in_border);
  (g,!node_of_interest)
;;

let add_graph_nodes g lref =
  let to_iter node = 
    lref := node :: (!lref);
  in
  MyGraph.iter_vertex to_iter g;;
let print_graphe_element g = 
  let aux node = 
    Printf.printf "%s\n" node
  in
  MyGraph.iter_vertex aux g
;;

let iter_graphe_from_high f g start debug=
  let visited_up = Hashtbl.create 10 in
  let to_visite = ref [] in
  if debug then (Printf.printf "I0\n");
  flush stdout;
  let rec go_up node = 
    if Hashtbl.mem visited_up node then 
      ()
    else
      begin
	Hashtbl.add visited_up node true;
	if (MyGraph.pred g node = []) then
	  to_visite := node :: !to_visite
	else
	  (MyGraph.iter_pred go_up g node)
      end
  in
  go_up start;
  if debug then (Printf.printf "I1\n");
  flush stdout;
  let visited_down = Hashtbl.create 10 in
  let pred = Hashtbl.create 10 in
  let visite_node node = 
    if Hashtbl.mem visited_down node then
      ()
    else
      begin
	Hashtbl.add visited_down node true;
	f node;
	let deal_with_son son = 
	  if Hashtbl.mem pred son then
	    begin
	      let l = remove node (Hashtbl.find pred son) in
	      if l = [] then (to_visite := son :: !to_visite);
	      Hashtbl.replace pred son l
	    end
	  else 
	    begin
	      let l = remove node (MyGraph.pred g son) in
	      if l = [] then (to_visite := son :: !to_visite);
	      Hashtbl.replace pred son l
	    end
	in
	MyGraph.iter_succ deal_with_son g node
      end
  in
  while (!to_visite <> []) do
    let p::q = !to_visite in
    to_visite := q;
    visite_node p
  done;;

Random.init 0;;

let simule2 h g beg size nb_max =

(* STAT SUR LES ENVOIS*)
  let nb_envoi = ref 0 in
  let nb_envoi_bf = ref 0 in
  let nb_graph = ref 0 in
  let dif_cum = ref 0 in

  let bf_l = Hashtbl.create 10 in
  let ancetre = Hashtbl.create 10 in
  let left_before = Hashtbl.create 10 in
  let tovisite = ref [beg] in
  let visited = Hashtbl.create 10 in
  let border_l = Hashtbl.create 10 in
  let bf_merge_aux = ref "" in
  Hashtbl.add bf_l "" [];
  Hashtbl.add border_l "" [];

  let visite node = 
    Printf.printf "Visiting Node %s\n" node;
    flush stdout;
    let debug = "11001101010110100100011010100011011110000011100101111100111000000010111100100101010010010000100111101001010111000010001111000111011101011011110110011011110000110000" = node in
(*    let debug = "11000010110001101000000000111100011001111011111100010011000000011000110000001000101000011000010101001100101010010101101000101110100001010001000111110001001101110010" = node in*)
(*    let debug = false hexa_to_binaire ("c54647b0952b766a9b5c741105168142490e42c93") = node  in*)
    (*let debug = hexa_to_binaire ("cb39843d4076c80e2d9ff5db24a474aac9c523094") = node in*)
    if (debug) then 
      begin
	Printf.printf "DEBUG ACTIVATED\n";
	flush stdout;
      end;
    let peres = MyGraph.pred g node in
    let added_node_l = ref [] in
    if (peres <> [])  then 
      begin
	if (debug) then Printf.printf "D2\n";
	flush stdout;
	let want_to_merge,to_merge = get_l (HashName.int (List.length peres)) peres [] in
	if (debug) then Printf.printf "pere principal : %s\n" (binaire_to_hexa want_to_merge);
	bf_merge_aux := want_to_merge;
	let glist = ref [] in
	let deal_with_one_thread node_par =
	  incr nb_envoi;
	  if (debug) then Printf.printf "[1]dealing with %s for %s\n" (binaire_to_hexa node_par) (binaire_to_hexa node);
	  flush stdout;
	  let bf = ref (Hashtbl.find bf_l want_to_merge) in
	  let border_l_1,border_l_2 = split (Hashtbl.find border_l want_to_merge) [] [] in
	  if (debug) then Printf.printf "D1 :\n%s\n" node;
	  flush stdout;
	  let border_l_ref = ref (border_l_2) in
	  let border = build_union_bf_s h (border_l_2) size in
	  if (debug) then Printf.printf "D3\n";
	  flush stdout;
	  let g_loc = MyGraph.create () in
	  MyGraph.add_vertex g_loc node_par;
	  let node_of_interest = ref [node_par] in
	  while (!node_of_interest <> []) do
	    incr nb_envoi_bf;
	    match (!bf) with
	    |(a,p)::q -> 
	      begin
		bf := q;
		if (debug) then Printf.printf "D5\n";
		flush stdout;
		let graphe,nl =
		  match (!border_l_ref) with
		  |t::r -> 
		    begin
		      (*let border =  build_union_bf_s h (!border_l_ref) size in 
		      border_l_ref := r;
		      if (debug) then (print_bf_l stdout ((Hashtbl.find border_l want_to_merge)));*)
		      if (debug) then (print_ss_bf stdout border);
		      give_history_2 h p (Hashtbl.find ancetre node_par) g_loc (!node_of_interest) border debug
		    end
		  |[] -> failwith "impossible";
		in
		if (debug) then
		  begin
		    print_graphe_element g_loc;
		    if (debug) then Printf.printf "node :\n%s\n" node_par;
		  end;
		if (debug) then Printf.printf "D6\n";
		flush stdout;
		node_of_interest := nl;
	      end
	    |[] -> failwith "no more bloom filters"
	  done;
	  let size_opt = compute_hist_diff g want_to_merge node_par in
	  let size_real = MyGraph.nb_vertex g_loc in
	  incr nb_graph;
	  dif_cum := abs (size_opt - size_real) + !dif_cum;
	  glist := (node_par,g_loc) :: !glist
	in
	List.iter deal_with_one_thread to_merge;
	let f node_in = 
	  added_node_l := node_in :: (!added_node_l)
	in
	if (debug) then Printf.printf "D7\n";
	flush stdout;
	List.iter (fun x -> iter_graphe_from_high f (snd x) (fst x) debug) !glist;
	if (debug) then Printf.printf "D4\n";
	  flush stdout;

	let graph_sol = MyGraph.copy (Hashtbl.find ancetre want_to_merge) in
	List.iter (fun x -> unif_graphe graph_sol (snd x)) !glist;
	
	MyGraph.add_vertex graph_sol node;
	MyGraph.iter_pred (fun x -> MyGraph.add_edge graph_sol x node) g node;

	Hashtbl.add ancetre node graph_sol;
      end
    else
      begin
	let graph_sol = MyGraph.create () in
	MyGraph.add_vertex graph_sol node;
	Hashtbl.add ancetre node graph_sol;
      end;

    let (pere_bf_l : (int * string array) list) = Hashtbl.find bf_l (!bf_merge_aux) in
    let border_bf_l = Hashtbl.find border_l (!bf_merge_aux) in
    if (debug) then
      begin
	let cout3 = open_out ("./debug/bord_before_"^node) in
	print_bf_l cout3 border_bf_l;
      end;

    added_node_l := (node :: !added_node_l);
    added_node_l := List.rev (!added_node_l);
    let bf_l_sol,border_l_sol = merge_opt_2 (!added_node_l) h size nb_max (pere_bf_l : (int * string array) list) border_bf_l (Hashtbl.find ancetre node) in
    Hashtbl.add bf_l node bf_l_sol;
    Hashtbl.add border_l node border_l_sol;
    if (debug) then
      begin
	let cout = open_out ("./debug/bf_"^node) in
	print_bf_l cout bf_l_sol;
	let cout2 = open_out ("./debug/bord_"^node) in
	print_bf_l cout2 border_l_sol;
	List.iter (fun x -> Printf.printf "adding in %s : %s\n" node x) (!added_node_l); 
      end;
    let gere_fils fils = 
      if (Hashtbl.mem left_before fils) then 
	let a = Hashtbl.find left_before fils in
	let l = remove node a in
	(*Printf.printf "[R]%s -> %d\n" fils (List.length l);*)
	Hashtbl.replace left_before fils (l);
	if (l = []) then
	  tovisite := fils :: (!tovisite);
	
      else 
	let l = remove node (MyGraph.pred g fils) in
	Hashtbl.add left_before fils (l);
	(*Printf.printf "[A]%s -> %d\n" fils (List.length l);*)
	if (l = []) then
	  tovisite := fils :: (!tovisite);
    in
    MyGraph.iter_succ (gere_fils) g node;
    
  in
  while (!tovisite <> []) do
    let p::q = !tovisite in
    tovisite := q;
    
    if (Hashtbl.mem visited p) then 
      ()
    else
      begin
	Hashtbl.add visited p true;
	visite p;
      end
  done;
  bf_l,ancetre, ((float_of_int (!dif_cum)) /. (float_of_int (!nb_graph))),(float_of_int (!nb_envoi_bf) /. float_of_int (!nb_envoi));;


(*
let simule2 h g beg size nb_max = 
  let bf_l = Hashtbl.create 10 in
  let ancetre = Hashtbl.create 10 in
  let left_before = Hashtbl.create 10 in
  let tovisite = ref [beg] in
  let visited = Hashtbl.create 10 in
  let border_l = Hashtbl.create 10 in
  let bf_merge_aux = ref "" in
  Hashtbl.add bf_l "" [];
  Hashtbl.add border_l "" [];

  let visite node = 
    Printf.printf "Visiting Node %s\n" node;
    flush stdout;
    let debug = "0000110010100000110000000111011011101001111101010001001101000010000011010100101011110011100111111011111001001100100100110011011011000101110111000100011001101110" = node in
    if (debug) then 
      begin
	Printf.printf "DEBUG ACTIVATED\n";
	flush stdout;
      end;
    let peres = MyGraph.pred g node in
    let added_node_l = ref [] in
    if (peres <> [])  then 
      begin
	if (debug) then Printf.printf "D2\n";
	flush stdout;
	let want_to_merge,to_merge = get_l (HashName.int (List.length peres)) peres [] in
	Printf.printf "pere principal : %s\n" want_to_merge;
	bf_merge_aux := want_to_merge;
	let glist = ref [] in
	let deal_with_one_thread node_par =
	  Printf.printf "[1]dealing with %s for %s\n" node_par node;
	  flush stdout;
	  let bf = ref (Hashtbl.find bf_l want_to_merge) in
	  let border_l_1,border_l_2 = split (Hashtbl.find border_l want_to_merge) [] [] in
	  Printf.printf "[2]dealing with %s for %s\n" node_par node;
	  if (debug) then Printf.printf "D1 :\n%s\n" node;
	  flush stdout;
	  let border_l_ref = ref (border_l_2) in
	  
	  if (debug) then Printf.printf "D3\n";
	  flush stdout;
	  let g_loc = MyGraph.create () in
	  MyGraph.add_vertex g_loc node_par;
	  let node_of_interest = ref [node_par] in
	  while (!node_of_interest <> []) do
	    match (!bf) with
	    |(a,p)::q -> 
	      begin
		bf := q;
		if (debug) then Printf.printf "D5\n";
		flush stdout;
		let graphe,nl =
		  match (!border_l_ref) with
		  |t::r -> 
		    begin
		      let border =  build_union_bf_s h (!border_l_ref) size in 
		      border_l_ref := r;
		      give_history_2 h p (Hashtbl.find ancetre node_par) g_loc (!node_of_interest) border false
		    end
		  |[] -> failwith "impossible";
		in
		if (debug) then
		  begin
		    print_graphe_element g_loc;
		    Printf.printf "node :\n%s\n" node_par;
		  end;
		if (debug) then Printf.printf "D6\n";
		flush stdout;
		node_of_interest := nl;
	      end
	    |[] -> failwith "no more bloom filters"
	  done;
	  if (debug) then
	  begin
	    print_graphe_element g_loc;
	    Printf.printf "node :\n%s\n" node_par;
	  end;
	  let file = open_out_bin ("./debug/"^node^"-"^node_par) in
	  ToDot.init ();
	  Dot.output_graph file g_loc;
	  glist := (node_par,g_loc) :: !glist
	in
	List.iter deal_with_one_thread to_merge;
	let f node_in = 
	  added_node_l := node_in :: (!added_node_l)
	in
	if (debug) then Printf.printf "D7\n";
	flush stdout;
	List.iter (fun x -> iter_graphe_from_high f (snd x) (fst x) debug) !glist;
	if (debug) then Printf.printf "D4\n";
	  flush stdout;

	let graph_sol = MyGraph.copy (Hashtbl.find ancetre want_to_merge) in
	List.iter (fun x -> unif_graphe graph_sol (snd x)) !glist;
	
	MyGraph.add_vertex graph_sol node;
	MyGraph.iter_pred (fun x -> MyGraph.add_edge graph_sol x node) g node;

	Hashtbl.add ancetre node graph_sol;
      end
    else
      begin
	let graph_sol = MyGraph.create () in
	MyGraph.add_vertex graph_sol node;
	Hashtbl.add ancetre node graph_sol;
      end;

    let (pere_bf_l : (int * string array) list) = Hashtbl.find bf_l (!bf_merge_aux) in
    let border_bf_l = Hashtbl.find border_l (!bf_merge_aux) in
    let cout3 = open_out ("./debug/bord_before_"^node) in
    print_bf_l cout3 border_bf_l;

    added_node_l := (node :: !added_node_l);
    added_node_l := List.rev (!added_node_l);
    let bf_l_sol,border_l_sol = merge_opt_2 (!added_node_l) h size nb_max (pere_bf_l : (int * string array) list) border_bf_l (Hashtbl.find ancetre node) in
    Hashtbl.add bf_l node bf_l_sol;
    Hashtbl.add border_l node border_l_sol;
    let cout = open_out ("./debug/bf_"^node) in
    print_bf_l cout bf_l_sol;
    let cout2 = open_out ("./debug/bord_"^node) in
    print_bf_l cout2 border_l_sol;
    List.iter (fun x -> Printf.printf "adding in %s : %s\n" node x) (!added_node_l); 
    let gere_fils fils = 
      if (Hashtbl.mem left_before fils) then 
	let a = Hashtbl.find left_before fils in
	let l = remove node a in
	(*Printf.printf "[R]%s -> %d\n" fils (List.length l);*)
	Hashtbl.replace left_before fils (l);
	if (l = []) then
	  tovisite := fils :: (!tovisite);
	
      else 
	let l = remove node (MyGraph.pred g fils) in
	Hashtbl.add left_before fils (l);
	(*Printf.printf "[A]%s -> %d\n" fils (List.length l);*)
	if (l = []) then
	  tovisite := fils :: (!tovisite);
    in
    MyGraph.iter_succ (gere_fils) g node;
    
  in
  while (!tovisite <> []) do
    let p::q = !tovisite in
    tovisite := q;
    
    if (Hashtbl.mem visited p) then 
      ()
    else
      begin
	Hashtbl.add visited p true;
	visite p;
      end
  done;
  bf_l,ancetre;;
*)
let simule h g beg size nb_max = 
  let bf_l = Hashtbl.create 10 in
  let ancetre = Hashtbl.create 10 in
  let left_before = Hashtbl.create 10 in
  let tovisite = ref [beg] in
  let visited = Hashtbl.create 10 in
  Hashtbl.add bf_l "" [];
  (*
    Hashtbl.add ancetre (beg) (MyGraph.create ());
    Hashtbl.add bf_l (beg) ;
  *)
  let debug = ref false in
  let visite node =
    (*if (node = "011111111100001010000111111101") then (debug := true) else (debug := false) ; *)
    Printf.printf "Entering : %s\n" node ;
    flush stdout;

    let new_nodes = ref [] in
    
    if (!debug) then ( Printf.printf "0\n");
    let peres = MyGraph.pred g node in
    let bf_merge_aux = ref "" in
    if (peres <> [])  then 
      begin
	let want_to_merge,to_merge = get_l (HashName.int (List.length peres)) peres [] in
	bf_merge_aux := want_to_merge;
	if (!debug) then (Printf.printf "1\n");
	let rec get_history_list bf l accuhisto accuunfinished = match l with
	  |p::q -> 
	    begin
	      let history,unfinished = give_history h (bf) (Hashtbl.find ancetre p) p (!debug) in
	      get_history_list bf q (history::accuhisto) (unfinished@accuunfinished)
	    end
	  |[] -> accuhisto,accuunfinished
	in

	if (!debug) then (Printf.printf "2\n");
	let unfinished = ref to_merge in
	let histo = ref [] in
	let bf_to_send = ref (Hashtbl.find bf_l want_to_merge) in

	if (!debug) then (Printf.printf "3\n");
	while (!unfinished <> []) do
	  let bf = 
	    match (!bf_to_send) with
	    |p::q -> (bf_to_send := q) ; snd p
	    |[] -> failwith "still unfinished but no more bf"
	  in
	  if (!debug) then (Printf.printf "4\n");
	  let a,b = get_history_list bf (!unfinished) [] [] in
	  if (!debug) then (Printf.printf "5\n");
	  
	  unfinished := b;
	  histo := a @ (!histo);
	done;

	
	let graph_sol = MyGraph.copy (Hashtbl.find ancetre want_to_merge) in
    
	let rec manage_histo l = match l with
	  |p::q -> unif_graphe graph_sol p; add_graph_nodes p new_nodes ;manage_histo q
	  |[] -> ()
	in
	manage_histo (!histo);
	MyGraph.add_vertex graph_sol node;
	
	
	let rec add_edges_with_parents l = match l with
	  |p::q -> MyGraph.add_edge graph_sol p node; add_edges_with_parents q
	  |[] -> ()
	in
	add_edges_with_parents peres;
	Hashtbl.add ancetre node graph_sol;
      end
    else 
      begin
	let graph_sol = MyGraph.create () in
	MyGraph.add_vertex graph_sol node;
	Hashtbl.add ancetre node graph_sol;
      end;
    let pere_bf_l = Hashtbl.find bf_l (!bf_merge_aux) in
    new_nodes := (node :: !new_nodes);
    let bf_l_sol = merge_opt (!new_nodes) h size nb_max (pere_bf_l : (int * (string array)) list)  in
    Hashtbl.add bf_l node bf_l_sol;
      
    
(*
    let rep_par = ref [] in
    let toiter_parents par = 
      rep_par := (Hashtbl.find bf_l par) :: !rep_par
    in
    MyGraph.iter_pred toiter_parents g node;
    if (!rep_par = []) then (Printf.printf "%s has no parents\n" node);
    let new_bftest = merge node (!rep_par) h size nb_max in
    Hashtbl.add bf_l node new_bftest;
*)    
    let gere_fils fils = 
      if (Hashtbl.mem left_before fils) then 
	let a = Hashtbl.find left_before fils in
	let l = remove node a in
	(*Printf.printf "[R]%s -> %d\n" fils (List.length l);*)
	Hashtbl.replace left_before fils (l);
	if (l = []) then
	  tovisite := fils :: (!tovisite);
	
      else 
	let l = remove node (MyGraph.pred g fils) in
	Hashtbl.add left_before fils (l);
	(*Printf.printf "[A]%s -> %d\n" fils (List.length l);*)
	if (l = []) then
	  tovisite := fils :: (!tovisite);
    in
    MyGraph.iter_succ (gere_fils) g node;
    
  in
  while (!tovisite <> []) do
    let p::q = !tovisite in
    tovisite := q;
    
    if (Hashtbl.mem visited p) then 
      ()
    else
      begin
	Hashtbl.add visited p true;
      visite p;
      end
  done;
  bf_l,ancetre;;





let print_graphe name g = 
  let file = open_out_bin (name) in
  ToDot.init ();
  MyDot.output_graph file g;;

let ancetre g a = 
  let res = MyGraph.create () in
  let already_visited = Hashtbl.create 10 in
  let nbvi = ref 0 in
  let rec visite node =
    if (Hashtbl.mem already_visited node) then
      ()
    else 
      begin
	Hashtbl.add already_visited node true;
	(*Printf.printf "Visiting %s %d\n" node (!nbvi);*)
	incr nbvi;
	MyGraph.add_vertex res node;
	let add_pere pere = 
	  MyGraph.add_edge res pere node;
	in
	MyGraph.iter_pred add_pere g node;
	MyGraph.iter_pred visite g node
	  
      end
  in
  visite a;
  res;;

let inclus g1 g2 = 
  let rep = ref true in
  let iter_vertex node = 
    if (not (MyGraph.mem_vertex g2 node)) then (rep := false)
  in
  let iter_edge a b = 
    if (not (MyGraph.mem_edge g2 a b)) then (rep := false)
  in
  MyGraph.iter_vertex iter_vertex g1;
  MyGraph.iter_edges iter_edge g1;
  !rep
;;

let egale u v =
  (inclus u v) && (inclus v u);;

let rec is_in_one_of_bf h node bf_l i = match bf_l with
  |p::q -> if (test_belong_s h node (snd p) false) then (i) else (is_in_one_of_bf h node q (i+1))
  |[] -> (-1)
;;
let nb_bit_1_s s = 
  let bs = binaire_string s in
  let n = String.length bs in
  let rep = ref 0 in
  for i = 0 to (n-1) do
    if (bs.[i] = '1') then incr rep;
  done;
  !rep;;

let nb_bit_1_bf b = 
  let n = Array.length b in
  let rep = ref 0. in
  for i = 0 to (n-1) do 
    rep := (float_of_int (nb_bit_1_s b.(i))) +. !rep;
  done;
  rep := !rep /. (float_of_int n);
  !rep;;

let stat_bf bf_l : float array * float array = 
  let size = List.length bf_l in
  let nb_bit_at_1 = Array.make (size) 0. in
  let max_size = Array.make size 0. in
  let rec parcours l i = match l with
    |(a,b)::q -> 
      begin
	max_size.(i) <- (float_of_int a);
	nb_bit_at_1.(i) <- nb_bit_1_bf b;
	parcours q (i+1)
      end
    |[] -> ()
  in
  parcours bf_l 0;
  max_size,nb_bit_at_1;;

let participation p rep =
  let n = Array.length p in
  for i = 0 to (n-1) do 
    let a,b = rep.(i) in
    rep.(i) <- (a+1,b+.p.(i))
  done;;

let max_array_size l = 
  let rep =ref min_int in
  let rec aux li = match li with
    |p::q ->
      begin
	let n = Array.length p in
	if (n > !rep) then (rep := n);
	aux q
      end
    |[] -> ()
  in
  aux l;
  !rep;;

let average l =
  let l1,l2 = split l [] [] in
  let n = max_array_size l1 in
  Printf.printf "Average, n = %d\n" n;
  flush stdout;
  let rep1 = Array.make n (0,0.) in
  let rep2 = Array.make n (0,0.) in
  let rrep1 = Array.make n 0. in
  let rrep2 = Array.make n 0. in
  let rec parcours l i = match l with
    |p::q -> ( participation p (if i = 1 then rep1 else rep2)) ; parcours q i
    |[] -> ()
  in
  parcours l1 1;
  parcours l2 2;
  for i = 0 to (n-1) do 
    rrep1.(i) <- (((snd (rep1.(i)))) /.(float_of_int (fst (rep1.(i)))));
    rrep2.(i) <- (((snd (rep2.(i)))) /.(float_of_int (fst (rep2.(i)))));
  done;
  rrep1,rrep2;;

let get_exemple () = 
  let g = MyGraph.create () in
  MyGraph.add_vertex g "0000";

  MyGraph.add_vertex g "0001";
  MyGraph.add_vertex g "0010";
  MyGraph.add_vertex g "0011";
  MyGraph.add_vertex g "0100";
  MyGraph.add_vertex g "0101";

  MyGraph.add_vertex g "1001";
  MyGraph.add_vertex g "1010";
  MyGraph.add_vertex g "1011";
  MyGraph.add_vertex g "1100";
  MyGraph.add_vertex g "1101";

  MyGraph.add_vertex g "1111";

  MyGraph.add_edge g "0000" "0001";
  MyGraph.add_edge g "0001" "0010";
  MyGraph.add_edge g "0010" "0011";
  MyGraph.add_edge g "0011" "0100";
  MyGraph.add_edge g "0100" "0101";
  MyGraph.add_edge g "0101" "1111";

  MyGraph.add_edge g "0000" "1001";
  MyGraph.add_edge g "1001" "1010";
  MyGraph.add_edge g "1010" "1011";
  MyGraph.add_edge g "1011" "1100";
  MyGraph.add_edge g "1100" "1101";
  MyGraph.add_edge g "1101" "1111";
  g,"0000";;

let remove_useless g = 
  let to_iter node = if (node = "r") then (MyGraph.remove_vertex g node) in
  MyGraph.iter_vertex to_iter
;;
let print_graph g = 
  let to_iter_node node = Printf.printf "%s\n" node in
  let to_iter_edge e1 e2  = Printf.printf "%s -> %s\n" e1 e2 in
  MyGraph.iter_vertex to_iter_node g;
  MyGraph.iter_edges to_iter_edge g;;

let one_head g = 
  let size = ref (-1) in
  let biggest = ref [] in
  let parcours node = 
    if (!size = -1) then (size := String.length node);
    if (MyGraph.pred g node = []) then (biggest := (node) :: !biggest);
  in
  MyGraph.iter_vertex parcours g;
  if (!size = -1) then
    ""
  else
    begin
      match (!biggest) with
      |p::[] ->
	begin
	  p
	end
      |p::q::r -> 
	begin
	  let sol = String.make (!size) '0' in
	  MyGraph.add_vertex g sol;
	  List.iter (fun x -> MyGraph.add_edge g sol x) (!biggest);
	  sol
	end
      |[] ->
	failwith "pas un dag"
    end
;;

let main () = 
  let testing_repartition = false in
  let test_bf = false in
  let testing_ancestors =  true in
  let measuring_bf = false in
  let testing_bf = true in
  let f_hach = true in (*true -> factor , false -> magnus*)
  let nb_hach = 20 in
  let nb_test_repart = 10000000 in
  let theta_tbl = Array.make nb_hach (0.) in
  for i = 0 to (nb_hach -1) do
    theta_tbl.(i) <- 0.00001+. HashName.float (0.99999);
    Printf.printf "%f - " theta_tbl.(i);
  done;
  Printf.printf "\n";
  
  let hash_fun = (if f_hach then apply_hash_factor 320 2 theta_tbl else hash_magnus 320 2) in
  let size_graphe = 1000 in 
  let prof_max = 800 in 
  let nb_test = string_of_int (14) in
  (*let g,tete = alea size_graphe prof_max 160 0.5 in*)
  let g = MyParsor.parse "./testdot/foopgl.dot" in
  MyGraph.remove_vertex g "r";
  let tete = one_head g in
(*get_exemple () in*)
  Printf.printf "FIN DE LA CREATION DU GRAPHE\n";
  flush stdout;
  let name0 = "test_simule/test_simule"^(nb_test)^"/graphe_main.dot" in
  print_graphe name0 g;
  let a,b,c,d = simule2 (hash_fun) g tete nb_hach 200 in
  let name1 = "test_simule/test_simule13/test.dot" in
  print_graphe name1 (Hashtbl.find b (hexa_to_binaire ("c54647b0952b766a9b5c741105168142490e42c93")));
  Printf.printf "Diff_opt : %.6e --- Nb_envoi : %.6e\n" c d;
  Printf.printf "Simulation Done\n";
  flush stdout;
  let name0 = "test_simule/test_simule"^(nb_test)^"/graphe_main.dot" in
  print_graphe name0 g;

  if testing_repartition then
    begin

      let test_repart_a = Array.make 320 0 in
      let test_repart_b = Array.make 320 0 in
      for i = 0 to (nb_test_repart-1) do
	HashName.init ();
	let a = HashName.newname 160 in
	let ma,mb = get_a_b a 320 in
	if (i mod 100 = 0) then (Printf.printf "%d a = %d\t b = %d\n" i ma mb);
	flush stdout;
	test_repart_a.(ma) <- test_repart_a.(ma)+1;
	test_repart_b.(mb) <- test_repart_b.(mb)+1;
      done;
      let cout1 = open_out "reparta_magnus" in
      let cout2 = open_out "repartb_magnus" in
      for i=0 to (319) do
	Printf.fprintf cout1 "%d %d\n" i test_repart_a.(i);
	Printf.fprintf cout2 "%d %d\n" i test_repart_b.(i);
      done;
      close_out cout1;
      close_out cout2;
      
    end
  ;
  if testing_ancestors then
    begin
      Printf.printf "=====Starting to test Ancestors=====\n";
      let rep = Hashtbl.create 10 in

      let nb = ref 0 in
      let iter_on_graph a = 
	Printf.printf "[BUILDING ANCESTORS] %d/%d %s\n" (!nb) size_graphe a;
	let ma,mb = get_a_b a 320 in
	Printf.printf "a = %d\t b = %d\n" ma mb;
	flush stdout;

	incr nb;
	Hashtbl.add rep a (ancetre g a) 
      in
      MyGraph.iter_vertex iter_on_graph g;
      nb := 0;
      let repbool = ref true in
      let test_egal k v = 
	Printf.printf "[CHECKING ANCESTORS] %d/%d %s\n" (!nb) size_graphe k;
	flush stdout;
	incr nb;
	let test = egale v (Hashtbl.find b k) in
	if (not test) then (Printf.printf "[CHECKING FAILED] %s\n" k;
			    let namenorm = "test_simule/test_simule"^(nb_test)^"/graphe_failed_theorique.dot" in
			    print_graphe namenorm v;
			    let namefailed = "test_simule/test_simule"^(nb_test)^"/graphe_failed_failed.dot" in
			    print_graphe namefailed (Hashtbl.find b k);
			    failwith "Check Failed");
	repbool := ((!repbool) && test) 
      in
      iter_graphe_from_high (fun x -> test_egal x (Hashtbl.find rep x)) g (hexa_to_binaire "c63b3e95c0c2aab51c7cc1d656f07eaebb47070c3") false;
      (*Hashtbl.iter (test_egal) rep;*)
      Printf.printf "Test Ancetre : %s\n" (if (!repbool) then "[OK]" else "[FAIL]");
      flush stdout;
      if testing_bf then 
	begin

	  Printf.printf "=====Starting to test Bloomfilters=====\n";
	  let fpstat = ref [] in
	  let nbfp = ref 0 in
	  let nbfn = ref 0 in
	  let nbgood = ref 0 in
	  let nb1 = ref 0 in
	  
	  let to_iter_test_bf node = 
	    Printf.printf "Test bf %d\n" (!nb1);
	    flush stdout;
	    incr nb1;
	    let ancetre = Hashtbl.find rep node in
	    let bf_l = Hashtbl.find a node in    
	    let to_iter_on_others b =
	      let is_in_really = MyGraph.mem_vertex ancetre b in
	      let is_in_bf = is_in_one_of_bf (hash_fun) b bf_l 0 in
	      if (is_in_bf == -1) then 
		begin 
		  if (not is_in_really) then 
		    incr nbgood
		  else 
		    incr nbfn
		end
	      else 
		begin
		  if (not is_in_really) then
		    begin
		      incr nbfp;
		      fpstat := (is_in_bf :: !fpstat);
		    end
		  else
		    incr nbgood
		end
	      ;
	    in
	    MyGraph.iter_vertex (to_iter_on_others) g;
	  in
	  MyGraph.iter_vertex (to_iter_test_bf) g;
	  let tot = float_of_int (!nbfp + !nbfn + !nbgood) in
	  let ffp = float_of_int (!nbfp) in
	  let ffn = float_of_int (!nbfn) in
	  let fgood = float_of_int (!nbgood) in
	  Printf.printf "RESULTAT : nbfp = %.6e - nbfn = %.6e - nbgood = %.6e - tot = %f\n" (ffp/.tot) (ffn/.tot) (fgood/.tot) tot;
	  let maxl = max_l (!fpstat) in
	  if (maxl >= 0) then 
	    begin
	      let stat_prof = Array.make (maxl +1) 0 in
	      let rec vide l = match l with
		|p::q -> stat_prof.(p) <- stat_prof.(p) +1 ; vide q
		|[] -> ()
	      in
	      vide (!fpstat);
	      for i = 0 to maxl do
		Printf.printf "%d %d\n" i (stat_prof.(i))
	      done;
	    end
	end;
    end;
  if measuring_bf then
    begin
      Printf.printf "=====Starting to measure bloomfilters=====\n";
      (*etude du nombre de bit et du max size en fonction de la profondeur*)
      let prof = Hashtbl.create 10 in
      
      let rec parcours_prof i node = 
	if  Hashtbl.mem (prof) node then 
	  ()
	else
	  begin
	    
	    Printf.printf "[PROFONDEUR COMPUTING] : %d\n" i;
	    flush stdout;
	    Hashtbl.add (prof) node i;
	    MyGraph.iter_succ (parcours_prof (i+1)) g node
	  end
      in
      parcours_prof 0 tete;
      
      Printf.printf "[PROFONDEUR COMPUTED]\n";
      flush stdout;
      let measure_bf_table = Hashtbl.create 10 in (*int -> (float array * float array)*)
      let measure_bf node = 
	let bf_l = Hashtbl.find a node in
	let prof_node = Hashtbl.find prof node in
	let a_ms,a_nb_bit = stat_bf bf_l in
	Hashtbl.add measure_bf_table (prof_node) (a_ms,a_nb_bit);
      in
      MyGraph.iter_vertex measure_bf g;
      
      Printf.printf "[MEASURE DONE]\n";
      flush stdout;
      let moyenne prof = 
	let (l : (float array * float array) list ) = Hashtbl.find_all measure_bf_table prof in
	if (l = []) then (Printf.printf "Empty list%d\n" prof);
	Hashtbl.replace measure_bf_table prof (average l);
      in
      for i =0 to (prof_max-1) do
	moyenne i
      done;
      Printf.printf "[AVERAGE COMPUTED]\n";
      flush stdout;
      let nb_bf_max = ref 0 in
      let to_iter_on_prof k value = 
	let n = Array.length (fst value) in
	if (n > !nb_bf_max) then (nb_bf_max := n);
      in
      Hashtbl.iter (to_iter_on_prof) measure_bf_table;
      let n = !nb_bf_max in 
      Printf.printf "[NB MAX] : %d\n" n;
      let cout_a_ms = Array.make n (stdout) in
      let cout_a_nb_bit = Array.make n (stdout) in
      for i = 0 to (n-1) do
	cout_a_ms.(i) <- open_out ("test_simule/test_simule"^(nb_test)^"/max_size_"^(string_of_int i));
	cout_a_nb_bit.(i) <- open_out ("test_simule/test_simule"^(nb_test)^"/nb_bit_"^(string_of_int i));
      done;

      for i = 0 to (prof_max -1 ) do
	let a,b = Hashtbl.find measure_bf_table i in
	let n = Array.length a in
	for j= 0 to (n-1) do
	  Printf.fprintf (cout_a_ms.(j)) "%d %f\n" i a.(j);
	  Printf.fprintf (cout_a_nb_bit.(j)) "%d %f\n" i b.(j);
	done
      done;
      
      Printf.printf "[PRINTING FINISHED]\n";
      flush stdout;
    end;


  
  (*
    let to_iter_bf key value = 
    let cout = open_out ("test_simule/test_simule"^(nb_test)^"/bf_"^key) in
    print_bf_l cout value;
    close_out cout;
    in
    let to_iter_ancestor key value = 
    let name = "test_simule/test_simule"^(nb_test)^"/graphe_"^key^".dot" in
    print_graphe name value
    in
    Hashtbl.iter to_iter_bf a;
    Hashtbl.iter to_iter_ancestor b;

  *)
  
  Printf.printf "End\n";


(*petit test*)
(*
  let cout = open_out "etudeproba/640_2_k_20" in
  for k = 0 to 1000 do
  let res = prob 640 2 k 15 in
  Printf.fprintf cout "%d %.6e\n" k res;
  done;
  close_out cout;
*)



(*test comparaison hash functions*)
if test_bf then
  begin
  let remplissage = 100 in
  let nbhach = 20 in
  let nbtest = 100 in

  let rep2g = ref 0 in
  let rep2f = ref 0 in
  let nbtot = ref 0 in
  let rep2gm = ref 0 in
  let rep2fm = ref 0 in

  let nbfp = ref 0 in
  let nbfpm = ref 0 in

  for i = 0 to (nbtest -1) do

    HashName.init ();
(*    let hasharray = Array.make nbhach (hash_multi 320 0.12345 3) in*)
    let theta_tbl = Array.make nbhach 0. in
    for i = 0 to (nbhach-1) do
      let f=  0.00001 +. HashName.float (0.99998) in
      theta_tbl.(i) <- f;
    done;
  
    let s = Array.make remplissage ("") in
    for i = 0 to (remplissage -1) do 
      s.(i) <- HashName.newname 160;
    done;

    let init = Array.make nbhach (to_string_size 40 0) in
    for i = 0 to (nbhach-1) do
      init.(i) <- to_string_size 40 0
    done;
    let bf = ref init in
    let bf2 = ref init in

    for i = 0 to (remplissage -1) do
      bf := build_next_bf_s (apply_hash_factor 320 2 theta_tbl) ([!bf]) (s.(i)) nbhach;
      bf2 := build_next_bf_s (hash_magnus 320 2) ([!bf2]) s.(i) nbhach
    done;

    for i = 0 to (remplissage -1) do
      let b1 = test_belong_s (apply_hash_factor 320 2 theta_tbl) (s.(i)) (!bf) false in
      if (not b1) then 
	incr nbfp;
      let b2 = test_belong_s (hash_magnus 320 2) (s.(i)) (!bf2) false in
      if (not b2) then
	incr nbfpm
    done;

 
    for i = (remplissage) to (10*remplissage -1) do
      let b1 = test_belong_s (apply_hash_factor 320 2 theta_tbl) (HashName.newname 160) (!bf) false in
      incr nbtot;
      if b1 then 
	incr rep2g
      else
	incr rep2f;
      let b2 = test_belong_s (hash_magnus 320 2) (HashName.newname 160) (!bf2) false in
      if b2 then 
	incr rep2gm
      else
	incr rep2fm;
      
    done;
    Printf.printf "[1] %d : %d/%d\n" i (!rep2g) (!nbtot);
    Printf.printf "[2] %d : %d/%d\n" i (!rep2gm) (!nbtot);
  done;
  let rep2gf = float_of_int (!rep2g) in
  let rep2ff = float_of_int (!rep2f) in
  let nbtotf = float_of_int (!nbtot) in
  let rep2gmf = float_of_int (!rep2gm) in
  let rep2fmf = float_of_int (!rep2fm) in
  Printf.printf "[RESULTAT] nb_test_tot : %d\n" (!nbtot);
  Printf.printf "[RESULTAT] [1] nbfp : %.6e === nbgd : %6.e\n" (rep2gf/.nbtotf) (rep2ff/.nbtotf);
  Printf.printf "[RESULTAT] [2] nbfp : %.6e === nbgd : %6.e\n" (rep2gmf/.nbtotf) (rep2fmf/.nbtotf);
  Printf.printf "[RESULTAT] [1] fp : %d === [2] fp : %d\n" (!nbfp) (!nbfpm);
  end;;





(*
let main () = 
  let testing_repartition = false in
  let test_bf = false in
  let testing_ancestors = true in
  let measuring_bf = false in
  let testing_bf = true in
  let f_hach = true in (*true -> factor , false -> magnus*)
  let nb_hach = 20 in
  let nb_test_repart = 10000000 in
  let theta_tbl = Array.make nb_hach (0.) in
  for i = 0 to (nb_hach -1) do
    theta_tbl.(i) <- 0.00001+. HashName.float (0.99999);
    Printf.printf "%f - " theta_tbl.(i);
  done;
  Printf.printf "\n";
  
  let hash_fun = (if f_hach then apply_hash_factor 320 2 theta_tbl else hash_magnus 320 2) in
  let size_graphe = 20 in 
  let prof_max = 15 in 
  let nb_test = string_of_int (11) in
  let g,tete = get_exemple () in
(*alea size_graphe prof_max 8 0.5 in*)
  let file = open_out_bin ("./debug/main.dot") in
  ToDot.init ();
  Dot.output_graph file g;
  let a,b = simule2 (hash_fun) g tete nb_hach 5 in
  Printf.printf "Simulation Done\n";
  flush stdout;
  let name0 = "test_simule/test_simule"^(nb_test)^"/graphe_main.dot" in
  print_graphe name0 g;

  if testing_repartition then
    begin

      let test_repart_a = Array.make 320 0 in
      let test_repart_b = Array.make 320 0 in
      for i = 0 to (nb_test_repart-1) do
	HashName.init ();
	let a = HashName.newname 160 in
	let ma,mb = get_a_b a 320 in
	if (i mod 100 = 0) then (Printf.printf "%d a = %d\t b = %d\n" i ma mb);
	flush stdout;
	test_repart_a.(ma) <- test_repart_a.(ma)+1;
	test_repart_b.(mb) <- test_repart_b.(mb)+1;
      done;
      let cout1 = open_out "reparta_magnus" in
      let cout2 = open_out "repartb_magnus" in
      for i=0 to (319) do
	Printf.fprintf cout1 "%d %d\n" i test_repart_a.(i);
	Printf.fprintf cout2 "%d %d\n" i test_repart_b.(i);
      done;
      close_out cout1;
      close_out cout2;
      
    end
  ;
  if testing_ancestors then
    begin
      Printf.printf "=====Starting to test Ancestors=====\n";
      let rep = Hashtbl.create 10 in

      let nb = ref 0 in
      let iter_on_graph a = 
	Printf.printf "[BUILDING ANCESTORS] %d/%d %s\n" (!nb) size_graphe a;
	let ma,mb = get_a_b a 320 in
	Printf.printf "a = %d\t b = %d\n" ma mb;
	flush stdout;

	incr nb;
	Hashtbl.add rep a (ancetre g a) 
      in
      MyGraph.iter_vertex iter_on_graph g;
      nb := 0;
      let repbool = ref true in
      let test_egal k v = 
	Printf.printf "[CHECKING ANCESTORS] %d/%d %s\n" (!nb) size_graphe k;
	flush stdout;
	incr nb;
	repbool := ((!repbool) && (egale v (Hashtbl.find b k))) 
      in
      Hashtbl.iter (test_egal) rep;
      Printf.printf "Test Ancetre : %s\n" (if (!repbool) then "[OK]" else "[FAIL]");
      flush stdout;
      if testing_bf then 
	begin

	  Printf.printf "=====Starting to test Bloomfilters=====\n";
	  let fpstat = ref [] in
	  let nbfp = ref 0 in
	  let nbfn = ref 0 in
	  let nbgood = ref 0 in
	  let nb1 = ref 0 in
	  
	  let to_iter_test_bf node = 
	    Printf.printf "Test bf %d\n" (!nb1);
	    flush stdout;
	    incr nb1;
	    let ancetre = Hashtbl.find rep node in
	    let bf_l = Hashtbl.find a node in    
	    let to_iter_on_others b =
	      let is_in_really = MyGraph.mem_vertex ancetre b in
	      let is_in_bf = is_in_one_of_bf (hash_fun) b bf_l 0 in
	      if (is_in_bf == -1) then 
		begin 
		  if (not is_in_really) then 
		    incr nbgood
		  else 
		    incr nbfn
		end
	      else 
		begin
		  if (not is_in_really) then
		    begin
		      incr nbfp;
		      fpstat := (is_in_bf :: !fpstat);
		    end
		  else
		    incr nbgood
		end
	      ;
	    in
	    MyGraph.iter_vertex (to_iter_on_others) g;
	  in
	  MyGraph.iter_vertex (to_iter_test_bf) g;
	  let tot = float_of_int (!nbfp + !nbfn + !nbgood) in
	  let ffp = float_of_int (!nbfp) in
	  let ffn = float_of_int (!nbfn) in
	  let fgood = float_of_int (!nbgood) in
	  Printf.printf "RESULTAT : nbfp = %.6e - nbfn = %.6e - nbgood = %.6e - tot = %f\n" (ffp/.tot) (ffn/.tot) (fgood/.tot) tot;
	  let maxl = max_l (!fpstat) in
	  if (maxl >= 0) then 
	    begin
	      let stat_prof = Array.make (maxl +1) 0 in
	      let rec vide l = match l with
		|p::q -> stat_prof.(p) <- stat_prof.(p) +1 ; vide q
		|[] -> ()
	      in
	      vide (!fpstat);
	      for i = 0 to maxl do
		Printf.printf "%d %d\n" i (stat_prof.(i))
	      done;
	    end
	end;
    end;
  if measuring_bf then
    begin
      Printf.printf "=====Starting to measure bloomfilters=====\n";
      (*etude du nombre de bit et du max size en fonction de la profondeur*)
      let prof = Hashtbl.create 10 in
      
      let rec parcours_prof i node = 
	if  Hashtbl.mem (prof) node then 
	  ()
	else
	  begin
	    
	    Printf.printf "[PROFONDEUR COMPUTING] : %d\n" i;
	    flush stdout;
	    Hashtbl.add (prof) node i;
	    MyGraph.iter_succ (parcours_prof (i+1)) g node
	  end
      in
      parcours_prof 0 tete;
      
      Printf.printf "[PROFONDEUR COMPUTED]\n";
      flush stdout;
      let measure_bf_table = Hashtbl.create 10 in (*int -> (float array * float array)*)
      let measure_bf node = 
	let bf_l = Hashtbl.find a node in
	let prof_node = Hashtbl.find prof node in
	let a_ms,a_nb_bit = stat_bf bf_l in
	Hashtbl.add measure_bf_table (prof_node) (a_ms,a_nb_bit);
      in
      MyGraph.iter_vertex measure_bf g;
      
      Printf.printf "[MEASURE DONE]\n";
      flush stdout;
      let moyenne prof = 
	let (l : (float array * float array) list ) = Hashtbl.find_all measure_bf_table prof in
	if (l = []) then (Printf.printf "Empty list%d\n" prof);
	Hashtbl.replace measure_bf_table prof (average l);
      in
      for i =0 to (prof_max-1) do
	moyenne i
      done;
      Printf.printf "[AVERAGE COMPUTED]\n";
      flush stdout;
      let nb_bf_max = ref 0 in
      let to_iter_on_prof k value = 
	let n = Array.length (fst value) in
	if (n > !nb_bf_max) then (nb_bf_max := n);
      in
      Hashtbl.iter (to_iter_on_prof) measure_bf_table;
      let n = !nb_bf_max in 
      Printf.printf "[NB MAX] : %d\n" n;
      let cout_a_ms = Array.make n (stdout) in
      let cout_a_nb_bit = Array.make n (stdout) in
      for i = 0 to (n-1) do
	cout_a_ms.(i) <- open_out ("test_simule/test_simule"^(nb_test)^"/max_size_"^(string_of_int i));
	cout_a_nb_bit.(i) <- open_out ("test_simule/test_simule"^(nb_test)^"/nb_bit_"^(string_of_int i));
      done;

      for i = 0 to (prof_max -1 ) do
	let a,b = Hashtbl.find measure_bf_table i in
	let n = Array.length a in
	for j= 0 to (n-1) do
	  Printf.fprintf (cout_a_ms.(j)) "%d %f\n" i a.(j);
	  Printf.fprintf (cout_a_nb_bit.(j)) "%d %f\n" i b.(j);
	done
      done;
      
      Printf.printf "[PRINTING FINISHED]\n";
      flush stdout;
    end;


  
  (*
    let to_iter_bf key value = 
    let cout = open_out ("test_simule/test_simule"^(nb_test)^"/bf_"^key) in
    print_bf_l cout value;
    close_out cout;
    in
    let to_iter_ancestor key value = 
    let name = "test_simule/test_simule"^(nb_test)^"/graphe_"^key^".dot" in
    print_graphe name value
    in
    Hashtbl.iter to_iter_bf a;
    Hashtbl.iter to_iter_ancestor b;

  *)
  
  Printf.printf "End\n";


(*petit test*)
(*
  let cout = open_out "etudeproba/640_2_k_20" in
  for k = 0 to 1000 do
  let res = prob 640 2 k 15 in
  Printf.fprintf cout "%d %.6e\n" k res;
  done;
  close_out cout;
*)



(*test comparaison hash functions*)
if test_bf then
  begin
  let remplissage = 100 in
  let nbhach = 20 in
  let nbtest = 100 in

  let rep2g = ref 0 in
  let rep2f = ref 0 in
  let nbtot = ref 0 in
  let rep2gm = ref 0 in
  let rep2fm = ref 0 in

  let nbfp = ref 0 in
  let nbfpm = ref 0 in

  for i = 0 to (nbtest -1) do

    HashName.init ();
(*    let hasharray = Array.make nbhach (hash_multi 320 0.12345 3) in*)
    let theta_tbl = Array.make nbhach 0. in
    for i = 0 to (nbhach-1) do
      let f=  0.00001 +. HashName.float (0.99998) in
      theta_tbl.(i) <- f;
    done;
  
    let s = Array.make remplissage ("") in
    for i = 0 to (remplissage -1) do 
      s.(i) <- HashName.newname 160;
    done;

    let init = Array.make nbhach (to_string_size 40 0) in
    for i = 0 to (nbhach-1) do
      init.(i) <- to_string_size 40 0
    done;
    let bf = ref init in
    let bf2 = ref init in

    for i = 0 to (remplissage -1) do
      bf := build_next_bf_s (apply_hash_factor 320 2 theta_tbl) ([!bf]) (s.(i)) nbhach;
      bf2 := build_next_bf_s (hash_magnus 320 2) ([!bf2]) s.(i) nbhach
    done;

    for i = 0 to (remplissage -1) do
      let b1 = test_belong_s (apply_hash_factor 320 2 theta_tbl) (s.(i)) (!bf) false in
      if (not b1) then 
	incr nbfp;
      let b2 = test_belong_s (hash_magnus 320 2) (s.(i)) (!bf2) false in
      if (not b2) then
	incr nbfpm
    done;

 
    for i = (remplissage) to (10*remplissage -1) do
      let b1 = test_belong_s (apply_hash_factor 320 2 theta_tbl) (HashName.newname 160) (!bf) false in
      incr nbtot;
      if b1 then 
	incr rep2g
      else
	incr rep2f;
      let b2 = test_belong_s (hash_magnus 320 2) (HashName.newname 160) (!bf2) false in
      if b2 then 
	incr rep2gm
      else
	incr rep2fm;
      
    done;
    Printf.printf "[1] %d : %d/%d\n" i (!rep2g) (!nbtot);
    Printf.printf "[2] %d : %d/%d\n" i (!rep2gm) (!nbtot);
  done;
  let rep2gf = float_of_int (!rep2g) in
  let rep2ff = float_of_int (!rep2f) in
  let nbtotf = float_of_int (!nbtot) in
  let rep2gmf = float_of_int (!rep2gm) in
  let rep2fmf = float_of_int (!rep2fm) in
  Printf.printf "[RESULTAT] nb_test_tot : %d\n" (!nbtot);
  Printf.printf "[RESULTAT] [1] nbfp : %.6e === nbgd : %6.e\n" (rep2gf/.nbtotf) (rep2ff/.nbtotf);
  Printf.printf "[RESULTAT] [2] nbfp : %.6e === nbgd : %6.e\n" (rep2gmf/.nbtotf) (rep2fmf/.nbtotf);
  Printf.printf "[RESULTAT] [1] fp : %d === [2] fp : %d\n" (!nbfp) (!nbfpm);
  end;;
  (*
  (*TEST MAGNUS*)
  for i = 0 to (remplissage -1) do
 
  done;
  let rep1g = ref 0 in
  let rep1f = ref 0 in
  for i = 0 to (remplissage -1) do
  
  if b then 
  incr rep1g
  else
  incr rep1f;
  done;
  let rf = float_of_int remplissage in
  Printf.printf "Good : %f\tFalse negative :%f\n" ((float_of_int (!rep1g))/. rf) ((float_of_int (!rep1f))/. rf);
  Printf.printf "===================\n";
  Printf.printf "|TESTING WRONG ONE|\n";
  Printf.printf "===================\n";
  
  let rep2g = ref 0 in
  let rep2f = ref 0 in

  for i = (remplissage) to (2*remplissage -1) do
  let b = test_belong_s (hash_magnus 320 2) (HashName.newname 160) (!bf2) false in

  if b then 
  incr rep2g
  else
  incr rep2f
  done;
  let dt2 = Unix.time () -. t02 in
  let dt2s = Sys.time () -. t02s in
  Printf.printf "Good : %f\tFalse positive :%f\n" ((float_of_int (!rep2f))/. rf) ((float_of_int (!rep2g))/. rf); 
  Printf.printf "[UNIX]\nTime normal : %f\nTime magnus : %f\n" dt1 dt2;
  Printf.printf "[SYST]\nTime normal : %f\nTime magnus : %f\n" dt1s dt2s;

  end;;

  *)
(*
  let sh1 = sha1 () in
  let s1 = "Hello" in
  let s2 = "World" in
  Printf.fprintf stdout "%s -> %s\n" s1 (binaire_string s1);
  Printf.fprintf stdout "%s -> %s\n" s2 (binaire_string s2);
  add s1 s2;
  Printf.fprintf stdout "%s -> %s\n" s2 (binaire_string s2);
*)

let f1 = (1. -. ((318.)/.(320.))**(200.)) in
let f = (1. -. ((318.)/.(320.))**(200.))** (40.)*. 500. *. 500. in
Printf.printf "%.6e\n" f1;
Printf.printf "%.6e\n" f;;


let gtest = MyGraph.create () ;;
MyGraph.add_vertex gtest "0";
MyGraph.add_vertex gtest "1";
MyGraph.add_vertex gtest "2";
MyGraph.add_vertex gtest "3";
MyGraph.add_vertex gtest "4";
MyGraph.add_vertex gtest "5";
MyGraph.add_vertex gtest "6";
MyGraph.add_edge gtest "0" "4";
MyGraph.add_edge gtest "1" "4";
MyGraph.add_edge gtest "2" "5";
MyGraph.add_edge gtest "3" "5";
MyGraph.add_edge gtest "4" "6";
MyGraph.add_edge gtest "5" "6";;

iter_graphe_from_high (fun x -> Printf.printf "%s\n" x) gtest "6" false;;



*)

(*main ();;*)



let main2 () =
  let string_test = "0123456789abcdef" in
  let binaire = hexa_to_binaire string_test in
  let retour = binaire_to_hexa binaire in
  Printf.printf "%s\n" string_test;
  Printf.printf "%s\n" binaire;
  Printf.printf "%s\n" retour;
(*
  let g = MyParsor.parse "./testdot/foopgl.dot" in
  MyGraph.remove_vertex g "r";
  print_graph g;
  Printf.printf "parsor ok\n";
  let file = open_out_bin ("./testdot/foopglmod.dot") in
  ToDot.init ();
  MyDot.output_graph file g*)
;;

main ();;
