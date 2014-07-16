module Comparable : Graph.Sig.COMPARABLE with type t = string = struct
  type t = string
  let compare = Pervasives.compare
  let hash a = 
    let n = String.length a in
    let modu = ref 1 in
    let rep = ref 0 in
    for i = 0 to (n-1) do
      if (a.[i] = '1') then (rep := !rep + !modu);
      modu := 2* !modu
    done;
    !rep
  let equal = (=)
end;;

module MyGraph = Graph.Imperative.Digraph.ConcreteBidirectional(Comparable);;
module Bf = Bloomfilter.Make(Hash.Hash_magnus);;
module Bf2 = Bloomfilter.Make(Hash.Hash_multi);;

module DagGen = Alea.Make(MyGraph)(Alea.StringElem)
module Truc = Mergetools.Make(MyGraph)(Bf)

module ToSet = 
struct
  type t = string
  let equal = (=)
end


let rec remove e l = match l with
  |p::q -> if (e = p) then q else (p::(remove e q))
  |[] -> []
;;

let rec get_l i l accu= match l with
  |p::q -> (if i = 0 then (p,(accu@q)) else get_l (i-1) q (p::accu))
  |[] -> failwith "i too big"
;;

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

module Database =
struct
  let known = (let rep = Hashtbl.create 10 in Hashtbl.add rep "" (Truc.empty_state ()); rep)
  let add k v = Hashtbl.add known k v
  let f bf bd l=
    let rec ancl l accu = match l with
      |p::q -> ancl q ((Truc.get_ancestor (Hashtbl.find known p))::accu)
      |[] -> (List.rev accu)
    in
    let anl = ancl l [] in
    let a,b = Truc.next_ring l anl bf bd in
    b,a
  let fstate node = Hashtbl.find known node
  let astate node state = Hashtbl.add known node state
end


let rec split l a1 a2 = match l with
  |(a,b)::q ->  split q (a::a1) (b::a2)
  |[] -> (a1,a2)
;;


let simule2 g beg =
  let left_before = Hashtbl.create 10 in
  let tovisite = ref [beg] in
  let visited = Hashtbl.create 10 in
  let bf_merge_aux = ref "" in

  let visite node = 
    let peres = MyGraph.pred g node in
    if (peres <> [])  then 
      begin
	let p::q = peres in
	let state_fin = ref (Database.fstate p) in
	let rec width l = match l with
	  |p::q -> 
	    begin
	      state_fin := Truc.increase_width (!state_fin) Database.f p;
	      width q
	    end
	  |[] -> state_fin := Truc.increase_high (!state_fin) peres node
	in
	width q;
	Database.astate node (!state_fin)
      end
    else
      begin
	let state_fin = Truc.increase_high (Truc.empty_state ()) [] node in
	Database.astate node (state_fin)
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
  done;;
(*
let simule g beg =

(* STAT SUR LES ENVOIS*)
  let nb_envoi = ref 0 in
  let nb_envoi_bf = ref 0 in
  let nb_graph = ref 0 in
  let dif_cum = ref 0 in

  let state_h = Hashtbl.create 10 in

  let bf_l = Hashtbl.create 10 in
  let ancetre = Hashtbl.create 10 in
  let border_l = Hashtbl.create 10 in

  let left_before = Hashtbl.create 10 in
  let tovisite = ref [beg] in
  let visited = Hashtbl.create 10 in
  let bf_merge_aux = ref "" in
  Hashtbl.add bf_l "" [];
  Hashtbl.add border_l "" [];
  Hashtbl.add (state_h) "" (Truc.empty_state ());
  let visite node = 
    let debug = "0000101000101010101001011000100111110000111101110100010000100010011110111111100010110110100101111101000101011001010110100101111010101101001011110111010001000110" = node in
    Printf.printf "Visiting Node %s\n" node;
    let peres = MyGraph.pred g node in
    let added_node_l = ref [] in
    let graph_rep = ref (MyGraph.empty ()) in
    if (peres <> [])  then 
      begin
	let want_to_merge,to_merge = get_l (Random.int (List.length peres)) peres [] in
	bf_merge_aux := want_to_merge;
	let glist = ref [] in
	let deal_with_one_thread node_par =
	  incr nb_envoi;
	  let state = Hashtbl.find state_h want_to_merge in
	  let bf = ref (state.Truc.bf) in
	  let border_l_1,border_l_2 = split (state.Truc.border) [] [] in
	  let border_l_ref = ref (border_l_2) in
	  let border =  Bf.build_union (border_l_2) in
	  let g_loc = MyGraph.empty () in

(*	  let bf = ref (Hashtbl.find bf_l want_to_merge) in
	  let border_l_1,border_l_2 = split (Hashtbl.find border_l want_to_merge) [] [] in
	  let border_l_ref = ref (border_l_2) in
	  let border =  Bf.build_union (border_l_2) in
	  let g_loc = MyGraph.empty () in *)
	  MyGraph.add_vertex g_loc node_par;
	  let node_of_interest = ref [node_par] in
	  while (!node_of_interest <> []) do
	    incr nb_envoi_bf;
	    match (!bf) with
	    |(a,p)::q -> 
	      begin
		bf := q;
		let graphe,nl =
		  match (!border_l_ref) with
		  |t::r -> 
		    begin
		      Truc.get_history (!node_of_interest) (Hashtbl.find state_h node_par) g_loc p border
		    end
		  |[] -> failwith "impossible";
		in
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
	List.iter (fun x -> Truc.iter_graphe_from_high f (snd x) (fst x)) !glist;

	let graph_sol = MyGraph.copy ((Hashtbl.find state_h want_to_merge).Truc.ancestor) in
	List.iter (fun x -> Truc.unif_graphe graph_sol (snd x)) !glist;
	
	MyGraph.add_vertex graph_sol node;
	if debug then (Printf.printf "Mark [1]\n";flush stdout);
	MyGraph.iter_pred (fun x -> MyGraph.add_edge graph_sol x node) g node;
	graph_rep := graph_sol
(*	Hashtbl.add ancetre node graph_sol;*)
      end
    else
      begin
	let graph_sol = MyGraph.empty () in
	MyGraph.add_vertex graph_sol node;
	graph_rep := graph_sol
(*	Hashtbl.add ancetre node graph_sol;*)
      end;
    let state = Hashtbl.find state_h (!bf_merge_aux) in
(*
    let (pere_bf_l : (int * string array) list) = Hashtbl.find bf_l (!bf_merge_aux) in
    let border_bf_l = Hashtbl.find border_l (!bf_merge_aux) in
*) 
    added_node_l := (node :: !added_node_l);
    added_node_l := List.rev (!added_node_l);
    let g_sol = !graph_rep in
    let statenew = Truc.add (!added_node_l) (state) (g_sol) in
    Hashtbl.add (state_h) node statenew;
   (*
    Hashtbl.add bf_l node bf_l_sol;
    Hashtbl.add border_l node border_l_sol;
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
  state_h, ((float_of_int (!dif_cum)) /. (float_of_int (!nb_graph))),(float_of_int (!nb_envoi_bf) /. float_of_int (!nb_envoi));;
*)
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

let rec is_in_one_of_bf node bf_l i = match bf_l with
  |p::q -> if (Bf.mem node (snd p)) then (i) else (is_in_one_of_bf node q (i+1))
  |[] -> (-1)
;;

let egale u v =
  (inclus u v) && (inclus v u);;
let max_l l = 
  let rep = ref min_int in
  let rec aux li = match li with
    |p::q -> if (p > !rep) then (rep := p ; aux q) else aux q
    |[] -> ()
  in
  aux l;
  !rep;;

let main () = 
  let size_graphe = 10000 in 
  let prof_max = 8000 in 
  let nb_test = "100" in
  let g,hd = DagGen.alea size_graphe prof_max 160 0 0.5 in
  let () = simule2 g hd in
  Hash.Hash_magnus.print_compte ();
  
  let state_h = Database.known in
  Printf.printf "=====Starting to test Acestors=====\n";
  let rep = Hashtbl.create 10 in
  
  let nb = ref 0 in
  let iter_on_graph a = 
    Printf.printf "[BUILDING ANCESTORS] %d/%d %s\n" (!nb) size_graphe a;
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
    let test = egale v (Truc.get_ancestor (Hashtbl.find state_h k)) in
    if (not test) then (Printf.printf "[CHECKING FAILED] %s\n" k);
    repbool := ((!repbool) && test) 
  in
  Hashtbl.iter (test_egal) rep;
  Printf.printf "Test Ancetre : %s\n" (if (!repbool) then "[OK]" else "[FAIL]");
  flush stdout;
      
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
    let bf_l = Truc.get_bf (Hashtbl.find (state_h) node) in
    let to_iter_on_others b =
      let is_in_really = MyGraph.mem_vertex ancetre b in
      let is_in_bf = is_in_one_of_bf b bf_l 0 in
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



  let string_to_binaire_mod s i l m =
    let compt =ref 1 in
    let rep = ref 0 in
    for j = i to (i+l-1) do
      if (s.[j] = '1') then (rep := (!rep + !compt) mod (max_int /100));
      compt := (2 * !compt) mod (max_int /100);
    done;
    !rep;;

let get_a_b s size = 
  let m = String.length s in
  let a = string_to_binaire_mod s 0 (m/2) (size) in
  let b = string_to_binaire_mod s (m/2) (m/2) (size) in
  a,b;;


let main2 () =
  
  Alea.HashName.init ();
  let remplis s = 
    let n = Array.length s in
    let m = 8 * (String.length s.(0)) in
    let rep = ref 0 in
    for i = 0 to (n-1) do
      let saux = binaire_string (s.(i)) in
      for j = 0 to (m-1) do
	if (saux.[j] = '1') then
	  incr rep
      done;
    done;
    (float_of_int (!rep))/.(float_of_int (n*m))
  in
  let store = ref (Hash.Hash_magnus.create ()) in
  let cout = open_out "./debug/hmag" in
  for i = 0 to 200 do
    let m = Alea.HashName.new_name 160 in
    store := (Bf.merge [!store] [m]);
    Printf.fprintf cout "%d %f\n" i (remplis (!store))
  done;
  store := (Hash.Hash_magnus.create ());
  let cout2 = open_out "./debug/hmult" in
  for i = 0 to 200 do
    let m = Alea.HashName.new_name 160 in
    store := (Bf2.merge [!store] [m]);
    Printf.fprintf cout2 "%d %f\n" i (remplis (!store))
  done;
  close_out cout2;
  close_out cout;
  let print_store s = 
    Printf.printf "=====STORE=====\n";
    let n = Array.length s in
    let m = 8 * (String.length s.(0)) in
    let rep = ref 0 in
    for i = 0 to (n-1) do
      let saux = binaire_string (s.(i)) in
      Printf.printf "%s\n" saux;
    done;
    
    (float_of_int (!rep))/.(float_of_int (n*m))
  in
  let storemag = ref (Hash.Hash_magnus.create ()) in
  let storemul = ref (Hash.Hash_magnus.create ()) in
  for i = 0 to 200 do
    let m = Alea.HashName.new_name 160 in

(*
    Printf.printf "%s\n" m;
    let a,b = get_a_b m 320 in
    Printf.printf "a : %d --- b : %d\n" a b;
*)
    storemag := (Bf.merge [!storemag] [m]);
    (*print_store (!storemag);*)
    storemul := (Bf2.merge [!storemul] [m]);
  done;
  let nbfailmag = ref 0 in
  let nbfailmul = ref 0 in
  let nbtest = 10000 in
  Printf.printf "\n";
  for i = 0 to nbtest do
    let m = Alea.HashName.new_name 160 in
    if (Bf.mem m (!storemag)) then (
      incr nbfailmag
    );
(*   Printf.printf "%s\n" m;incr nbfailmag;
      let a,b = get_a_b m 320 in
      Printf.printf "a : %d --- b : %d\n" a b
    );*)
    if (Bf2.mem m (!storemul)) then incr nbfailmul;
  done;
  let resmag = float_of_int (!nbfailmag) /. (float_of_int nbtest) in
  let resmul = float_of_int (!nbfailmul) /. (float_of_int nbtest) in
  Printf.printf "MAG : %f --- MUL : %f\n" resmag resmul
;;
(*main2();;*)

let prob m n k = 
  (1. -. (1. -. 1./.m) ** n) ** k;;

let main3 () =
  let cout = open_out "bf_res" in
  let placed = Hashtbl.create 10 in
  let storemul = ref (Hash.Hash_magnus.create ()) in
  let offset = 100 in
  let predo () = 
    for i = 0 to (offset -1) do
      let m = Alea.HashName.new_name 160 in
      Hashtbl.add placed (m) true;
      storemul := (Bf.merge [!storemul] [m]);
    done;
  in
  predo ();
  for i = 1 to 50 do
    for j = 0 to 9 do
      let m = Alea.HashName.new_name 160 in
      Hashtbl.add placed m true;
      storemul := (Bf.merge [!storemul] [m]);
    done;

    let nbfailmul = ref 0 in
    let nbtest = 100000 in
    Alea.HashName.init ();
    for i = 0 to nbtest do
      let m = ref (Alea.HashName.new_name 160) in
      let keep = ref (Hashtbl.mem placed (!m)) in
      while (!keep) do
	m := Alea.HashName.new_name 160;
	keep := Hashtbl.mem placed (!m);
      done;
      if (Bf.mem (!m) (!storemul)) then incr nbfailmul;
    done;
    let resmul = float_of_int (!nbfailmul) /. (float_of_int nbtest) in
    Printf.fprintf cout "%d %.5e %.5e\n" (offset + i * 10) resmul (prob (float_of_int 320) (float_of_int (offset + i*10)) (float_of_int 20));
    Printf.printf "%d %.5e %.5e\n" (offset + i * 10) resmul (prob (float_of_int 320) (float_of_int (offset + i*10)) (float_of_int 20))
  done;
  close_out cout;;

main3 ();;
