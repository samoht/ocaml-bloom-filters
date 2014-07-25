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
module Truc = Mergetools.Make(MyGraph)(Bf2)

module ToSet = 
struct
  type t = string
  let equal = (=)
end
let is_char_in_string_n m c s =
  let n = String.length s in
  let i = ref 0 in
  let j = ref 0 in
  while (!i < n && !j < m) do (if (s.[!i] = c) then incr j ; incr i) done;
  (!j = m)
;;
let hexa_to_binaire_char c s i = match c with
  |'0' -> s.[i] <- '0';s.[i+1] <- '0';s.[i+2] <-'0';s.[i+3] <- '0' 
  |'1' -> s.[i] <- '0';s.[i+1] <- '0';s.[i+2] <-'0';s.[i+3] <- '1' 
  |'2' -> s.[i] <- '0';s.[i+1] <- '0';s.[i+2] <-'1';s.[i+3] <- '0' 
  |'3' -> s.[i] <- '0';s.[i+1] <- '0';s.[i+2] <-'1';s.[i+3] <- '1' 
  |'4' -> s.[i] <- '0';s.[i+1] <- '1';s.[i+2] <-'0';s.[i+3] <- '0' 
  |'5' -> s.[i] <- '0';s.[i+1] <- '1';s.[i+2] <-'0';s.[i+3] <- '1' 
  |'6' -> s.[i] <- '0';s.[i+1] <- '1';s.[i+2] <-'1';s.[i+3] <- '0' 
  |'7' -> s.[i] <- '0';s.[i+1] <- '1';s.[i+2] <-'1';s.[i+3] <- '1' 
  |'8' -> s.[i] <- '1';s.[i+1] <- '0';s.[i+2] <-'0';s.[i+3] <- '0' 
  |'9' -> s.[i] <- '1';s.[i+1] <- '0';s.[i+2] <-'0';s.[i+3] <- '1' 
  |'a' -> s.[i] <- '1';s.[i+1] <- '0';s.[i+2] <-'1';s.[i+3] <- '0' 
  |'b' -> s.[i] <- '1';s.[i+1] <- '0';s.[i+2] <-'1';s.[i+3] <- '1' 
  |'c' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'0';s.[i+3] <- '0' 
  |'d' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'0';s.[i+3] <- '1' 
  |'e' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'1';s.[i+3] <- '0' 
  |'f' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'1';s.[i+3] <- '1' 
  |'A' -> s.[i] <- '1';s.[i+1] <- '0';s.[i+2] <-'1';s.[i+3] <- '0' 
  |'B' -> s.[i] <- '1';s.[i+1] <- '0';s.[i+2] <-'1';s.[i+3] <- '1' 
  |'C' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'0';s.[i+3] <- '0' 
  |'D' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'0';s.[i+3] <- '1' 
  |'E' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'1';s.[i+3] <- '0' 
  |'F' -> s.[i] <- '1';s.[i+1] <- '1';s.[i+2] <-'1';s.[i+3] <- '1' 
  |_ -> Printf.printf "char : %c" c ;failwith "pas de l'hexa"
;;
let int_to_hexa_c i = 
  if (i < 10) then
    char_of_int (48 + i)
  else
    char_of_int (97 + i - 10)
;;

let nb_of_bin s i l =
  let rep = ref 0 in
  let compt = ref 1 in
  for j = (i+l-1) downto i do
    if (s.[j] = '1') then (rep := !rep + !compt);
    compt := 2 * !compt
  done;
  !rep
;;

let hexa_to_binaire s = 
  let n = String.length s in
  let rep = String.make (4*n) '0' in
  for i = 0 to (n-1) do
    hexa_to_binaire_char (s.[i]) rep (4*i)
  done;
  rep;;

let binaire_to_hexa s = 
  let n = String.length s in
  let p = (n/4) in
  let m = if (n mod 4 <> 0) then (failwith "pas un multiple de 4") else p in
  let rep = String.make m '0' in
  for i = 0 to (m-1) do
    rep.[i] <- int_to_hexa_c (nb_of_bin s (4*i) 4)
  done;
  rep;;

module L = struct
  open Graph
  let node (a : Dot_ast.node_id) (b : Dot_ast.attr list) =
    let tokeep = ref false in
    let deal_one elem = 
      let e,f = elem in
      match e with
      |Dot_ast.Ident(s) -> 
	begin
	  match f with
	  |Some(sthg) -> 
	    begin
	      match sthg with
	      |Dot_ast.Ident(s) -> ()
	      |Dot_ast.Number(s) -> ()
	      |Dot_ast.String(s) -> if (is_char_in_string_n 3 '|' s) then (tokeep := true)
	      |Dot_ast.Html(s) -> ()
	    end
	  |None -> ()
	end
       
      |Dot_ast.Number(s) -> ()
      |Dot_ast.String(s) -> ()
      |Dot_ast.Html(s) -> ()
    in
    let deal_one_l l = 
      List.iter deal_one l
    in
    List.iter deal_one_l b;
    if (not (!tokeep)) then "r" else 
      begin
	let c,d = a in
	match c with
	|Dot_ast.Ident(s) -> hexa_to_binaire s
	|Dot_ast.Number(s) -> hexa_to_binaire s
	|Dot_ast.String(s) -> hexa_to_binaire s
	|Dot_ast.Html(s) -> hexa_to_binaire s
      end

  let edge l = ()
end
module Buildtool = struct 
  module G = MyGraph
  let empty = MyGraph.create ~size:10
  let copy = MyGraph.copy
  let add_vertex a b = MyGraph.add_vertex a b ; a
  let add_edge a b c = MyGraph.add_edge a b c ; a
  let add_edge_e a b = MyGraph.add_edge_e a b ; a
  let remove_vertex a b = MyGraph.remove_vertex a b ; a
  let remove_edge a b c = MyGraph.remove_edge a b c ; a
  let remove_edge_e a b = MyGraph.remove_edge_e a b ; a 
end

module MyParsor = Graph.Dot.Parse(Buildtool)(L);;

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
module ToDot = 
struct
   include MyGraph 
   let edge_attributes (a, b) = []
   let default_edge_attributes _ = []
   let get_subgraph _ = None
   let vertex_attributes v = 
     if ((binaire_to_hexa v) <> "c2c6803c67bf13018c08a1854ca95a2e8511f1372") then [`Shape `Box]
     else (Printf.printf "FOUND" ; [`Fillcolor(125);`Shape `Circle])
   let vertex_name v =
     if (String.length v mod 4 = 0) then
       binaire_to_hexa v
     else
       v
   let default_vertex_attributes _ = []
  let graph_attributes _ = []
end;;

module MyDot = Graph.Graphviz.Dot(ToDot);;

let simule2 g beg =
  let left_before = Hashtbl.create 10 in
  let tovisite = ref [beg] in
  let visited = Hashtbl.create 10 in
  let bf_merge_aux = ref "" in
  let moyenne = ref 0 in
  let nb_tot = ref 0 in
  let truenb = ref 0 in
  let visite node = 
    incr truenb;
    Printf.printf "%d visiting %s\n" (!truenb) (binaire_to_hexa node);
    let peres = MyGraph.pred g node in
    if (peres <> [])  then 
      begin
	let p::q = peres in
	let state_fin = ref (Database.fstate p) in
	let rec width l = match l with
	  |p::q -> 
	    begin
	      incr nb_tot;
	      let newst,nb_turn = Truc.increase_width (!state_fin) Database.f p in
	      state_fin := newst;
	      moyenne := !moyenne + nb_turn;
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
  done;
  (float_of_int !moyenne) /. (float_of_int !nb_tot)
;;
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


let iter_graphe_from_high f g start =
  let visited_up = Hashtbl.create 10 in
  let to_visite = ref [] in
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

let main () = 
  let size_graphe = 1000 in 
  let prof_max = 800 in 
  let nb_test = "100" in
  let g,hd = DagGen.alea size_graphe prof_max 160 0 0.5 in
  let n = simule2 g hd in
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

let main0 () = 
  let g = MyParsor.parse "./testdot/foopgl.dot" in
  Printf.printf "Input OK\n";
  MyGraph.remove_vertex g "r";
  let tete = one_head g in
  Printf.printf "Removing useless state OK\n";

  Printf.printf "Finding an head OK\n";
  let file = open_out_bin ("test.dot") in
  MyDot.output_graph file g;
  let f = simule2 g tete in
  Printf.printf "%f\n" f;
  let nb = ref 0 in
  let state_h = Database.known in
  let rep = Hashtbl.create 10 in
  let iter_on_graph a = 
    Printf.printf "[BUILDING ANCESTORS] %d/%d %s\n" (!nb) 1000 a;
    incr nb;
    Hashtbl.add rep a (ancetre g a) 
  in
  
  MyGraph.iter_vertex iter_on_graph g;
  nb:= 0;
  let repbool = ref true in
  let test_egal k v = 
    Printf.printf "[CHECKING ANCESTORS] %d/%d %s\n" (!nb) 1000 k;
    flush stdout;
    incr nb;
    let test = egale v (Truc.get_ancestor (Hashtbl.find state_h k)) in
    if (not test) then (Printf.printf "[CHECKING FAILED] %s\n" k);
    repbool := ((!repbool) && test) 
  in
  let test_egal2 k =
    Printf.printf "[CHECKING ANCESTORS] %d/%d %s\n" (!nb) 1000 (binaire_to_hexa k);
    flush stdout;
    incr nb;
    let test = egale (Hashtbl.find rep k) (Truc.get_ancestor (Hashtbl.find state_h k)) in
    if (not test) then (
      let file = open_out_bin ("true.dot") in
      MyDot.output_graph file (Hashtbl.find rep k);

      let file2 = open_out_bin ("false.dot") in
      MyDot.output_graph file2 (Truc.get_ancestor (Hashtbl.find state_h k));
      Printf.printf "[CHECKING FAILED] %s\n" k;
      failwith "failed";
    );
    repbool := ((!repbool) && test) 
  in
  (*Hashtbl.iter (test_egal) rep;*)
  iter_graphe_from_high (test_egal2) g tete;
  Printf.printf "Test Ancetre : %s\n" (if (!repbool) then "[OK]" else "[FAIL]");
  flush stdout;;

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

(*main3 ();;*)
let compute_old_bf g n=
  let rep = Hashtbl.create 10 in
  let visite_one node = 
    let visited = Hashtbl.create 10 in
    let rec visite_up node arr =
      if (Hashtbl.mem visited node) then
	()
      else
	begin
	  Hashtbl.add visited node true;
	  for i = 0 to (n-1) do 
	    if (node.[i] = '1') then arr.(i) <- arr.(i) +1
	  done;
	  MyGraph.iter_pred (fun x -> visite_up x arr) g node
	end
    in
    let rep = Array.make n 0 in
    visite_up node (rep);
    rep
  in
  let add_one node =
    Hashtbl.add rep node (visite_one node)
  in
  MyGraph.iter_vertex add_one g;
  rep;;
      
      
let compute_bca g a b =
  let hta = Hashtbl.create 10 in
  let visiteda = Hashtbl.create 10 in
  let rec visite_a node = 
    if (Hashtbl.mem visiteda node) then
      ()
    else 
      begin
	Hashtbl.add visiteda node true;
	MyGraph.iter_pred visite_a g node
      end
  in
  visite_a a;
  let visitedb = Hashtbl.create 10 in
  let nb_bca = ref 0 in
  let rec visite_b node = 
    if (Hashtbl.mem visitedb node) then
      ()
    else
      begin
	Hashtbl.add visitedb node true;
	if (Hashtbl.mem visiteda node) then
	  nb_bca := !nb_bca +1
	else 
	  MyGraph.iter_pred visite_b g node; 
      end
  in
  visite_b b;
  !nb_bca;;
let is_under a b n= 
  let i = ref 0 in
  while (!i < n && a.(!i) <= b.(!i)) do (incr i) done;
  (!i = n);;

let find_under min h =
  let rep = ref 0 in
  let deal_with_one key value =
    if (is_under value min 160) then (incr rep)
  in
  Hashtbl.iter deal_with_one h;
  !rep;;

let compute_min repa repb n =
  let rep = Array.make n 0 in
  for i = 0 to (n-1) do
    rep.(i) <- min (repa.(i)) (repb.(i))
  done;
  rep;;

let main4 () =
  
  for k = 1 to 8 do
  
    (*let coutbca = open_out ("resultprem/bca"^(string_of_int k)) in*)
    let coutnum = open_out ("resultprem/num"^(string_of_int k)) in
    for p = 1 to 10 do
      let g,b = DagGen.alea 100 (k*10) 160 0 ((float_of_int p)/.10.) in
      let htbl = compute_old_bf g 160 in
      let num = ref 0 in
      (*let nbc = ref 0 in*)
      let compt = ref 0 in
      let deal_with_couple a b =
	if (!compt mod 100 = 0) then (Printf.printf "[Computing BCA and NUM] %d/100 \n" (!compt/100); flush stdout;);
	incr compt;
	let m = compute_min (Hashtbl.find htbl a) (Hashtbl.find htbl b) 160 in
	let nb_under_min = find_under m htbl in
	(*let nb_bca= compute_bca g a b in*)
	num := !num + nb_under_min;
	(*nbc := !nbc + nb_bca;*)
      in
      MyGraph.iter_vertex (fun x -> (MyGraph.iter_vertex (fun y -> deal_with_couple x y) g)) g;
      Printf.printf "%d %d\n" k p;
      (*Printf.fprintf coutbca "%f %f\n" (float_of_int p /. 10.) (float_of_int (!nbc) /. 10000.);*)
      Printf.fprintf coutnum "%f %f\n" (float_of_int p /. 10.) (float_of_int (!num) /. 10000.);
    done;
    (*close_out coutbca;*)
    close_out coutnum;
  done;;

main4 ();;
    
