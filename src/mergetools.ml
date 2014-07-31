module type DataSig =
sig
  type t
  type u
  val name : t -> string
  val nb_max : int
  val merge : u list -> t list -> u
  val mem : t -> u -> bool
end
exception No_more_bf;;

module Compteur = 
struct
  let b1 = ref false
  let b2 = ref false
  let b3 = ref false
  let focus1 = ref (0)
  let focus2 = ref (0)
  let focus3 = ref (0)
  let l1 = ref []
  let l2 = ref [] 
  let l3 = ref [] 
  let database_compteur = Hashtbl.create 10
  let new_compteur s = Hashtbl.add database_compteur s (ref 0)
  let incr1 s =
    let b = Hashtbl.find database_compteur s in
    incr b
  let incrn s n = 
    let b = Hashtbl.find database_compteur s in
    b := !b + n
  let value s = 
    !(Hashtbl.find database_compteur s)
  let moyenne s n =
    (float_of_int !(Hashtbl.find database_compteur s)) /. (float_of_int n)
  let give_focus1 s =
    focus1 := value s
  let give_focus2 s =
    focus2 := value s
  let give_focus3 s =
    focus3 := value s
  let take_focus1 s =
    let b = Hashtbl.find database_compteur s in
    b := (!focus1)
  let take_focus2 s =
    let b = Hashtbl.find database_compteur s in
    b := (!focus2)
  let take_focus3 s =
    let b = Hashtbl.find database_compteur s in
    b := (!focus3)
  let incrf1 () = incr focus1
  let incrf2 () = incr focus2
  let incrf3 () = incr focus3
  let remove s = 
    Hashtbl.remove database_compteur s
end

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







module Make (B : Graph.Sig.I) (D : DataSig with type t = B.V.t)  =
struct
  type v = (int * D.u) list
  type t = {ancestor : B.t ; bf : v ; border : v}
  type retour = Some of (B.t) | None    
      
  let rec remove e l = match l with
    |p::q -> if (e = p) then q else (p::(remove e q))
    |[] -> []
  ;;    
  let empty_state () = {ancestor = B.create (); bf = [] ; border = []}
  let get_ancestor t = t.ancestor
  let get_bf t = t.bf
  let build_next_border bf parent_list current_border =
    let rep = ref (current_border) in
    let nb_added = ref 0 in
    let one_elem node = 
      if (D.mem node bf) then 
	()
      else
	begin
	  rep := D.merge [!rep] [node];
	  nb_added := !nb_added + 1
	end
    in
    List.iter one_elem parent_list;
    !nb_added,!rep;;
  let add nodel (state : t) g = 
    let rep = ref (state.bf) in
    let repf = ref (state.border) in
    let rec add_one l = match l with
      |p::q ->
	begin
	  match (!rep) with
	  |(nb,bf)::r -> 
	    begin
	      if (nb+1 > D.nb_max) then
		begin
		  let a = D.merge [] [p] in
		  rep := (1,a) :: (!rep);
		  let b = D.merge [] (B.pred g p) in
		  repf := (1,b) :: (!repf);
		  add_one q;
		end
	      else
		begin
		  let a = D.merge [bf] [p] in
		  rep := (nb+1,a) :: r;
		  begin
		    match (!repf) with
		    |[] -> failwith "empty border with non empty bf"
		    |(nb_border,border)::queue -> 
		      begin
			let n,b= build_next_border a (B.pred g p) (border) in
			repf := (nb_border +n, b)::queue
		      end;
		  end;
		  add_one q;
		end
	      end
	  |[] -> 
	    begin
	      rep := [1,D.merge [] [p]]; repf := [1,D.merge [] [p]]; add_one q
	    end
	end
      |[] -> ()
    in
    add_one nodel;
    {ancestor = g; bf = !rep; border = !repf}

  let next_ring node_list ancestor_list bf border = 
    let g = B.create () in
    let node_of_interest = ref [] in
    let in_border = ref [] in
    let in_bf = ref [] in
    let explored = Hashtbl.create 10 in
    let explored_down = Hashtbl.create 10 in
    
    let rec explore_one boul node ancetre= 
      if boul then
	begin
	  if (Hashtbl.mem explored node) then
	    ()
	  else 
	    begin
(*
	      Printf.printf "going up %s\n" (binaire_to_hexa (D.name node));
	      flush stdout;*)
	      if !Compteur.b3 then (Compteur.incrf3 ());
	      Hashtbl.add explored node true;
	      let is_in_bf = D.mem node bf in
	      if (is_in_bf) then 
		begin
		 (*
		  Printf.printf "going bf %s\n" (binaire_to_hexa (D.name node));
		  flush stdout;*) 
		  found_in_bf node ancetre;
		end
	      else
		  begin
		    let is_in_border = D.mem node border in
		    if (is_in_border) then 
		      begin
			(*
			Printf.printf "going bd %s\n" (binaire_to_hexa (D.name node));
			flush stdout;*)
			found_in_border node ancetre
		      end
	            else 
		      begin
			if (!Compteur.b1) then (Compteur.incrf1 ());
			B.iter_pred (fun x -> explore_one false x ancetre) (ancetre) node;
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
		if (B.mem_vertex g node) then 
		  ()
		else
		  begin
		    if (!Compteur.b3) then (Compteur.incrf3 ());
(*
		    Printf.printf "going up %s\n" (binaire_to_hexa (D.name node));
		    flush stdout;*)
		    Hashtbl.add explored node true;
		    let is_in_bf = D.mem node bf in
		    if (is_in_bf) then 
		      begin
		      (*
			Printf.printf "going bf %s\n" (binaire_to_hexa (D.name node));
			flush stdout;*)
			found_in_bf node ancetre
		      end
		    else
		      begin
			let is_in_border = D.mem node border in
			if (is_in_border) then 
			  begin
			    (*
			    Printf.printf "going bd %s\n" (binaire_to_hexa (D.name node));
			    flush stdout;*)
			    found_in_border node ancetre
			  end
			else 
			  begin
			    if (!Compteur.b1) then (Compteur.incrf1 ());
			    B.iter_pred (fun x -> explore_one false x ancetre) (ancetre) node;
			  end
		      end
		  end
	      end
	end
    and found_in_bf node ancetre = 
      in_bf := (node,ancetre) :: (!in_bf);
    and found_in_border node ancetre = 
      in_border := (node,ancetre) :: (!in_border);
    in
    let rec fst_rec a b = match a,b with
      |p::q,t::r -> explore_one true p t; fst_rec q r
      |[],[] -> ()
	|_-> failwith "pas le même nombre"
    in
    fst_rec node_list ancestor_list;
    
    let rec deal_with_bf node ancetre = 
      if Hashtbl.mem explored_down node then () else
	begin
	  if !Compteur.b3 then (Compteur.incrf3 ());
	  Hashtbl.add explored_down node true;
	  B.add_vertex g node;
	  let add_edges_with_son son = 
	    B.add_edge g node son
	  in
	  if !Compteur.b2 then (Compteur.incrf2 ());
	  let lson = B.succ ancetre node in
	  List.iter (fun x -> add_edges_with_son x) lson;
	  List.iter (fun x -> deal_with_bf x ancetre) lson;
	end
    in
    let mark_down = Hashtbl.create 10 in
      let rec deal_with_border (node) ancetre = 
	if Hashtbl.mem mark_down node then
	  ()
	else
	  begin
	    if !Compteur.b3 then (Compteur.incrf3 ());
	    Hashtbl.add mark_down node true;
	    if !Compteur.b2 then (Compteur.incrf2 ());
	    let son = B.succ ancetre node in
	    let rec keep_in_graphe l ing outg= match l with
	      |p::q -> (if (B.mem_vertex g p) then (keep_in_graphe q (p::ing) outg) else (keep_in_graphe q ing (p::outg)))
	      |[] -> (ing,outg)
	    in
	    let son_in,son_out = keep_in_graphe son [] [] in
	    if (son_in <> []) then
	      begin
		B.add_vertex g node;
		List.iter (fun x -> B.add_edge g node x) son_in;
		node_of_interest := (node) :: (!node_of_interest);
	      end;
	    List.iter (fun x -> deal_with_border x ancetre) son_out;
	  end
      in
      List.iter (fun x -> deal_with_bf (fst x) (snd x)) (!in_bf);
      List.iter (fun x -> deal_with_border (fst x) (snd x)) (!in_border);
 (*    if (B.is_empty g) then 
	(g,node_list)
      else*)
      (*List.iter (fun x -> if (B.mem_vertex g x) then () else (node_of_interest := x::(!node_of_interest))) node_list;*)
      (g,!node_of_interest)

    let get_history node_list state g bf border =
      let ancetre = state.ancestor in
      let node_of_interest = ref [] in
      let in_border = ref [] in
      let in_bf = ref [] in
      let explored = Hashtbl.create 10 in
      let explored_down = Hashtbl.create 10 in
      
      let rec explore_one boul node = 
	if boul then
	  begin
	    if (Hashtbl.mem explored node) then
	      ()
	    else 
	      begin
		Hashtbl.add explored node true;
		let is_in_bf = D.mem node bf in
		if (is_in_bf) then 
		  begin
		    found_in_bf node;
		  end
		else
		  begin
		    let is_in_border = D.mem node border in
		    if (is_in_border) then 
		      begin
			found_in_border node
		      end
	            else 
		      begin
			B.iter_pred (explore_one false) (ancetre) node;
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
		if (B.mem_vertex g node) then 
		  ()
		else
		  begin
		    Hashtbl.add explored node true;
		    let is_in_bf = D.mem node bf in
		    if (is_in_bf) then 
		      begin
			found_in_bf node
		      end
		    else
		      begin
			let is_in_border = D.mem node border in
			if (is_in_border) then 
			  begin
			    found_in_border node
			  end
			else 
			  begin
			    B.iter_pred (explore_one false) (ancetre) node;
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
	    Hashtbl.add explored_down node true;
	    B.add_vertex g node;
	    let add_edges_with_son son = 
	      B.add_edge g node son
	    in
	    B.iter_succ add_edges_with_son (ancetre) node;
	    B.iter_succ deal_with_bf (ancetre) node
	  end
      in
      let mark_down = Hashtbl.create 10 in
      let rec deal_with_border (node) = 
	if Hashtbl.mem mark_down node then
	  ()
	else
	  begin
	    Hashtbl.add mark_down node true;
	    let son = B.succ ancetre node in
	    let rec keep_in_graphe l ing outg= match l with
	      |p::q -> (if (B.mem_vertex g p) then (keep_in_graphe q (p::ing) outg) else (keep_in_graphe q ing (p::outg)))
	      |[] -> (ing,outg)
	    in
	    let son_in,son_out = keep_in_graphe son [] [] in
	    if (son_in <> []) then
	      begin
		B.add_vertex g node;
		List.iter (fun x -> B.add_edge g node x) son_in;
		node_of_interest := (node) :: (!node_of_interest);
	      end;
	    List.iter deal_with_border son_out;
	  end
      in
      List.iter (deal_with_bf) (!in_bf);
      List.iter (deal_with_border) (!in_border);
      (g,!node_of_interest)
    let iter_graphe_from_high f g start =
      let visited_up = Hashtbl.create 10 in
      let to_visite = ref [] in
      let rec go_up node = 
	if Hashtbl.mem visited_up node then 
	  ()
	else
	  begin
	    Hashtbl.add visited_up node true;
	    if (B.pred g node = []) then
	      to_visite := node :: !to_visite
	    else
	      (B.iter_pred go_up g node)
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
		  let l = remove node (B.pred g son) in
		  if l = [] then (to_visite := son :: !to_visite);
		  Hashtbl.replace pred son l
		end
	    in
	    B.iter_succ deal_with_son g node
	  end
      in
      while (!to_visite <> []) do
	let p::q = !to_visite in
	to_visite := q;
	visite_node p
      done
    let unif_graphe g g2 =
      let forall_vertex elem = 
	B.add_vertex g elem
      in
      let forall_edge deb fin = 
	B.add_edge g deb fin
      in
      B.iter_vertex forall_vertex g2;
      B.iter_edges forall_edge g2;;

    let rec split l a1 a2 = match l with
      |(a,b)::q ->  split q (a::a1) (b::a2)
      |[] -> (a1,a2)
    ;;
    let increase_high (state_init : t) (former_heads : B.V.t list) (head : B.V.t) =
      let g = B.copy (state_init.ancestor) in
      B.add_vertex g head;
      let deal_with_heads one = 
	B.add_edge g one head
      in
      List.iter deal_with_heads former_heads;
      let state_new = add ([head]) (state_init) g in
      state_new

    let increase_width (state_init : t) (f : D.u -> D.u -> B.V.t list -> (B.V.t list * B.t)) (head : B.V.t) =
      (*Printf.printf "NEW BF\n";
      flush stdout;*)
      if !Compteur.b1 then (Compteur.new_compteur "pred");
      if !Compteur.b2 then (Compteur.new_compteur "succ");
      if !Compteur.b3 then (Compteur.new_compteur "visite");
      if !Compteur.b1 then (Compteur.give_focus1 "pred");
      if !Compteur.b2 then (Compteur.give_focus2 "succ");      
      if !Compteur.b3 then (Compteur.give_focus3 "visite");      
      
      let bf = ref (state_init.bf) in
      let border_l_1,border_l_2 = split (state_init.border) [] [] in
      let border_l_ref = ref (border_l_2) in
      let border =  D.merge (border_l_2) [] in
      let keep_going = ref true in
      let graph_rep = B.create () in
      B.add_vertex graph_rep head;
      let interest = ref [head] in
      let nb_turn = ref 0 in
      while (!keep_going) do
(*	Printf.printf "New turn\n";*)
	incr nb_turn;
	match (!bf) with
	|(a,p)::q -> 
	  begin
	    bf := q;
	    match (!border_l_ref) with
	    |t::r -> 
	      begin
		
		let lretour,couronne = f p (D.merge (!border_l_ref) []) (!interest) in 
		(*List.iter (fun x -> Printf.printf "contret : %s\n" (binaire_to_hexa (D.name x))) lretour;*)
		interest := lretour;
		border_l_ref := r;
		unif_graphe graph_rep couronne;
		if (lretour = []) then
		  keep_going := false
	      end
	    |[] -> failwith "impossible";
	  end
	|[] -> raise No_more_bf;
      done;
      let added_node_l = ref [] in
      let g node_in = 
	added_node_l := node_in :: (!added_node_l)
      in
      iter_graphe_from_high g (graph_rep) head;
      unif_graphe graph_rep (state_init.ancestor);
      
      if !Compteur.b1 then (Compteur.take_focus1 "pred");
      if !Compteur.b2 then (Compteur.take_focus2 "succ");
      if !Compteur.b3 then (Compteur.take_focus3 "visite");
      let statenew = add (!added_node_l) (state_init) (graph_rep) in
      let n = ref 0 in
      let diff node = 
	if (B.mem_vertex state_init.ancestor node) then () else (incr n)
      in
      B.iter_vertex diff graph_rep;
      (*Printf.printf "%d %d\n" (Compteur.value "pred") (n); *)
      if !Compteur.b1 then (let f1 = Compteur.moyenne "pred" (!n) in Compteur.l1 := f1 :: (!Compteur.l1);Compteur.remove "pred");
      if !Compteur.b2 then (let f2 = Compteur.moyenne "succ" (!n) in Compteur.l2 := f2 :: (!Compteur.l2);Compteur.remove "succ");
      if !Compteur.b3 then (let f3 = Compteur.moyenne "visite" (!n) in Compteur.l3 := f3 :: (!Compteur.l3);Compteur.remove "visite");
      
      
      
      
      statenew,(!nb_turn);;
  end
