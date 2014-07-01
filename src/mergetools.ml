module type DataStructure =
sig
  type t
  type u
  val nb_max : int
  val build_next : u list -> t -> u
  val build_next_l : u list -> t list -> u
  val build_union : u list -> u
  val test_belong : t -> u -> bool
end


module MergeTools (B : Alea.Build) (D : DataStructure with type t = B.G.V.t) :
sig
  type v = (int * D.u) list
  val add : B.G.V.t list -> v -> v -> B.G.t -> (v * v)
  val get_history : B.G.V.t list -> B.G.t -> B.G.t -> D.u -> D.u -> (B.G.t * (B.G.V.t list))
  val iter_graphe_from_high : (B.G.V.t -> unit) -> B.G.t -> B.G.V.t -> unit
  val unif_graphe : B.G.t -> B.G.t -> unit
end =
  struct
    let rec remove e l = match l with
      |p::q -> if (e = p) then q else (p::(remove e q))
      |[] -> []
    ;;
    type v = (int * D.u) list
    let build_next_border bf parent_list current_border =
      let rep = ref (current_border) in
      let nb_added = ref 0 in
      let one_elem node = 
	if (D.test_belong node bf) then 
	  ()
	else
	  begin
	    rep := D.build_next [!rep] node;
	    nb_added := !nb_added + 1
	  end
      in
      List.iter one_elem parent_list;
      !nb_added,!rep;;
    let add nodel pere_bf_l border_bf_l g = 
      let rep = ref pere_bf_l in
      let repf = ref border_bf_l in
      let rec add_one l = match l with
	|p::q ->
	  begin
	    match (!rep) with
	    |(nb,bf)::r -> 
	      begin
		if (nb+1 > D.nb_max) then
		  begin
		    let a = D.build_next [] p in
		    rep := (1,a) :: (!rep);
		    let b = D.build_next_l [] (B.G.pred g p) in
		    repf := (1,b) :: (!repf);
		    add_one q;
		  end
		else
		  begin
		    let a = D.build_next [bf] p in
		    rep := (nb+1,a) :: r;
		    begin
		      match (!repf) with
		      |[] -> failwith "empty border with non empty bf"
		      |(nb_border,border)::queue -> 
			begin
			  let n,b= build_next_border a (B.G.pred g p) (border) in
			  repf := (nb_border +n, b)::queue
			end;
		    end;
		    add_one q;
		  end
	      end
	    |[] -> 
	      begin
		rep := [1,D.build_next [] p]; repf := [1,D.build_next[] p]; add_one q
	      end
	  end
	|[] -> ()
      in
      add_one nodel;
      !rep,!repf
    let get_history node_list ancetre g bf border =
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
		let is_in_bf = D.test_belong node bf in
		if (is_in_bf) then 
		  begin
		    found_in_bf node;
		  end
		else
		  begin
		    let is_in_border = D.test_belong node border in
		    if (is_in_border) then 
		      begin
			found_in_border node
		      end
	            else 
		      begin
			B.G.iter_pred (explore_one false) (ancetre) node;
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
		if (B.G.mem_vertex g node) then 
		  ()
		else
		  begin
		    Hashtbl.add explored node true;
		    let is_in_bf = D.test_belong node bf in
		    if (is_in_bf) then 
		      begin
			found_in_bf node
		      end
		    else
		      begin
			let is_in_border = D.test_belong node border in
			if (is_in_border) then 
			  begin
			    found_in_border node
			  end
			else 
			  begin
			    B.G.iter_pred (explore_one false) (ancetre) node;
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
	    B.G.iter_succ add_edges_with_son (ancetre) node;
	    B.G.iter_succ deal_with_bf (ancetre) node
	  end
      in
      let mark_down = Hashtbl.create 10 in
      let rec deal_with_border (node) = 
	if Hashtbl.mem mark_down node then
	  ()
	else
	  begin
	    Hashtbl.add mark_down node true;
	    let son = B.G.succ ancetre node in
	    let rec keep_in_graphe l ing outg= match l with
	      |p::q -> (if (B.G.mem_vertex g p) then (keep_in_graphe q (p::ing) outg) else (keep_in_graphe q ing (p::outg)))
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
	    if (B.G.pred g node = []) then
	      to_visite := node :: !to_visite
	    else
	      (B.G.iter_pred go_up g node)
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
		  let l = remove node (B.G.pred g son) in
		  if l = [] then (to_visite := son :: !to_visite);
		  Hashtbl.replace pred son l
		end
	    in
	    B.G.iter_succ deal_with_son g node
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
      B.G.iter_vertex forall_vertex g2;
      B.G.iter_edges forall_edge g2;;
    
  end
