(*#load "graph.cma";;*)

open Format;;
open Graph;;
open Pack;;
open Imperative;;
open Digraph;;

let truc : int  = 3;;
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
  

module Comparable : Sig.COMPARABLE with type t = string = struct
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

module MyGraph = ConcreteBidirectional(Comparable);;

module ToDot = 
struct
   include MyGraph
   let r = ref 0 
   let t = Hashtbl.create 10
   let init () = Hashtbl.reset t; r := 0
   let edge_attributes (a, b) = []
   let default_edge_attributes _ = []
   let get_subgraph _ = None
   let vertex_attributes _ = [`Shape `Box]
   let vertex_name v =
     if (String.length v mod 4 = 0) then
       binaire_to_hexa v
     else
       v
   let default_vertex_attributes _ = []
  let graph_attributes _ = []
end;;

module MyDot = Graphviz.Dot(ToDot);;

module HashName = struct
  type tree = Node of bool * tree * tree | Nil of bool
  let float = Random.float
  let initr = Random.init
  let int = Random.int
  let current = ref (Nil(false))
  let is_in (stg : string) = 
    let n = String.length stg in
    let rec is_in_rec st i t = match t with
      |Nil(b) -> (i == n) && b
      |Node(b,g,d) -> if (i == n) then (b) else (
	if (st.[i] = '0') then 
	  (is_in_rec st (i+1) g)
	else
	  (is_in_rec st (i+1) d)
      )
    in
    is_in_rec stg 0 (!current)
  let add_immut (st : string ) (t :tree) = 
    let n = String.length st in
    let rec add st i t = match t with 
      |Nil(b) -> if (i == n) then (Nil(true)) else add st i (Node(b,Nil(false),Nil(false)))
      |Node(b,g,d) -> if (i == n) then (Node(true,g,d)) else (
      if (st.[i] = '0') then 
	  (Node(b,add st (i+1) g,d)) 
      else 
	  (Node(b,g,add st (i+1) d))
      )
    in
    add st 0 t
  let add st = 
    current := add_immut st (!current)

     let init () = current := Nil(false)
    let newname (n : int) =
      let rep = String.make n '0' in
      for i = 0 to (n-1) do
	if (Random.int 2 = 0) then (rep.[i] <- '0') else (rep.[i] <- '1') 
      done;
      rep
    let new_name n = 
      let rep = ref (newname n) in
      while (is_in (!rep)) do 
	rep := newname n
      done;
      add (!rep);
      !rep
end;;
(* Create a random dag with n nodes of high h and with tag of length t with branching factor p*)
module type Build = 
  sig
    module G : Sig.G
    val empty : unit -> G.t
    val add_vertex : G.t -> G.V.t -> unit
    val add_edge : G.t -> G.V.t -> G.V.t -> unit
  end

module type Elem = 
  sig
    type t
    val init : int -> unit
    val next_item : int -> t
  end



module AleaDag ( B : Build) (L : Elem with type t = B.G.V.t) =
  struct
    let alea n h t seed p =
      let rep = B.empty () in
      L.init seed;
      let tab = Array.make h [] in
      let u =  L.next_item t in
      tab.(0) <- [u];
      B.add_vertex rep u;
      for i = 1 to (n-1) do
	let p = L.next_item t in
	let k = if (i < h) then (i) else (1 + Random.int (h-1)) in
	tab.(k) <- p::(tab.(k));
	B.add_vertex rep p
      done;
      let to_iter (i: int) (s : B.G.V.t) =
	let rec to_iter2 l already = match l with
	  |t::q::r -> if ((Random.float 1.) < p ) then (B.add_edge rep t s ; to_iter2 (q::r) true) else (to_iter2 (q::r) already)
	  |t::[] -> if (not already) then B.(add_edge rep t s)
	  |[] -> ()
	in
	to_iter2 tab.(i) false
      in
      for i = 1 to (h-1) do
	List.iter (to_iter (i-1)) tab.(i)  
      done;
      rep,u
    ;;
  end

let alea (n : int) (h : int) (t : int) (p : float)=
  let rep = MyGraph.create () in
  HashName.init ();
  let tab = Array.make h [] in
  let u =  HashName.new_name t in
  tab.(0) <- [u];
  MyGraph.add_vertex rep u;
  for i = 1 to (n-1) do
    let p = HashName.new_name t in
    let k = if (i < h) then (i) else (1 + Random.int (h-1)) in
    tab.(k) <- p::(tab.(k));
      MyGraph.add_vertex rep p
  done;
  let to_iter (i: int) (s : string) =
    let rec to_iter2 l already = match l with
      |t::q::r -> if ((Random.float 1.) < p ) then (MyGraph.add_edge rep t s ; to_iter2 (q::r) true) else (to_iter2 (q::r) already)
      |t::[] -> if (not already) then MyGraph.(add_edge rep t s)
      |[] -> ()
    in
    to_iter2 tab.(i) false
  in
  for i = 1 to (h-1) do
    List.iter (to_iter (i-1)) tab.(i)  
  done;
  rep,u
;;

module L = struct

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

module Buildtest = struct
  module G = MyGraph
  let empty = MyGraph.create ~size:10
  let copy = MyGraph.copy
  let add_vertex a b = MyGraph.add_vertex a b 
  let add_edge a b c = MyGraph.add_edge a b c 
  let add_edge_e a b = MyGraph.add_edge_e a b 
  let remove_vertex a b = MyGraph.remove_vertex a b
  let remove_edge a b c = MyGraph.remove_edge a b c
  let remove_edge_e a b = MyGraph.remove_edge_e a b 
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

module MyParsor = Dot.Parse(Buildtool)(L);;

(*
let value (c : char) = int_of_char c -48;;
(*add s1 to s2 (the result is stock in s2)*)

let add (s : string) (a : int array) = 
  let n = String.length s in 
  let m = Array.length a in
  if (m = n) then 
    (
      for i = 0 to (n-1) do
	a.(i) <- value (s.[i]) + a.(i)
      done;
    )
  else ();;

let string_to_array s = 
  let n = String.length s in
  let rep = Array.make n 0 in
  for i = 0 to (n-1) do
    rep.(i) <- value (s.[i])
  done;
rep;;

let add_a_a a b = 
  let n = Array.length a in
  let m = Array.length b in
  if (n = m) then (
    for i= 0 to (n-1) do
      b.(i) <- a.(i) + b.(i)
    done
  );;

let rec remove e l = match l with
  |p::q -> if (p = e) then q else (p::(remove e q))
  |[] -> [];;

(*take a graph g and the min of the dag and computes the bloomfilter of the dag by giving back two hashtables node->bloomfilter * bloomfilter -> node(s) *)

let bloomfilter_old g b = 
  let n = String.length b in
  let repntob = Hashtbl.create 10 in 
  let repbton = Hashtbl.create 10 in
  let pred_not_visited = Hashtbl.create 10 in
  let tovisite = ref [b] in
  while (!tovisite <> []) do 
    match (!tovisite) with 
    |p::q -> 
      begin
	tovisite := q;
	let bf = Array.make n 0 in

	let toiteronpred pred = 
	  let a = Hashtbl.find repntob pred in
	  add_a_a a bf
	in
	MyGraph.iter_pred toiteronpred g p;
	add p bf;
	Hashtbl.add repntob p bf;
	Hashtbl.add repbton bf p;
        let toiter_on_succ succ = 
	  try (
	    let (l : string list)  = Hashtbl.find pred_not_visited succ in
	    let (q : string list)  = remove p l in
	    if (q = []) then (tovisite := (succ):: !tovisite ); 
	    Hashtbl.replace pred_not_visited succ q;
	    
	  )
	  with
	  |Not_found -> 
	    (
	      let q = remove p (MyGraph.pred g succ) in
	      if (q = []) then (tovisite := (succ):: !tovisite ); 
	      Hashtbl.add pred_not_visited succ (q)
	    )
	in
	MyGraph.iter_succ toiter_on_succ g p
      end 
    |[] -> failwith ("impossible")
  done;
    repntob,repbton;;

let min a b = if a < b then a else b;;
let min_a t1 t2 = 
  let n = Array.length t1 in
  let m = Array.length t2 in
  let rep = Array.make n 0 in
  if (n <> m) then (failwith ("not the same size")) else (
    for i = 0 to (n-1) do
      rep.(i) <- min (t1.(i)) (t2.(i))
    done
  );
  rep;;

let under t m =
 
  let n = Array.length t in
  let m2 = Array.length m in
  if (n <> m2) then (false) else (
    let i = ref 0 in
    while (!i < n && t.(!i) <= m.(!i)) do (i := !i +1) done;
    !i = n
  );;

(*m : value max, g : the graph , h : the hashtbl node -> bloomfield , t : origin of the dag*)
(* find the nodes which bloomfield is under the vector m*)
let find_under m g h t = 
  let rep = Hashtbl.create 10 in
  let rec find_under_rec cur = 
    if (Hashtbl.mem rep cur) then () else 
      begin
	let btree = Hashtbl.find h cur in
	Hashtbl.add rep cur (under btree m) ;
	MyGraph.iter_succ find_under_rec g cur
      end 
  in
  find_under_rec t;
  rep;;



let rec is_inter_empty s1 s2 = match s1 with
  |p::q -> if (Hashtbl.find s2 p) then false else (is_inter_empty q s2)
  |[] -> true;;

(*find the biggest common ancestors of a and b in g dag with origin t and h the hashtbl node -> bloomfield*)

let find_bca a b g t h =
  let m = min_a (Hashtbl.find h a) (Hashtbl.find h b) in
  let l = find_under m g h t in
  let count_under_min = ref 0 in
  let tocount key boolean = if boolean then count_under_min := !count_under_min + 1 in
  Hashtbl.iter tocount l;
  let ancestor = Hashtbl.create 10 in
  let rec mark_ancestor i current =
    let nb = 
      try Hashtbl.find ancestor current
      with 
      |Not_found -> 0
    in
    if (nb < i) then 
      begin
	Hashtbl.replace ancestor (current) (nb+1);
	MyGraph.iter_pred (mark_ancestor i) g current
      end
  in
  mark_ancestor 1 a;
  mark_ancestor 2 b;
  let htb_print a b = 
    Printf.printf "%s -> %d\n" a b
  in
  let filtre a = 
    try 
      let nb = Hashtbl.find ancestor a in
      nb = 2
    with
    |Not_found -> false
  in
  let toiter_filter1 key boolean =
    if (boolean && not (filtre key)) then Hashtbl.replace l key false
  in
  Hashtbl.iter toiter_filter1 l;
  let l2 = Hashtbl.copy l in
  let filtre2 a = 
    let next = MyGraph.succ g a in
    is_inter_empty next l2
  in
  let toiter_filter2 key boolean = 
    if (boolean && not (filtre2 key)) then Hashtbl.replace l key false
  in
  Hashtbl.iter toiter_filter2 l;
  let rep = ref [] in
  let iter_rep key boolean = if boolean then rep := key :: !rep in
  Hashtbl.iter iter_rep l;
  !count_under_min,!rep;;

(*Graphe de test*)
let gt = 
  let gtest = MyGraph.create () in
  MyGraph.add_vertex gtest "000";
  MyGraph.add_vertex gtest "001";
  MyGraph.add_vertex gtest "010";
  MyGraph.add_vertex gtest "011";
  MyGraph.add_vertex gtest "100";
  MyGraph.add_vertex gtest "101";
  MyGraph.add_vertex gtest "110";
  MyGraph.add_vertex gtest "111";
  
  MyGraph.add_edge gtest "000" "001";
  MyGraph.add_edge gtest "000" "010";
  MyGraph.add_edge gtest "001" "011";
  MyGraph.add_edge gtest "001" "100";
  MyGraph.add_edge gtest "010" "100";
  MyGraph.add_edge gtest "010" "101";
  MyGraph.add_edge gtest "100" "110";
  MyGraph.add_edge gtest "100" "111";
  MyGraph.add_edge gtest "101" "110";
  MyGraph.add_edge gtest "101" "111";
  gtest;;


(*Fin*)

let rec get i l = match l with
  |p::q -> 
    begin 
      if (i = 0 ) then p else (get (i-1) q)
    end
  |[] -> failwith "list too short";;
(*Test nombre d'élements à visiter : *)

let test n (*number of dags*) c (*number of couples per dag*) m (*size of dags*) h (*high of dags*) p (*number of fathers*) =
  let avg_number_bca = ref 0 in
  let avg_number_under_min = ref 0 in
  let compt = ref 0 in
  for i = 1 to n do
    let g,d = alea m h 160 p in
    let ntob,bton = bloomfilter g d in
    let l = ref [] in
    let to_iter a = l := a :: !l in
    MyGraph.iter_vertex to_iter g;
    let size = List.length (!l) in
    for j = 1 to c do
      let ra = Random.int (size) in
      let rb = Random.int (size) in
      let a = get (ra) (!l) in
      let b = get (rb) (!l) in
      let under_min,li = find_bca a b g d ntob in
      compt := !compt + 1;
      avg_number_bca := !avg_number_bca + (List.length li);
      avg_number_under_min := !avg_number_under_min + under_min;
      let nf = float_of_int (!compt) in
      Printf.printf "%d --- NB_BCA : %f --- NB_UNDER_MIN : %f --- UM : %d --- a : %d --- b : %d \n" (!compt) (float_of_int (!avg_number_bca) /. (nf)) (float_of_int (!avg_number_under_min) /. nf) (under_min) ra rb;
      flush stdout;
    done
  done;
  let nf = float_of_int (!compt) in
  (float_of_int (!avg_number_bca) /. (nf *. (float_of_int m))),(float_of_int (!avg_number_under_min) /. (nf*.(float_of_int m)));;
(*Impression avec MyDot*)

let trees () = 
  let h = ref 5 in
  while (!h <= 75) do 
    let p = ref 0.1 in
    while (!p < 0.91) do
      let file = open_out_bin ("res0/exemplearbre/mygraph"^(string_of_int (!h))^"-"^(string_of_float (!p))^".dot") in
      let g,d = alea 100 (!h) 160 (!p) in
      ToMyDot.init ();
      MyDot.output_graph file g;
      p := !p +. 0.1;
      Printf.printf "%d %f\n" (!h) (!p);
      flush stdout;
    done;
    h := !h + 10;
  done;;

trees();;
let imprime () =
  
  let h = ref 5 in
  while (!h <= 75) do 
    let cout = open_out ("res1/data_nb_under_min_"^(string_of_int (!h))) in
    let cout2 = open_out ("res1/data_nb_bca_"^(string_of_int (!h))) in
    let p = ref 0.1 in
    while (!p < 0.91) do
      let a,b = test 20 20 100 (!h) (!p) in
      Printf.fprintf cout "%f %f\n" (!p) b;
      Printf.fprintf cout2 "%f %f\n" (!p) a; 
      p := !p +. 0.1;
      Printf.printf "%d %f\n" (!h) (!p);
      flush stdout;
    done;
    h := !h + 10;
    
    close_out cout;
    close_out cout2;
  done;;

imprime ();;

(*Another try at bloomfilters*)

let rec add pos value bloomfilter = match bloomfilter with
  |p::q -> 
    if (fst p > pos) then (((pos,value)::p::q)) else 
      begin
	if (fst p = pos) then (((pos,value + snd p)::q))
	else p::(add pos value q)
      end
  |[] -> [pos,value]
;;

let add_b_to_b b1 b2 = 
  let rep = ref [] in
  let rec iter a b = match (a,b) with
    |(p1,v1)::r1,(p2,v2)::r2 -> 
      begin
	if (p1 < p2) then
	  begin
	    rep := (p1,v1):: (!rep);
	    iter r1 b
	  end
	else 
	  begin
	    if (p1 = p2) then (rep := (p1,v1+v2) :: !rep ; iter r1 r2)
	    else (rep := (p2,v2):: !rep ; iter a r2)
	  end
      end
    |p::q,[] ->  (rep := p :: !rep ; iter q [])
    |[],p::q ->  (rep := p :: !rep ; iter q [])
    |[],[] -> ()
  in
  iter b1 b2;
  List.rev (!rep);;

*)
