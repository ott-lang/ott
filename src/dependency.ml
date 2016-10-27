(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2010                                                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

open Types

module G = Graph.Pack.Digraph

(* *** computing the dependencies of a syntaxdefn *)

(* local debug *)
let show = 
  let count = ref 0 in
  let internal g =
    let name = "tmp_"^(string_of_int !count)^".dot" in
    G.dot_output g name;
    count := !count+1
  in internal

let print_class c =
  print_string "[";
  let rec internal ntr_class =
    ( match ntr_class with
    | [] -> ()
    | ntr::[] -> Printf.printf "%s" ntr
    | ntr::tl -> Printf.printf "%s, " ntr; internal tl )
  in 
  match c with
  | Mvrlist l | Ntrlist l -> internal l;
  print_string "]"

let debug_graph g i p = 
  print_endline "*** vertex informations";
  List.iter (fun (v,n) -> 
    Printf.printf "%i : " (G.V.label v); p n; print_newline ()) i;
  print_newline ();
  show g 
   
let debug = ref false (* true to generate dot files *)
(* end local debug *)

let compute_dependencies (xd:syntaxdefn) (m:string) : xd_dependencies =
  
  let rules_of_language = xd.xd_rs in

  (* auxiliary function on graphs *)
  let add_vertex g i c v =  
    let vertex = G.V.create !c in
    i := (vertex, v)::!i;
    G.add_vertex g vertex;
    c := !c+1 in

  (* we rely on the simplest graphs provided by ocamlgraph, and we
     explicitly record the association vertex_identifier -> nonterminal
     list + metavar list *) 
  let g = G.create () in let g_vertex_info,
    g_vertex_count = ref [], ref 0 in

  let vertex_associated_to_ntr_or_mvr m = 
    (* print_endline ("***"^Grammar_pp.pp_plain_metavarroot m); *)
    fst (List.find 
	   ( fun (_,n) -> match n with
	   | Mvrlist ml -> List.mem m ml
	   | Ntrlist ml -> List.mem m ml )  
	   !g_vertex_info) in

  (* a node corresponds to a nonterminal or a metavariable of the language *)
  (* scan the language, adding all the nodes to the graph *)

  let ntrs_class_of_language l =
    List.map (fun r -> Ntrlist (List.map fst r.rule_ntr_names)) rules_of_language in
  (* list of equivalence classes of non-terminals, each represented as a list *)
  let mvrs_class_of_language l =
    List.map (fun m -> Mvrlist (List.map fst m.mvd_names)) xd.xd_mds in
  (* list of equivalence classes of metavars, each represented as a list *)

  List.iter (add_vertex g g_vertex_info g_vertex_count) (ntrs_class_of_language xd);
  List.iter (add_vertex g g_vertex_info g_vertex_count) (mvrs_class_of_language xd);

  (* an edge correspond to a call between nonterminals/metavars: 
     add all the edges *)
  let add_edge ns nt =
    let v_ns = vertex_associated_to_ntr_or_mvr ns in
    let v_nt = vertex_associated_to_ntr_or_mvr nt in
    G.add_edge g v_ns v_nt in

  let add_edges_rule r =
    let add = add_edge r.rule_ntr_name in
    NtrSet.iter add (Auxl.primary_ntrs_used_in_rule xd false (Some m) true r);
    MvrSet.iter add (Auxl.primary_mvrs_used_in_rule xd false (Some m) r);
  in

  List.iter add_edges_rule rules_of_language;

  if !debug then debug_graph g !g_vertex_info print_class;

  (* g contains the dependency graph. we now build the informations 
     that will be stored in the xd *)

  (* 1- topological sort *)

  (* now compute the strongly connected components of g *)
  let scc_node_sets = G.Components.scc_list g in

  (* create a new graph, each node correspond to a set of sc nodes in g *)
  let scc_graph = G.create () in
  let scc_vertex_info, scc_vertex_count = ref [], ref 0 in

  List.iter (add_vertex scc_graph scc_vertex_info scc_vertex_count) scc_node_sets;

  (* scan all the original arcs, and add them to the component graph *)
  let vertex_associated_to_v v =
    fst (List.find (fun (_,n) -> List.mem v n) !scc_vertex_info) in

  G.iter_edges
    (fun s d ->
      G.add_edge scc_graph (vertex_associated_to_v s) (vertex_associated_to_v d))
    g;
  if !debug then debug_graph scc_graph !scc_vertex_info
      (fun vl ->
	List.iter (fun v -> print_class (List.assoc v !g_vertex_info)) vl);

  (* scc is the graph of the components of g. we now do a topological sort *)

  (* first remove the reflexive edges *)
  G.iter_vertex (fun v -> G.remove_edge scc_graph v v) scc_graph;
  if !debug then debug_graph scc_graph !scc_vertex_info
      (fun vl -> List.iter (fun v -> print_class (List.assoc v !g_vertex_info)) vl);

  let back_to_nt_or_mv_root l = 
    match l with
    | Mvrlist l -> Mvr (List.hd l)
    | Ntrlist l -> Ntr (List.hd l) in

  (* then do a topological sort and dump the new rules *)
  let dump_scc_vertex v rl =
    let dump_vertex v r =
      let ntr_mvr_l = List.assoc v !g_vertex_info in
      let v = back_to_nt_or_mv_root ntr_mvr_l in
      v::r in
    (* (List.find (fun r -> r.rule_ntr_name = ntr) rules_of_language)::r in *)
    let vl = List.assoc v !scc_vertex_info in
    (List.fold_right dump_vertex vl [])::rl in

  let topological_sort = 
    G.Topological.fold dump_scc_vertex scc_graph [] in

  (* if !debug then Grammar_pp.pp_plain_top_sort topological_sort; *)

  (* 2- dump the dependency graph *)
  (* build the transitive closure of g *)
  let tc_g = G.transitive_closure g in

  let dep_graph = ref [] in
  G.iter_vertex 
    ( fun v -> 
      let ntr_list v = 
	List.assoc (G.find_vertex g (G.V.label v)) !g_vertex_info in
      let s = G.succ tc_g v in 
      let vi = back_to_nt_or_mv_root (ntr_list v) in
      let si = List.map (function x -> back_to_nt_or_mv_root (ntr_list x)) s in 
      dep_graph := (vi,si)::!dep_graph )
    tc_g;
  
  let dep_graph_nontran = ref [] in
  G.iter_vertex 
    ( fun v -> 
      let ntr_list v = 
	List.assoc (G.find_vertex g (G.V.label v)) !g_vertex_info in
      let s = G.succ g v in 
      let vi = back_to_nt_or_mv_root (ntr_list v) in
      let si = List.map (function x -> back_to_nt_or_mv_root (ntr_list x)) s in 
      dep_graph_nontran := (vi,si)::!dep_graph_nontran )
    g;
  
  { xd_dep_ts = topological_sort; xd_dep_graph = !dep_graph ;xd_dep_graph_nontran = !dep_graph_nontran}


(* *** general sorting function - used for funcs *)

let sort (l : ('b * 'b list * 'a) list) : ('b * 'a) list list * 'b list =
  let g = G.create () in
  let g_vertex_info, g_vertex_count = ref [], ref 0 in  
  
  let find_vertex n info =
    try
      List.assoc n (List.map (fun (x,y) -> (y,x)) !info) 
    with Not_found -> 
      (* Auxl.error ("internal: sort: cannot find a node labelled " ^ n ^ "\n") *) 
      Auxl.warning ("internal: sort: cannot find a node labelled " ^ n ^ "\n");
      raise Not_found in

  let add_vertex g i c v =
    let vertex = G.V.create !c in
    i := (vertex, v)::!i;
    G.add_vertex g vertex;
    c := !c+1 in

  let add_edge g sn tn =
    try
      let snv = find_vertex sn g_vertex_info in
      let tnv = find_vertex tn g_vertex_info in
      if (not (G.mem_edge g snv tnv)) then G.add_edge g snv tnv 
    with Not_found -> 
      Auxl.warning ("internal: sort: cannot connect " ^ sn ^ " to " ^ tn ^"\n") in
  
  (* adding vertexes *)
  let vl = List.map (function (x,_,_) -> x) l in
  (* List.iter (fun x -> print_endline ("added "^x)) vl; *)
  List.iter (add_vertex g g_vertex_info g_vertex_count) vl;
  
  (* adding arcs *)
  List.iter
    ( function (sn,tnl,_) -> 
      List.iter (add_edge g sn) tnl )
    l;

  (* 1- *)

  (* compute the strongly connected components of g *)
  let scc_node_sets = G.Components.scc_list g in

  (* create a new graph, each node correspond to a set of sc nodes in g *)
  let scc_graph = G.create () in
  let scc_vertex_info, scc_vertex_count = ref [], ref 0 in

  let find_scc_vertex n info =
    fst (List.find (fun (_,ml) -> List.mem n ml) !info) in

  List.iter (add_vertex scc_graph scc_vertex_info scc_vertex_count) scc_node_sets;

  (* scan all the original arcs, and add them to the component graph *)    
  G.iter_edges
    (fun s d ->
      G.add_edge scc_graph (find_scc_vertex s scc_vertex_info) (find_scc_vertex d scc_vertex_info))
    g;

  (* scc is the graph of the components of g. we now do a topological sort *)

  (* first remove the reflexive edges *)
  G.iter_vertex (fun v -> G.remove_edge scc_graph v v) scc_graph;
  
  let top_sort = G.Topological.fold
      ( fun sn rl -> 
	let dump_vertex v r =
	  let a = (List.assoc v !g_vertex_info) in
	  let (_,_,s) = List.find (function (x,_,_) -> x = a) l in
	  (a,s)::r in 
	let vl = List.assoc sn !scc_vertex_info in
	(List.fold_right dump_vertex vl [])::rl )

      scc_graph [] in

  (* 2- *)

  let singletons = List.flatten (List.filter (fun x -> (List.length x) = 1) top_sort) in
  let rec_singletons = 
    List.map (fun (x,_) -> x ) 
      ( List.filter 
	  (fun (nt,_) -> 
	    let v = find_vertex nt g_vertex_info in
	    G.mem_edge g v v)
	  singletons ) in

(* we return the topological sort of the strongly connected
  components, and a list of nodes which are not part of a group but
  which have a dependency on themselves *)

  (top_sort, rec_singletons)

(* *** the collapser *)

let isa_primrec_collapse m xd (funcs:int_funcs) : int_funcs_collapsed = 
  let rec group funcs carry =
    match funcs with
    | [] -> List.rev carry
    | x::xs ->
	let (a,b) = List.partition (fun y -> x.r_fun_type = y.r_fun_type) xs in
	group b ((x::a)::carry)
  in 
  let collapse_clause m id (_, lhs, rhs) =
    match m with
    | Isa _ -> "\"" ^ id ^ " " ^ lhs ^ " = (" ^ rhs ^ ")\"\n"
    | _ -> Auxl.error "internal: isa_collapse called with wrong target\n" in

  let collapse_clauses m id clauses =
    String.concat "| " (List.map (collapse_clause m id) clauses) in

  let collapse_func m f =
    (f.r_fun_id, f.r_fun_dep, (f.r_fun_header, (collapse_clauses m f.r_fun_id f.r_fun_clauses), Footer_empty)) in

  let collapse_big_group m xd g =
    (* 1- the id *)
    let id_list = List.map (fun x -> x.r_fun_id) g in
    let id = String.concat "_" id_list in

    (* 1.5- build the table of projections *)
    let projection_list = 
      let make_projection_code x =
	"(%(" ^ String.concat "," id_list ^ ")." ^ x ^ ") (" ^ id in
      let make_projection x =
	"(%(" ^ String.concat "," id_list ^ ")." ^ x ^ ") o " ^ id in
      List.map (fun x -> 
	(x,(id,make_projection_code x, make_projection x))) id_list in

    (* 2- the dependencies *)
    let deps = List.concat (List.map (fun x -> x.r_fun_dep) g) in
    Auxl.debug ("** " ^ id ^ " depends on:\n" ^ (String.concat "\n" deps) ^ "\n");

    (* 3- the header *)
    let extract_inp_type (header,_,_) =
      let rx_inp_type = Str.regexp ".*\"\\(.*\\) =>.*" in
      if Str.string_match rx_inp_type header 0 
      then Str.matched_group 1 header 
      else Auxl.error "internal: cannot extract the inp type from the header\n" in
    let (inp_type,inp_type_list) =
      ( match List.map (fun x -> extract_inp_type x.r_fun_header) g with
      | h::t -> (h,t)
      | _ -> raise Auxl.ThisCannotHappen ) in
    if not (List.for_all (fun t -> String.compare inp_type t = 0) inp_type_list) 
    then Auxl.error "internal: collapsing functions over different types\n";

    let extract_ret_type (header,_,_) =
      let rx_ret_type = Str.regexp ".*=> \\(.*\\)\"" in
      if Str.string_match rx_ret_type header 0 
      then Str.matched_group 1 header 
      else Auxl.error "internal: cannot extract the out type from the header\n" in
    let ret_types = List.map (fun x -> extract_ret_type x.r_fun_header) g in
   
    let output_type =
      "(" ^ String.concat ") * (" ret_types ^ ")" in

    let header = 
      id ^ " :: \"" 
      ^ inp_type 
      ^ " => " ^ output_type ^ "\"\n" in

    (* 4- the lhs *)
    let extract_lhs f =
      let (_,lhs,rhs) = Auxl.split3 ((List.hd g).r_fun_clauses) in
      lhs in 
    let lhs = extract_lhs (List.hd g) in
    
    let compare_lhs l1 l2 =
      List.for_all2 (fun lc1 lc2 -> String.compare lc1 lc2 = 0) l1 l2 in
    if not (List.for_all (fun f -> compare_lhs lhs (extract_lhs f)) (List.tl g))
    then Auxl.error "internal: non equal lhs when collapsing";

    (* 5- the rhs *)
    let extract_rhs f =
      let (_,lhs,rhs) = Auxl.split3 f.r_fun_clauses in
      rhs in
    
    let rhs_list = List.map extract_rhs g in 
    let rhs_lines = try 
      Auxl.transpose rhs_list 
    with
      e -> 
	print_string ("\nerror in dependency.ml, around 383, in call to transpose, on:\n"
		      ^String.concat "\n" 
			  (List.map (fun rhss -> String.concat "&&" rhss) rhs_list)
		      ^"\n");
	flush stdout; raise e in

    let rhs =
      List.map
	(fun l -> (String.concat " , " l))
	rhs_lines in

    (* 6- build the big gadget *)    
    let clauses = List.map (fun (c1,c2) -> ("",c1,c2)) (List.combine lhs rhs) in
    let dummy_type = "" in
    let func = 
      { r_fun_id = id;
	r_fun_dep = deps;
	r_fun_type = dummy_type;
	r_fun_header = (header,"","");
	r_fun_clauses = clauses } in
    let collapsed = collapse_func m func in

    (* 7- generate the projections and associated lemmas *)

    let make_definitions e h =
      "definition " ^ e	
      ^ " :: " ^ "\"" ^ inp_type ^ " => " ^ (extract_ret_type h) ^ "\" where\n"
      ^ "\"" ^ e ^" == " 
      ^ ((fun (_,_,x) -> x) (List.assoc e projection_list)) 
      ^ "\"\n" in

    let projections = 
      String.concat "\n" 
	(List.map
	   (fun x -> make_definitions x.r_fun_id x.r_fun_header)
	   g)
      ^ "\n" in
    
    let make_lemma_clauses id clauses =
      String.concat "\n" 
	(List.map (fun (_,lhs,rhs) -> 
	  "\"" ^ id ^ " " ^ lhs ^ " = " ^ rhs ^ "\"") clauses) in
    
    let lemma_clauses = 
      String.concat "\n" 
	(List.map 
	   (fun x -> make_lemma_clauses x.r_fun_id x.r_fun_clauses)
	   g)
      ^ "\n" in 

    let lemma_defns =
      String.concat " " (List.map (fun x -> x.r_fun_id^"_def") g) in
(*     let lemma =  *)
(*       "lemma\n"  *)
(*       ^ String.concat "\n"  *)
(* 	  (List.map  *)
(* 	     (fun (id,_,_,_,clauses) -> make_lemma_clauses id clauses) *)
(* 	     g) *)
(*       ^ "\n  by(simp_all add: "  *)
(*       ^ String.concat " " (List.map (fun (id,_,_,_,_) -> id^"_def") g) *)
(*       ^ ")\n\n" in *)

    let footer = Footer_isa_proj_lemma (projections,lemma_clauses,lemma_defns) in

    let collapsed = 
      ( match collapsed with
      | (id,dep,(lhs,rhs,_)) ->
	  (id,dep,(lhs,rhs,footer)) ) in

    (collapsed, projection_list) in

  let collapse_group m xd g =
    Auxl.debug ("** COLLAPSING\n" ^ String.concat "\n" (List.map (fun x -> x.r_fun_id) g) ^ "\n");
    if List.length g = 1 
    then ( collapse_func m (List.hd g), [] )
    else collapse_big_group m xd g in 

  (* 8- compute the collapsed thing *)
  let groups = group funcs.i_funcs [] in

  let collapsed, substitutions = 
    List.split (List.map (collapse_group m xd) groups) in
  let substitutions = List.concat substitutions in

  (* 9- update the names of the collapsed things *)
  let update_deps substs deps =
    let update_dep dep =
      Auxl.debug ("* updating " ^ dep ^ "\n" );
      try (fun (p,_,_) -> Auxl.debug ("* found " ^ p ^ "\n"); p) (List.assoc dep substs)
      with Not_found -> Auxl.debug ("* not found\n"); dep in
    Auxl.remove_duplicates (List.map update_dep deps) in 

  let substitute substs s =
    let int_string = ref s in
    let substitute_one (orig,(_,sub,_)) =
      let rx_orig = Str.regexp ( "("^(Str.quote orig)^" \\([^)]*\\))" ) in
      int_string := 
	Str.global_replace rx_orig ("("^sub^" \\1))") !int_string
    in List.iter substitute_one substs; !int_string in

  List.map (fun (i,d,(h,body,footer)) -> 
    ( i, 
      update_deps substitutions d, 
      ( h, 
	substitute substitutions body, 
	footer ))) 
    collapsed

let build_footer_proof s =
  match s with
  | None -> Footer_empty
  | Some s -> Footer_proof s

let isa_fun_collapse m xd funcs =
  let collapse_clause m id (_,lhs, rhs) =
    "\""^ id ^" "^ lhs ^ " = (" ^ rhs ^ ")\"\n" in
  let collapse_clauses m id clauses =
    ""
    ^ String.concat "| " (List.map (collapse_clause m id) clauses) in
  let collapse_func m f =
    (f.r_fun_id, f.r_fun_dep, (f.r_fun_header,
			       (collapse_clauses m f.r_fun_id f.r_fun_clauses),
			       build_footer_proof funcs.i_funcs_proof)) in
  List.map (collapse_func m) funcs.i_funcs

let hol_collapse m xd funcs = 
  let collapse_clause m id (_,lhs, rhs) =
    "  ( "^ id ^" "^ lhs ^ " = " ^ rhs ^ ")\n" in
  let collapse_clauses m id clauses =
    "" 
    ^ String.concat "/\\" (List.map (collapse_clause m id) clauses) in
  let collapse_func m f =
    (f.r_fun_id, f.r_fun_dep, (f.r_fun_header, 
			       (collapse_clauses m f.r_fun_id f.r_fun_clauses), 
			       build_footer_proof funcs.i_funcs_proof)) in
  List.map (collapse_func m) funcs.i_funcs

let coq_collapse m xd funcs = 
  let collapse_clause m id (_,lhs, rhs) =
    "  | " ^ lhs ^ " => " ^ rhs ^ "\n" in
  let collapse_clauses m id clauses =
    String.concat "" (List.map (collapse_clause m id) clauses) in
  let collapse_func m f =
    (f.r_fun_id, f.r_fun_dep, (f.r_fun_header, (collapse_clauses m f.r_fun_id f.r_fun_clauses), Footer_empty)) in
  List.map (collapse_func m) funcs.i_funcs

let twf_collapse m xd funcs = 
  let collapse_clause m id (pfx, lhs, rhs) =
    "" ^ id ^ "/" ^ pfx ^ " : " ^ id ^ " " ^ lhs ^ " " ^ rhs ^ ".\n" in
  let collapse_clauses m id clauses =
    String.concat "" (List.map (collapse_clause m id) clauses) in
  let collapse_func m f =
    (f.r_fun_id, f.r_fun_dep, (f.r_fun_header, (collapse_clauses m f.r_fun_id f.r_fun_clauses), Footer_empty)) in
  List.map (collapse_func m) funcs.i_funcs

let caml_collapse m xd funcs = 
  let collapse_clause m id (_, lhs, rhs) =
    "  | " ^ lhs ^ " -> " ^ rhs ^ "\n" in
  let collapse_clauses m id clauses =
    String.concat "" (List.map (collapse_clause m id) clauses) in
  let collapse_func m f =
    (f.r_fun_id, f.r_fun_dep, (f.r_fun_header, (collapse_clauses m f.r_fun_id f.r_fun_clauses), Footer_empty)) in
  List.map (collapse_func m) funcs.i_funcs

let lem_collapse m xd funcs = 
  let collapse_clause m id (_, lhs, rhs) =
    lemTODO "6" "   | " ^ lhs ^ " -> " ^ rhs ^ "\n" in
  let collapse_clauses m id clauses =
    String.concat "" (List.map (collapse_clause m id) clauses) in
  let collapse_func m f =
    (f.r_fun_id, f.r_fun_dep, (f.r_fun_header, (collapse_clauses m f.r_fun_id f.r_fun_clauses), Footer_empty)) in
  List.map (collapse_func m) funcs.i_funcs

let rec remove_duplicates (funcs:int_func list) : int_func list =
  match funcs with
  | [] -> []
  | x::xs ->
      if (List.exists (fun y -> String.compare y.r_fun_id x.r_fun_id = 0) xs) 
      then remove_duplicates xs 
      else x::(remove_duplicates xs)

let collapse m xd (funcs:int_funcs) : int_funcs_collapsed =
  let funcs = { funcs with i_funcs = remove_duplicates funcs.i_funcs } in
  match m with
  | Isa io when io.ppi_isa_primrec -> isa_primrec_collapse m xd funcs
  | Isa io when not io.ppi_isa_primrec -> isa_fun_collapse m xd funcs
  | Hol _ -> hol_collapse m xd funcs
  | Lem _ -> lem_collapse m xd funcs
  | Coq _ -> coq_collapse m xd funcs
  | Twf _ -> twf_collapse m xd funcs
  | Caml _ -> caml_collapse m xd funcs
  | Tex _ | Ascii _ -> Auxl.error "internal: collapse of Tex-Ascii\n"

(* *** the printer *)

let print m xd (sorting,refl) =
  match m with
  | Tex _ | Ascii _ -> Auxl.error "internal: print of Tex-Ascii\n"
  | Isa io ->
      let print_lemma block = 
	if ( List.exists 
	       (fun (_,(_,_,f)) ->
		 match f with
		 | Footer_empty | Footer_proof _ -> false
		 | Footer_isa_proj_lemma _ -> true) )
	       block 
	then
	  (String.concat "" 
	     (List.map 
		(fun (_,(_,_,f)) ->
		  match f with
		  | Footer_empty | Footer_proof _ -> ""
		  | Footer_isa_proj_lemma (p,_,_) -> p ) 
		block))
	  ^ 
	    ( if io.ppi_generate_lemmas 
	    then 
	      "lemma\n" 
	      ^ (String.concat "" 
		   (List.map 
		      (fun (_,(_,_,f)) ->
			match f with
			| Footer_empty | Footer_proof _ -> ""
			| Footer_isa_proj_lemma (_,c,_) -> c ) 
		      block))
	      ^ "  by(simp_all add: "
	      ^ (String.concat " " 
		   (List.map 
		      (fun (_,(_,_,f)) ->
			match f with
			| Footer_empty | Footer_proof _ -> ""
			| Footer_isa_proj_lemma (_,_,i) -> i ) 
		      block))
	      ^ ")\n\n"
	    else "" )
	else "" in

      let print_block block = 
	( match io.ppi_isa_primrec with
	| false ->
	    "fun\n"
	    ^ (String.concat "and " (List.map (fun (_,((h1,h2,h3),_,_)) -> h1^h2^h3) block))
	    ^ "where\n"
	    ^ (String.concat "| " (List.map (fun (_,(_,s,_)) -> s) block))
            ^ "\n"
	    ^ (print_lemma block)
	| true ->
	    "primrec\n"
	    ^ (String.concat "and " (List.map (fun (_,((h1,h2,h3),_,_)) -> h1^h2^h3) block))
	    ^ "where\n" 
	    ^ (String.concat "| " (List.map (fun (_,(_,s,_)) -> s) block))
            ^ "\n" 
	    ^ (print_lemma block) ) in
      String.concat "" (List.map print_block sorting)

  | Hol _ ->
      let print_block block = 
	let (nt,((h1,h2,h3),s,f)) = List.hd block in
	let (define,proof) =
	  match f with 
	  | Footer_proof s -> ("tDefine", "("^s^")")
	  | _ -> ("ottDefine", "") in
	"val _ = "^define^" \""^nt^"\" `\n  "
	^ (String.concat "/\\" (List.map (fun (_,(_,s,_)) -> s) block))
        ^ "`"^proof^";\n" in 
      String.concat "\n" (List.map print_block sorting) 


  | Coq _ ->
      let print_block block =
	if ((List.length block) = 1) 
	then 
	  let (nt,((h1,h2,h3),s,_)) = List.hd block in
	  if (List.mem nt refl) 
	  then "Fixpoint " ^ h1 ^ h2 ^ h3 ^ s ^ "end.\n\n" 
	  else "Definition " ^ h1 ^ h3 ^ s ^ (if String.compare h3 "" = 0 then ".\n\n" else "end.\n\n")
	else
	  "Fixpoint "
	  ^ (String.concat "end\nwith " 
               (List.map (fun (_,((h1,h2,h3),s,_)) -> h1 ^ h2 ^ h3 ^ s) block))
	  ^ "end.\n\n" in
      String.concat "" (List.map print_block sorting)

  | Twf _ ->
      (* PLACEHOLDER CODE *)
      let print_block block = 
	""
	^ (String.concat "" (List.map (fun (_,((h1,h2,h3),_,_)) -> h1^h2^h3) block))
        (* ^ "\n" *)
	^ "\n" 
	^ (String.concat "" (List.map (fun (_,(_,s,_)) -> s) block))
        ^ "\n" 
	 in
      String.concat "" (List.map print_block sorting)

  | Caml _ ->
      let print_block block =
	if ((List.length block) = 1) 
	then 
	  let (nt,((h1,h2,h3),s,_)) = List.hd block in
	  if (List.mem nt refl) 
	  then "let rec " ^ h1 ^ h2 ^ h3 ^ s ^ "\n\n" 
	  else "let " ^ h1 ^ h3 ^ s ^ "\n\n"
	else
	  "let rec "
	  ^ (String.concat "and\n" 
               (List.map (fun (_,((h1,h2,h3),s,_)) -> h1 ^ h2 ^ h3 ^ s) block))
	  ^ "\n\n" in
      String.concat "" (List.map print_block sorting)

  | Lem _ ->
      let print_block block =
        lemTODO "7" (
	if ((List.length block) = 1) 
	then 
	  let (nt,((h1,h2,h3),s,_)) = List.hd block in
	  if (List.mem nt refl) 
	  then "let rec " ^ h1 ^ h2 ^ h3^ s ^ "  end\n\n" 
(*	  then "let rec " ^ h1 ^"GOO1"^ h2^"GOO2" ^ h3^"GOO3" ^ s ^ "  end\n\n" *)
	  else "let " ^ h1 ^ h3 ^ s ^ "  end\n\n"
	else
	  "let rec "
	  ^ (String.concat "and\n" 
(*               (List.map (fun (_,((h1,h2,h3),s,_)) -> h1 ^ "FOO1" ^ h2 ^ "FOO2"^ h3 ^ "FOO3"^s) block))*)
               (List.map (fun (_,((h1,h2,h3),s,_)) -> h1 ^ h2 ^ h3 ^ s ^ "  end\n") block))
	  ^ "\n") in
      String.concat "" (List.map print_block sorting)

(* *** all together *)

let compute m xd (funcs:int_funcs_collapsed) =
  print m xd (sort funcs)

