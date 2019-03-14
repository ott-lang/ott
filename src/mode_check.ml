
(* Example use: make ott.opt && ./ott -mode_check GtT_i_i_i  ../tests/test10st.ott 
   Create a DOT file tmp.dot that can be converted to PDF with
   dot -Tpdf tmp.dot -o tmp.pdf

   PDF shows a graph with nodes corresponding to judgements annotated with a mode and arcs from a node to 
   other nodes that it is dependent on. Nodes with a * have failed mode analysis. Stdout will show details of 
   mode analysis and indicate the rule(s) that fail mode analysis.

   The output of this analysis can be used to check before loading the rules into a backend, such as
   Isabelle, and avoiding the wait whilst the backend processes the file and to provide more useful information than
   the error reporting from the backend.

   Limitations/Bugs:
     Mode checking infer_pat_typ is a false negative. Somehow it needs to realise that x!0 and x_list are the same.
*)

open Types;;
module SS = Set.Make(String);;
module G = Graph.Imperative.Digraph.Abstract(struct type t = string end)

type mode = InMode | OutMode
                                            
module Display = struct
  include G
  let vertex_name v = "\"" ^ String.escaped (V.label v) ^ "\""
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end
module DotOutput = Graph.Graphviz.Dot(Display)

let mode_as_string m = String.concat " " (List.map (fun m -> match m with
                                                       | InMode -> "in "
                                                       | OutMode ->"out ") m)

                                     
module DefnMode = struct
  type t = string* (mode list)
  let compare (s1,m1) (s2,m2) =
    let f s m = s ^ " " ^ (mode_as_string m) in
    let u1 = f s1 m1 in
    let u2 = f s2 m2 in
    compare u1 u2
      
end                                     
module PSet = Set.Make( DefnMode )

let allowed_modes = ref (PSet.of_list [])
                            
                                            
let show g =
  let oc = open_out "tmp.dot" in
  DotOutput.output_graph oc g;
  close_out oc

let contains s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

             
let suffix_as_string s = String.concat "" (List.map (fun si -> match si with
                                                               | Si_num n -> Printf.sprintf "#%s" n 
                                                               | Si_punct p-> p 
                                                               | Si_var (sv,_) -> sv
                                                               | Si_index i -> Printf.sprintf "!%d" i
                                                    ) s)

(* Apply f to each element in the list with the first one that returns Some being the result *)                                       
let foldOption ( f : 'b -> 'a option)  (xs : 'b list ) : 'a option = List.fold_left (fun x y -> match x with
                                                                                                | Some _ -> x
                                                                                                | None -> f y) None xs
                                                                                    
let not_formula_judgement nb =
  let v = (not (contains nb.st_prod_name "judgement")) && (nb.st_prod_name <> "formula_dots") in
          v


(* Find in st the first thing satisfying g and apply f to it *)                                        
let rec find_apply st g f = match st with
  | St_node (_, nb) -> if g nb  then f nb else foldOption (fun ste -> find_apply_ste ste g f) nb.st_es
  | _ -> None
and find_apply_stli stli g f = match stli with
  | Stli_single (_, stes) -> foldOption (fun ste -> find_apply_ste ste g f) stes
  | Stli_listform stli_body -> foldOption (fun ste -> find_apply_ste ste g f) (stli_body.stl_elements)
and find_apply_ste ste g f = match ste with
  | Ste_st (_,st) -> find_apply st g f
  | Ste_list (_, stlis) -> foldOption (fun stli -> find_apply_stli stli g f) stlis
  | _ -> None

                                       
let compute_dependencies sd =

  let dep_for sd d =
    let process_rule r = match r with
      | PSR_Rule r -> List.concat (List.map (fun (_,st,_) ->
                                       let f = (fun nb -> Some nb.st_prod_name) in
                                       match find_apply st not_formula_judgement f with
                                       | Some x -> [x]
                                       | None -> [] )  r.drule_premises)
      | _ -> []
    in SS.of_list (List.concat (List.map process_rule d.d_rules)) in
  
  (* auxiliary function on graphs *)
  let add_vertex_for g i d=  
    let vertex = G.V.create d.d_name in
    i := (vertex, (d.d_name, d))::!i;
    G.add_vertex g vertex in

  (* we rely on the simplest graphs provided by ocamlgraph, and we
     explicitly record the association vertex_identifier -> nonterminal
     list + metavar list *) 
  let g = G.create () in let g_vertex_info,
    g_vertex_count = ref [], ref 0 in

    let vertex_associated_to_defn dname =
      try
        Some (fst (List.find (fun (_,(n,_)) -> dname = n) !g_vertex_info))
      with Not_found -> None in

  let defs = 
    List.concat (List.map (fun r -> match r with
                       | FDC _ -> []
                       | RDC dc -> dc.dc_defns ) sd.relations) in

  let add_dep_edges g (vertex,(_,d)) =
    let deps = dep_for sd d in
    List.iter (fun d2 -> match vertex_associated_to_defn d2 with
                         | Some v2 -> G.add_edge g vertex v2
                         | None -> ())  (SS.elements deps) in
                       
  List.iter (add_vertex_for g g_vertex_info) defs;
  List.iter (add_dep_edges g ) !g_vertex_info;
  show g

let pp_plain_drule (dr:drule) : unit =
  print_endline ("&*"^dr.drule_name); 
  print_endline (String.concat "\n" (List.map Grammar_pp.pp_plain_symterm (List.map (fun (_,st,_) -> st) dr.drule_premises)));  
  print_endline (Grammar_pp.pp_plain_symterm dr.drule_conclusion)


       
let pp_sd  sd =
  let rec pp_st_element ste = match ste with
    | Ste_st (_,st) -> pp_symterm st
    | Ste_metavar (_, mvroot, (_,suff)) -> Printf.printf " mvar[%s%s] " mvroot (suffix_as_string suff)
    | Ste_var (_, _, _)-> Printf.printf " var "
    | Ste_list (_, sts) -> Printf.printf " <  "; List.iter pp_st_list_item sts; Printf.printf " >"
  and pp_st_list_item stli = match stli with
    | Stli_single (_, stes ) -> List.iter pp_st_element stes
    | Stli_listform stli_body -> List.iter pp_st_element (stli_body.stl_elements)
  and pp_symterm st = match st with
      | St_node (_,nb) -> Printf.printf " %s( " nb.st_prod_name ; List.iter pp_st_element nb.st_es; Printf.printf " ) "
      | St_nonterm (_,ntroot,(_,nts))  -> Printf.printf " nt[%s%s]" ntroot (suffix_as_string nts)
      | St_nontermsub _  -> Printf.printf " nts "
      | St_uninterpreted (_,s)  -> Printf.printf "ut[%s] " s
  in
    let pp_rule srr = match srr with
      | PSR_Rule dr -> pp_plain_drule dr ; Printf.printf "  %s " dr.drule_name;
                       Printf.printf "  Premises: ";
                       List.iter (fun (_,s,_) -> pp_symterm s) dr.drule_premises ; Printf.printf "\n";
                       Printf.printf "  Conclusion: "; pp_symterm dr.drule_conclusion; Printf.printf "\n"
       | PSR_Defncom es -> Printf.printf "  defncom\n" in
    let pp_defn d = Printf.printf "Defn Name: %s \n" d.d_name;
                    Printf.printf "     Form: "; pp_symterm d.d_form; Printf.printf "\n";
                    List.iter pp_rule d.d_rules in
    let pp_defnclass dc = Printf.printf "RDC %s " dc.dc_name;
                          List.iter pp_defn dc.dc_defns
    in
      List.iter (fun r -> match r with
         | FDC _ -> Printf.printf "FDC\n"
         | RDC dc -> pp_defnclass dc
                            ) sd.relations




let rec zip (xs:'a list) (ys:'b list) : ('a*'b) list = match (xs,ys) with
  | ( x::xs , y::ys ) -> (x,y)::(zip xs ys)
  | ([],_) -> []
  | (_,[]) -> []



let concat_set c s = SS.fold (fun x y -> x^c^y)  s ""

(* For a given definition, list of defn it depends on and their modes *)
module DefMap = Map.Make(String)                                   

                        
let pp_mode m = Printf.printf "< %s >" (mode_as_string m)
    
let check_defn d mode =

  let def_list = ref DefMap.empty in
  let def_pass = ref true in
  let add_required_mode name mode =
    let m = ! def_list
    in
    let new_m = 
      try
        let ms = DefMap.find name m
        in DefMap.add name (mode::ms) m
      with Not_found -> DefMap.add name [mode] m
    in def_list := new_m in

  let allowed_name_mode name mode =
    if (List.mem name (List.map fst (PSet.elements !allowed_modes))) then
      PSet.mem (name,mode) (!allowed_modes)
    else
      true
  in
  
  let rec free_vars_ste ste = match ste with
    | Ste_st (_,st) -> free_vars_aux st
    | Ste_metavar (_,mvroot,(_,suff)) -> [ mvroot^(suffix_as_string suff) ]
    | Ste_var (_,mvroot,var) -> [ mvroot^var ]
    | Ste_list (_,stlis) -> List.concat (List.map free_vars_stli stlis)
  and free_vars_stli stli = match stli with
    | Stli_single (_, stes ) -> List.concat (List.map free_vars_ste stes)
    | Stli_listform stli_body -> List.concat (List.map free_vars_ste (stli_body.stl_elements))
  and free_vars_aux st = match st with
    | St_node (_,nb) -> List.concat (List.map free_vars_ste  nb.st_es)
    | St_nonterm (_,ntroot,(ntr,nts))  -> [ ntr ^(suffix_as_string nts) ]
    | _ -> [] in
  let free_vars st = SS.of_list (free_vars_aux st) in
  let calc_invars mode st = 
    let f = (fun nb -> Some (List.concat (List.map (fun (mode,ste) -> if mode = InMode then free_vars_ste ste else []) (zip mode nb.st_es))))
    in match find_apply st not_formula_judgement f with
       | Some x -> SS.of_list x
       | None -> SS.empty
  in
  let process_premise p in_vars =
    Printf.printf "  Premise: invars = %s\n" (concat_set "," in_vars);
    let (name, mode) = let f = (fun nb -> Some (nb.st_prod_name, List.map (fun ste ->
                                                                     (*Printf.printf "Premise: free vars in st %s\n" (String.concat  "," (free_vars_ste ste));*)
                                                                     if SS.subset (SS.of_list (free_vars_ste ste)) in_vars then InMode else OutMode) nb.st_es))
               in match find_apply p not_formula_judgement f with
                  | Some x -> x
                  | None -> ("?",[]) in
    (if allowed_name_mode name mode then (
      Printf.printf "  Premise: %s Required mode: " name; pp_mode mode; Printf.printf " Ok \n";
      add_required_mode name mode
    ) else
      (Printf.printf "  Premise: %s Required mode: " name; pp_mode mode; Printf.printf " Fail (Not allowed)\n"));
    let known_vars = free_vars p
    in known_vars
  in
  let process_rule mode r = match r with
    | PSR_Rule r ->
       let in_vars = calc_invars mode r.drule_conclusion in
       Printf.printf "Rule: %s\n  Conc: freevars=%s invars=%s\n" r.drule_name (concat_set ", " (free_vars r.drule_conclusion)) (concat_set ", " in_vars); 
       List.iter (fun (_,p,_) -> Printf.printf "  Premise vars: %s\n" (concat_set ", " ( free_vars p))) r.drule_premises;
       let known_vars = List.fold_left (fun vars (_,p,_) -> SS.union (process_premise p vars) vars) in_vars r.drule_premises in
       let ok = SS.subset (free_vars r.drule_conclusion) known_vars in
       if not ok then def_pass := false;
       Printf.printf "  Known vars  : %s %s\n" (concat_set ", " known_vars) (if ok then " Pass " else " Fail ")
    | _ -> ()
  in
  let fv = free_vars d.d_form (* in
  let mode = match mode with
    | None -> List.map (fun _ -> InMode) (match d.d_form with
                                          | St_node (_, nb) -> nb.st_es
                                          | _ -> [] )
    | Some x -> x                   *)
  in Printf.printf "Definition: %s\n" d.d_name;
     Printf.printf "Argument terms: %s\n" (concat_set ", " fv);
     Printf.printf "Checking mode: "; pp_mode mode; Printf.printf "\n";
     List.iter (fun r -> process_rule mode r) d.d_rules;
     (!def_list,!def_pass)




let defn_by_name sd name =
  Printf.printf "defn_by_nme <%s>\n" name;
  match (List.concat (List.map (fun r -> match r with
                      | FDC _ -> []
                      | RDC dc -> List.concat (List.map (fun d -> if d.d_name = name then [d] else []) dc.dc_defns) 
                               ) sd.relations)) with
  | x::xs -> Some x
  | [] -> None

let rec unfoldr (f : 'b -> ('a*'b) option) (x:'b) : 'a list  =
  match f x with
  | None -> []
  | Some (a,b) -> (unfoldr f b) @ [a]

module DefMapFull = Map.Make(String)                                   

let create_graph def_map_full =
    let g = G.create () in
  let g_vertex_info = ref [] in

  let vertex_associated_to_defn label =
    try
        Some (fst (List.find (fun (_,label2) -> label = label2) !g_vertex_info))
    with Not_found -> None
  in

  let mode_as_string2 m = match m with
      | None -> "all_in"
      | Some m -> mode_as_string m
  in

  let add_vertex_tag g lab tag i =
    match vertex_associated_to_defn lab with
    | Some _ -> ()
    | None ->               
       let vertex = G.V.create (lab^tag) in 
       i := (vertex, lab)::!i
  in
  
  let add_vertex g name mode i = add_vertex_tag g (name ^ " " ^ (mode_as_string mode)) "" i
  in

  let add_edge g l1 n2 m2 = 
    let l2 = (n2 ^ " " ^ (mode_as_string m2)) in
    match (vertex_associated_to_defn l1,vertex_associated_to_defn l2) with
      | (Some v1,Some v2) -> G.add_edge g v1 v2
      | _ -> Printf.printf "Cannot find '%s' or '%s' in graph\n" l1 l2                                  
  in

  (* Build the graph. First the vertices and then the edges *)
  List.iter (fun (label, (dmap,pass)) ->
      let tag = if pass then "" else " *" in
      add_vertex_tag g label tag g_vertex_info;
    ) (DefMapFull.bindings !def_map_full);

  List.iter (fun (label, (dmap,pass)) ->
      let deps = (List.concat (List.map (fun (k,v) -> List.map (fun m -> (k,m)) v)  ((DefMap.bindings) dmap))) in
      List.iter (fun (name2, mode2) -> add_vertex g name2 mode2 g_vertex_info; add_edge g label name2 mode2 ) deps
    ) (DefMapFull.bindings !def_map_full);
  
  show g

let read_lines file =
  let in_ch = open_in file in
  let rec read_line acc  =
    try
      let line = input_line in_ch in
      read_line (acc@[line] )
    with End_of_file -> acc
  in read_line []
       
  
(* Performs mode analysis of inductive rule graph starting with mode annotated defn_name *)       
let do_check sd file_name =

  let fixed_modes = read_lines file_name in

  Printf.printf "Lines: %s\n" (String.concat " " fixed_modes );
  
  let (defn_name :: _ ) = fixed_modes in 
  
  pp_sd sd;
  compute_dependencies sd;

  (* Extract definition name and mode list from string *)
  let calc_name_mode name_mode =
    let re = Str.regexp "_[io]" in
    let f i =
      if i<1 then
        None
      else if (String.get name_mode i = 'i') && ((String.get name_mode (i-1)) = '_') then
        Some (InMode,i-2)
      else if String.get name_mode i = 'o' && String.get name_mode (i-1) = '_' then
        Some (OutMode,i-2)
      else
        None
    in      
    let mode = unfoldr f ((String.length name_mode) - 1) in
      (String.sub name_mode 0 ((String.length name_mode) - (List.length mode)*2),mode)
  in                  
    
  let (defn_name,mode) = calc_name_mode defn_name in                
  let processed = ref PSet.empty in
  let to_process = ref (PSet.of_list [ (defn_name,mode) ])   in
  allowed_modes := PSet.of_list (List.map calc_name_mode fixed_modes);
  
  let def_map_full = ref DefMapFull.empty in

  (* Process definitions until there are none left to process *)
  while not (PSet.is_empty !to_process) do
    let (defn_name,mode) = PSet.choose !to_process in
    to_process := PSet.remove (defn_name,mode) !to_process;
    processed := PSet.add (defn_name,mode) !processed;
    match defn_by_name sd defn_name with
      | Some def ->  
             let (dmap,pass) = check_defn def mode in
             let new_to_process = (List.concat (List.map (fun (k,v) -> List.map (fun m -> (k,m)) v)  ((DefMap.bindings) dmap))) in

             def_map_full := DefMapFull.add (defn_name ^ " " ^ (mode_as_string mode)) (dmap,pass)  !def_map_full;
             to_process := PSet.diff (PSet.union !to_process (PSet.of_list new_to_process)) !processed
      | None -> ()
   done;

   create_graph def_map_full
