open Types
open Grammar_rewrite
open Isa_rules_rewrite

(* Use original rules for positive part of rules ?

 *)

       
       
(* For each defn that has relevant homs then
     Add map from defn to new signature [*]


   For each defn that has relevant homs then
      Output new defn and signature
      For each rule
           -- Output positive version of rule with new signature 
             For each premise
                  If has postive/negative [lookup in map * ], then output positive version
                  Else output same
             For conclusion
                  Output positive

           -- Output error rules for each premise
           For each premise
              If premise has a hom
                 Output new rule using premises < this one in their positive mode and then current premise/formula in neg mode
                        conclusion is negative
              If premise is a dotted form ..              
 *)

(* Get the naming of the typing judgement we have 
   Use rdm to find ok hom for st; 
   Walk over hom and st in step and generate string for new st
   Write it out

   Example conclusion st
     (St_node :formula:formula_judgement: 
      (Ste_st 
        (St_node :judgement:judgement_typing: 
         (Ste_st 
          (St_node :typing:type: 
           (Ste_st (St_nonterm G))                         --> Hom index 0
           (Ste_st (St_node :t:t_Var: (Ste_metavar x)))    --> Hom index 1
           (Ste_st (St_nonterm T)))))))                    --> Hom index 2


 *)

let find_hom homs name =
  try
    Some (List.assoc name homs)
  with Not_found ->
    Printf.eprintf "find_hom Not Found %s\n" name ;
    None

let pp_plain_hom hs = String.concat " " (List.map (fun h -> match h with
                                                        | Hom_string _ -> "Hom_string "
                                                        | Hom_index i -> "Hom_index " ^ (string_of_int i)
                                                        | Hom_terminal _ -> "Hom_termina ") hs)

       
let rec walk_st xd (sts : symterm_element list) (hs : hom_spec ) = match (sts,hs) with
  | (  (Ste_st (_,st)  as ste) :: sts , (Hom_index _ ) :: hs ) ->
     (Grammar_pp.pp_symterm Isa_rules_rewrite.m_ascii  xd [] de_empty st) :: walk_st xd sts hs
  | ( _ , (Hom_string s :: hs) ) -> s :: (walk_st xd sts hs)
  | (_,[]) -> []


(*
      let p = Auxl.prod_of_prodname xd formula_name
      let fail_prod = Get fail prod name from p.hom
      let p = Auxl.prod_of_prodname xd fail_prod
 *)    


(* Not needed ? *)
let create_err_prod sd = 
  let st = St_node(dummy_loc, { st_rule_ntr_name = "typing";
                                st_prod_name = "type_err";
                                st_es = [];
                                st_loc = dummy_loc 
             } ) in 
  let new_prod = create_defn_prod "typing" "type_err" st in
  let xd = update_grammar_rules sd.syntax  [ ("typing", [new_prod]) ] in
  { sd with syntax = xd }


let rewrite_st_ok_original xd rdm st : string = 
  Grammar_pp.pp_symterm Isa_rules_rewrite.m_ascii xd [] de_empty st

                
let rewrite_st_ok xd rdm st : string = 
    let (St_node (_,stnb)) = st in
    if stnb.st_prod_name = "formula_judgement" then 
      let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
      let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
      Printf.eprintf "stnb.st_es len=%d stnb.st_prod_name=%s\n" (List.length stnb.st_es) stnb.st_prod_name;
      let (hom,_) = List.assoc stnb.st_prod_name rdm in
      String.concat " " (walk_st xd stnb.st_es hom)
    else
      Grammar_pp.pp_symterm Isa_rules_rewrite.m_ascii xd [] de_empty st

let delist_dot_form (St_node (_,stnb)) =
 let [ Ste_list (_, [ stli ] ) ] = stnb.st_es in
 let Stli_listform stlb  = stli in
 let [ Ste_st (_,st) ] = stlb.stl_elements in
 map_st { id_mf with f_nt = fun (ntr,nt) -> (ntr, strip_index_suffix nt) } st

let renumber_bound b = match b with
  | Bound_dotform bd -> Bound_dotform { bd with bd_upper = Si_var ("k",0) }
  | _ -> b
 

let renumber_dot_form_map_fn = { id_mf
                               with
                                 f_nt = (fun (ntr,(_,suff)) ->
                                 if has_index_suffix suff then
                                   (ntr, (ntr, (Si_punct "'") :: suff))
                                 else
                                   (ntr,(ntr,suff)));
                                 f_mv = (fun (ntr,(_,suff)) ->
                                   if has_index_suffix suff then
                                     (ntr, (ntr, (Si_punct "'") :: suff))
                                   else
                                     (ntr,(ntr,suff)));
                                 f_stlb = fun stlb -> { stlb with stl_bound = renumber_bound stlb.stl_bound  }
                               }
                                 
let renumber_dot_form st = map_st renumber_dot_form_map_fn st

(* Replace St_nonterm t with
    St_node either_error  [Ste_st (St_nonterm t)] 
 *)
let rewrite_st_dot_form xd rdm (st : symterm ) =
  let st = map_st { id_mf with f_st  = fun st ->
                              match st with
                              | St_node (l,stnb) ->
                                 if stnb.st_prod_name = "type" then (
                                   Printf.eprintf "found type node %s\n" stnb.st_prod_name;
                                   let stnb = { stnb with st_es =
                                                            map_stes { id_mf with f_st = fun st ->
                                                                                         Printf.eprintf "here\n";
                                                                                         match st with
                                                                                         | St_nonterm (l,ntr,nt) when ntr="T" ->
                                                                                            St_node(l, { st_rule_ntr_name = "either_error";
                                                                                                         st_prod_name = "Either_error_ok";
                                                                                                         st_es = [Ste_st (l,st)];
                                                                                                         st_loc = l })
                                                                                         | _ -> st 
                                                              } stnb.st_es 
                                              } in
                                   St_node (l,stnb)
                                 ) else st
                              | _ -> st    }  st
  in Grammar_pp.pp_symterm Isa_rules_rewrite.m_ascii  xd [] de_empty st

                                  
(* Splits judgement dot form into 'short circuit' form where the last one has an error *)                                  
let rec rewrite_dot_form xd rdm st err_reason =
  let premise1 = rewrite_st_dot_form xd rdm st in
  let premise2 = rewrite_st_fail xd rdm (delist_dot_form st) err_reason in
  String.concat "\n" [premise1; premise2 ]

and split_a_listform stlis = List.concat
  (List.map (
    fun stli -> match stli with
                | Stli_single _ -> [stli]
                | Stli_listform stlb -> [stli;
                                         Stli_single (dummy_loc,
                                                      map_stes { id_mf with
                                                          f_nt = (fun (ntr,nt) -> (ntr, strip_index_suffix nt));
                                                          f_mv = (fun (ntr,nt) -> (ntr, strip_index_suffix nt))
                                                        } stlb.stl_elements);
                                         map_stli renumber_dot_form_map_fn stli
                                        ]
     )
     stlis)
                
and split_listforms st = map_st { id_mf with f_ste_list = split_a_listform } st
                
and  rewrite_st_fail xd rdm st err_reason : string =
  Printf.eprintf "rewrite_st_fail st=%s\n" (Grammar_pp.pp_plain_symterm st); 
  let (St_node (_,stnb)) = st in
  match stnb.st_prod_name with 
  | "formula_judgement" ->
     let st = split_listforms st in
     let (St_node (_,stnb)) = st in
     let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
     let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
     let (_,hom) = List.assoc stnb.st_prod_name rdm in
     String.concat " " ((walk_st xd stnb.st_es hom) @ [err_reason])
  | "formula_dots" -> rewrite_dot_form xd rdm st err_reason
  | _ -> 
      let p = Auxl.prod_of_prodname xd stnb.st_prod_name in
      let Some [Hom_string fail_prod] = find_hom p.prod_homs "fail_error" in
      let p = Auxl.prod_of_prodname xd ("formula_" ^ fail_prod) in
      let (Some s) = Grammar_pp.pp_elements Isa_rules_rewrite.m_ascii  xd [] p.prod_es true true true true  in
      s

let rec prefix_list xs prefix = match xs with
    [] -> []
  | x :: xs -> ( (prefix , x ) :: (prefix_list xs (prefix @ [x] )))

let hom_prefix hom =
  Printf.eprintf "hom=<%s>\n" hom;
  let re = Str.regexp "\\([a-zA-Z_]+\\).*" in
  if not (Str.string_match re hom 0) then "XX"
  else Str.matched_group 1 hom
    
                 
let rewrite_rule fd xd rdm (PSR_Rule d) =

  let rule_name = d.drule_name in 
  (* Positive Rule *)
  (* Leave this for the original rules
  let c = rewrite_st_ok xd rdm d.drule_conclusion in
  List.iter (fun (_,p,_) -> let p = rewrite_st_ok xd rdm p in
                      Printf.fprintf fd "%s\n" p) d.drule_premises;
  Printf.fprintf fd "-------------- :: %s\n" rule_name;
  Printf.fprintf fd "%s\n\n" c;
   *)

  (* Fail Rules *)
  List.iter (fun (prefix,(_,p,homs)) ->

      (* Add a rule for each premise with a fail hom *)
      match find_hom homs "fail" with
      | None -> ()
      | Some _ -> 
         List.iter (fun (_,p,_) -> let p = rewrite_st_ok_original xd rdm p in
                                   Printf.fprintf fd "%s\n" p) prefix;
         let p = rewrite_st_fail xd rdm p "err_reason" in (* FIXME *)
         Printf.printf "Homs for p length=%d\n" (List.length homs);
         let hom = (match find_hom homs "fail" with
                    | None -> "err_reason"
                    | Some [ Hom_string hom ] -> hom) in
         let c = rewrite_st_fail xd rdm d.drule_conclusion hom in
         Printf.fprintf fd "%s\n" p;
         Printf.fprintf fd "-------------- :: %s\n" (rule_name ^ "_" ^ (hom_prefix hom) );
         Printf.fprintf fd "%s\n\n" c) (prefix_list d.drule_premises [])
  
let rewrite_defn fd sd rdm d [(Hom_string prod)] =
  Printf.fprintf fd "defn\n%s :: :: %s_fail :: %s_fail_\nby\n" prod d.d_name d.d_name ;
  List.iter (rewrite_rule fd sd.syntax rdm) d.d_rules;
  d

                      
let rewrite_defn_map sd = List.concat (List.map (fun rd ->
       match rd with
         FDC fd -> []
       | RDC dc -> List.concat (List.map (fun d ->
                                    match (find_hom d.d_homs "fail_ok", find_hom d.d_homs "fail_error") with
                                    | (Some h1,Some h2) -> Printf.eprintf "Len hom =%d hom=%s\n" (List.length h1) (pp_plain_hom h1);
                                                [(d.d_name, (h1,h2))]
                                    | _ -> []) dc.dc_defns)) sd.relations)
  
  
                      
let process_defn fd sd rdm d =
  let ok_hom = find_hom d.d_homs "fail_ok"  in
  let error_hom = find_hom d.d_homs  "fail_error" in
  let fail_hom = find_hom d.d_homs "fail"  in
  match (ok_hom, error_hom, fail_hom) with
    (None,None,None) -> d
   | (Some ok_hom, Some error_hom, Some fail_hom) -> rewrite_defn fd sd rdm d fail_hom
   | (_,_,_) -> raise (Invalid_argument "Incorrect fail_ok and fail_error hom specification")

let do_rewrite sd =
  let fd = open_out "err.ott" in
  Printf.fprintf fd "defns\ntyping_fail :: '' ::=\n\n";
  let rdm = rewrite_defn_map sd in
  let new_rel = List.map (fun rd -> match rd with
                              | FDC fd -> rd
                              | RDC dc -> RDC { dc with dc_defns = List.map (process_defn fd sd rdm ) dc.dc_defns } ) sd.relations
  in
  let sd = { sd with relations = new_rel } in
  (*Printf.eprintf "** Rewritten Rules **\n%s\n" (Isa_rules_rewrite.pp_relations sd.syntax new_rel);*)
  sd

