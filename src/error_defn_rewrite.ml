open Types


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
  with Not_found -> None

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
       
let rewrite_st_ok xd rdm st : string = 
    let (St_node (_,stnb)) = st in
    if stnb.st_prod_name = "formula_judgement" then 
      let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
      let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
      Printf.eprintf "es len %d\n" (List.length stnb.st_es);
      let (hom,_) = List.assoc "type" rdm in
      String.concat " " (walk_st xd stnb.st_es hom)
    else
      Grammar_pp.pp_symterm Isa_rules_rewrite.m_ascii xd [] de_empty st

let rewrite_st_fail xd rdm st err_reason : string =
  Printf.eprintf "rewrite_st_fail st=%s\n" (Grammar_pp.pp_plain_symterm st); 
  let (St_node (_,stnb)) = st in
  match stnb.st_prod_name with 
  | "formula_judgement" ->
      let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
      let [Ste_st (_,St_node(_,stnb))] = stnb.st_es in
      let (_,hom) = List.assoc "type" rdm in
      String.concat " " ((walk_st xd stnb.st_es hom) @ [err_reason])
  | "formula_dots" -> Grammar_pp.pp_symterm Isa_rules_rewrite.m_ascii xd [] de_empty st
  | _ -> 
      let p = Auxl.prod_of_prodname xd stnb.st_prod_name in
      let Some [Hom_string fail_prod] = find_hom p.prod_homs "fail_error" in
      let p = Auxl.prod_of_prodname xd ("formula_" ^ fail_prod) in
      let (Some s) = Grammar_pp.pp_elements Isa_rules_rewrite.m_ascii  xd [] p.prod_es true true true true  in
      s

let rec prefix_list xs prefix = match xs with
    [] -> []
  | x :: xs -> ( (prefix , x ) :: (prefix_list xs (prefix @ [x] )))
       
let rewrite_rule fd xd rdm (PSR_Rule d) =
  let c = rewrite_st_ok xd rdm d.drule_conclusion in
  let rule_name = d.drule_name in 
  List.iter (fun (_,p,_) -> let p = rewrite_st_ok xd rdm p in
                      Printf.fprintf fd "%s\n" p) d.drule_premises;
  Printf.fprintf fd "-------------- :: %s\n" rule_name;
  Printf.fprintf fd "%s\n\n" c;

  List.iter (fun (prefix,(_,p,homs)) ->
      List.iter (fun (_,p,_) -> let p = rewrite_st_ok xd rdm p in
                                Printf.fprintf fd "%s\n" p) prefix;
      let p = rewrite_st_fail xd rdm p "err_reason" in
      Printf.printf "Homs for p length=%d\n" (List.length homs);
      let hom = (match find_hom homs "fail" with
        | None -> "err_reason"
        | Some [ Hom_string hom ] -> hom) in
      let c = rewrite_st_fail xd rdm d.drule_conclusion hom in
      Printf.fprintf fd "%s\n" p;
      Printf.fprintf fd "-------------- :: %s\n" (rule_name ^ "_" ^ hom);
      Printf.fprintf fd "%s\n\n" c) (prefix_list d.drule_premises [])
  

                 

                     
       
let rewrite_defn fd sd rdm d [(Hom_string prod)] =
  Printf.fprintf fd "defn\n%s :: :: type_fail :: type_fail_\nby\n" prod;
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
  Printf.eprintf "%s\n" (Isa_rules_rewrite.pp_relations new_rel);
  sd

