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
   
let rewrite_st rdm st : string = "<new st>" 
       
let rewrite_rule rdm (PSR_Rule d) =
  let c = rewrite_st rdm d.drule_conclusion in
  Printf.eprintf "new conc=%s" c

                     
       
let rewrite_defn sd rdm d [(Hom_string prod)] =
  Printf.printf "defn\n%s\nby\n" prod;
  List.iter (rewrite_rule rdm) d.d_rules;
  d

let find_hom homs name =
  try
    Some (List.assoc name homs)
  with Not_found -> None

let pp_plain_hom hs = String.concat " " (List.map (fun h -> match h with
                                                        | Hom_string _ -> "Hom_string "
                                                        | Hom_index i -> "Hom_index " ^ (string_of_int i)
                                                        | Hom_terminal _ -> "Hom_termina ") hs)
                      
let rewrite_defn_map sd = List.concat (List.map (fun rd ->
       match rd with
         FDC fd -> []
       | RDC dc -> List.concat (List.map (fun d ->
                                    match (find_hom d.d_homs "fail_ok") with
                                    | Some h -> Printf.eprintf "Len hom =%d hom=%s\n" (List.length h) (pp_plain_hom h); [(d.d_name, h)]
                                    | None -> []) dc.dc_defns)) sd.relations)
  
  
                      
let process_defn sd rdm d =
  let ok_hom = find_hom d.d_homs "fail_ok"  in
  let error_hom = find_hom d.d_homs  "fail_error" in
  let fail_hom = find_hom d.d_homs "fail"  in
  match (ok_hom, error_hom, fail_hom) with
    (None,None,None) -> d
   | (Some ok_hom, Some error_hom, Some fail_hom) -> rewrite_defn sd rdm d fail_hom
   | (_,_,_) -> raise (Invalid_argument "Incorrect fail_ok and fail_error hom specification")

let do_rewrite sd =
  let rdm = rewrite_defn_map sd in
  let new_rel = List.map (fun rd -> match rd with
                              | FDC fd -> rd
                              | RDC dc -> RDC { dc with dc_defns = List.map (process_defn sd rdm ) dc.dc_defns } ) sd.relations
  in
  let sd = { sd with relations = new_rel } in
  Printf.eprintf "%s\n" (Isa_rules_rewrite.pp_relations new_rel);
  sd

