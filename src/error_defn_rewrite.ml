open Types


(* If defn has relevant homs then
      Create new defn and signature
      For each rule
           Output positive version of rule with new signature
           For each premise
              If premise has a hom
                 Output new rule using premises < this one in their positive mode and then current premise/formula in neg mode
                        conclusion is negative
              If premise is a dotted form ..              
 *)

let rewrite_defn d =
  { d with d_rules = List.map (fun srr -> match srr with
                                          | PSR_Rule dr -> Printf.eprintf "Rule=%s\n" dr.drule_name;
                                                           List.iter (fun h -> Printf.eprintf "Hom\n") dr.drule_homs;
                                                           List.iter (fun (p,st,hl) -> Printf.eprintf "st=%s\n" (Grammar_pp.pp_plain_symterm st);
                                                                                    match p with
                                                                                    | Some s -> Printf.eprintf " s=%s\n" s
                                                                                    | None -> Printf.eprintf " none\n" ) dr.drule_premises;
                                                           srr
                                          | _ -> srr) d.d_rules }

       
let process_defn d =
  let ok_hom = List.assoc "fail_ok" d.d_homs in
  let error_hom = List.assoc "fail_error" d.d_homs in
  let fail_hom = List.assoc "fail" d.d_homs in
  match (ok_hom, error_hom, fail_hom) with
    ([],[],[]) -> d
  | (ok_hom::[],error_hom::[], fail_hom::[]) -> rewrite_defn d fail_hom
  | (_,_,_) -> raise (Invalid_argument "Incorrect fail_ok and fail_error hom specification")

let do_rewrite sd = 
  let new_rel = List.map (fun rd -> match rd with
                              | FDC fd -> rd
                              | RDC dc -> RDC { dc with dc_defns = List.map rewrite_defn dc.dc_defns } ) sd.relations
  in
  { sd with relations = new_rel }
