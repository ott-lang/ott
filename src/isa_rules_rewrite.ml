
(* TODO
    Limitations
      1. Handles presence of subrules badly - internal error
      2. Handles using of secondary names for nonterms badly. ie if 
           label, l 
         then will won't find l_T_list; only label_T_list will have been used as name of label_T_list nonterm
 *)
open Types;;


let xd_ref = ref (None : syntaxdefn option)  

let rec unzip3 (xyzs : ('a * 'b * 'c) list ) : ( ('a list) * ('b list) * ('c list) )  = match xyzs with
  | [] -> ([],[],[])
  | ((x,y,z)::xyzs) -> let (xs,ys,zs) = unzip3 xyzs in (x::xs,y::ys,z::zs)

let rec unzip4 (s  : ('a * 'b * 'c * 'd) list ) : ( ('a list) * ('b list) * ('c list) * ('d list) )  = match s with
  | [] -> ([],[],[],[])
  | ((x,y,z,w)::s) -> let (xs,ys,zs,ws) = unzip4 s in (x::xs,y::ys,z::zs,w::ws)


                 
(*---------------------------------------------------------
 
   Facilities for mapping and folding over symterm trees

----------------------------------------------------------- *)  
                                           
type map_functions = {
    f_st : symterm -> symterm;
    f_stnb : symterm_node_body -> symterm_node_body;
    f_nt : (nontermroot*nonterm) -> (nontermroot*nonterm);
    f_mv : (metavarroot*metavar) -> (metavarroot*metavar);
    f_stlb : symterm_list_body -> symterm_list_body;
  }

let id_map_functions = {
    f_st = (fun x -> x);
    f_stnb = (fun x -> x);
    f_nt = (fun x -> x);
    f_mv = (fun x -> x);
    f_stlb = (fun x -> x)
  }

let rec map_st (f : map_functions) st = match st with
  | St_node (l,stnb) ->  St_node(l, { (f.f_stnb stnb) with st_es = List.map (map_ste f) stnb.st_es })
  | St_nonterm (l,ntr,nt) -> let (ntr,nt) = f.f_nt (ntr,nt) in St_nonterm(l,ntr,nt)
and map_ste (f : map_functions) ste = match ste with
  | Ste_st(l,st) -> Ste_st (l, map_st f st)
  | Ste_metavar(l,mvr,mv) -> let (mvr,mv) = f.f_mv (mvr,mv) in Ste_metavar(l,mvr,mv)
  | Ste_list (l,stlis) -> Ste_list(l,List.map (map_stli f) stlis)
and map_stli f stli = match stli with
  | Stli_single(l,stes) -> Stli_single(l,List.map (map_ste f) stes)
  | Stli_listform stlb -> Stli_listform (f.f_stlb stlb)
and map_stes f stes = List.map (fun ste -> map_ste f ste ) stes

                         
type 'a fold_functions = {
    f_st : symterm -> 'a -> 'a;
    f_stnb : symterm_node_body -> 'a -> 'a;
    f_stlb : symterm_list_body -> 'a -> 'a;
    f_ste : symterm_element -> 'a -> 'a;
    f_stli : symterm_list_item -> 'a -> 'a;
    f_nt : (nontermroot*nonterm) -> 'a -> 'a;
    f_mv : (metavarroot*metavar) -> 'a -> 'a;
  }


let rec fold_drule  (f : 'a fold_functions) (base : 'a) (dr : drule ) : 'a =
  let base = fold_st f base dr.drule_conclusion
  in List.fold_left (fun x (_, p) -> fold_st f x p) base dr.drule_premises
                           
and  fold_defnclass  (f : 'a fold_functions) (base : 'a) (dc : defnclass ) : 'a =
  List.fold_left (fun x d -> List.fold_left (fun x r -> match r with
                                                        | PSR_Rule dr -> fold_drule f x dr
                                                        | _  -> x) x d.d_rules) base dc.dc_defns

and  fold_rel (f : 'a fold_functions) (base : 'a) (rels : relationsdefn ) : 'a =
  List.fold_left (fun x r -> match r with
                             | FDC _ -> x
                             | RDC dc -> fold_defnclass f x dc) base rels
                          
and fold_st (f : 'a fold_functions) (base : 'a) (st : symterm) : 'a =
  let b = match st with
    | St_node (l,stnb) ->  fold_stes f base stnb.st_es
    | St_nonterm (l,ntr,nt) ->  f.f_nt (ntr,nt) base
    | St_nontermsub _ -> base
    | St_uninterpreted _ -> base
  in f.f_st st b
          
and  fold_ste (f : 'a fold_functions)  (base : 'a)  (ste : symterm_element) : 'a =
  let b = match ste with
    | Ste_st(l,st) -> fold_st f base st
    | Ste_metavar(l,mvr,mv) -> f.f_mv (mvr,mv) base
    | Ste_list (l,stlis) -> List.fold_left (fun b stli -> fold_stli f b stli) base stlis
  in f.f_ste ste b
           
and fold_stli f base stli =
  let b = match stli with
    | Stli_single(l,stes) -> List.fold_left (fun b ste -> fold_ste f b ste) base stes
    | Stli_listform stlb  -> fold_stes f base stlb.stl_elements
  in f.f_stli stli b

and fold_stes f base stes = List.fold_left (fun b ste -> fold_ste f b ste) base stes

let id_fold_functions = {
    f_st = (fun _ a -> a);
    f_stnb = (fun _ a -> a);
    f_nt  = (fun _ a -> a);
    f_mv  = (fun _ a -> a);
    f_stlb  = (fun _ a -> a);
    f_ste = (fun _ a -> a);
    f_stli = (fun _ a -> a);
  }

let rec map_drule  (f : drule -> drule)  (dr : drule ) : drule = f dr
                           
and  map_defnclass  (f : drule -> drule ) (dc : defnclass ) : defnclass =
  { dc with dc_defns = List.map (fun d -> { d with d_rules = List.map (fun r -> match r with
                                                                                      | PSR_Rule dr -> PSR_Rule (map_drule f dr)
                                                                                      | _  -> r ) d.d_rules }) dc.dc_defns}

and  map_rel (f : drule -> drule ) (rels : relationsdefn )  =
  List.map (fun r -> match r with
                             | FDC _ -> r
                             | RDC dc -> RDC (map_defnclass f dc)) rels

                          

type 'a syntax_fold_functions = {
         f_element : element -> 'a -> 'a
       }


let sd_id_fold_fn = {
    f_element = (fun _ a -> a)
  }
                                  
let rec fold_xd f b xd = List.fold_left (fun b r -> fold_rule f b r ) b xd.xd_rs

and fold_rule f b r = List.fold_left (fun b p -> fold_prod f b p ) b r.rule_ps

and fold_prod f b p = List.fold_left (fun b e -> f.f_element e b ) b p.prod_es

and fold_es f b es = List.fold_left (fun b e -> f.f_element e b ) b es
                          
(*-----------------------------------------------------------------------
  
   Adding new rules and productions

-------------------------------------------------------------------------*)
                          
let jdots_judgement stnb = if stnb.st_rule_ntr_name = "judgement" then stnb else stnb
                          
let jdots st = map_st { id_map_functions with f_stnb = jdots_judgement } st

let m_ascii = Ascii { ppa_colour = false; 
		      ppa_lift_cons_prefixes = false; 
		      ppa_ugly= false; 
		      ppa_show_deps = true; 
		      ppa_show_defns = false } 

  
let debugln s = Printf.eprintf s

let has_num_suffix suffix = (List.length (Auxl.option_map (fun s -> match s with Si_num _ -> Some s | _ -> None) suffix)) > 0
let has_index_suffix suffix = (List.length (Auxl.option_map (fun s -> match s with Si_index _ -> Some s | _ -> None) suffix)) > 0

                              
let pp_plain_prod p = "Prod: name: " ^ (p.prod_name) ^ (String.concat " " (List.map Grammar_pp.pp_plain_element p.prod_es))
  
let pp_plain_rule r = "Rule. name: " ^ (r.rule_ntr_name) ^ "\ntr_names:" ^ (String.concat " " (List.map (fun (s,_) -> s) r.rule_ntr_names)) ^ "\nProds: " ^ (String.concat "\n" (List.map (fun p -> pp_plain_prod p) r.rule_ps))

let rec unzip xs = match xs with
  | [] -> ([],[])
  | (x,y)::xys -> let (xs,ys) = unzip xys in (x::xs,y::ys)

let flatten_option xs = Auxl.option_map (fun x -> x) xs

let rec rem_dupsf xs f = match xs with
  | [] -> []
  | (x::xs) -> if List.exists (fun y -> f x y) xs then rem_dupsf xs f else (x::(rem_dupsf xs f))
                                        
let rec rem_dups xs = match xs with
  | [] -> []
  | (x::xs) -> if List.mem x xs then rem_dups xs else (x :: (rem_dups xs))

let rec map_sep (f : 'a -> 'b) (sep : 'b)  (xs : 'a list) : 'b list  = match xs with
  | [] -> [] 
  | [x] -> [f x]
  | x1::x2::xs -> (f x1) :: (sep :: (map_sep f sep (x2::xs)))
                                                        
let newprod nme es homs = { prod_name = nme;     
	               prod_flavour = Bar;
	               prod_meta = false;
	               prod_sugar = false;
                       prod_categories = StringSet.empty;
	               prod_es = es;
	               prod_homs = homs;
                       prod_disambiguate = None;
	               prod_bs = [];
                       prod_loc = dummy_loc }

    
(** Functions for creating new names **)                            
let extract_names es = Auxl.option_map (fun e -> match e with
                                          | Lang_nonterm (_,n) -> Some n
                                          | Lang_metavar (_,n) -> Some n
                                          | _ -> None ) es



                                
let as_string (ntvmr,suffix) = ntvmr ^ (Grammar_pp.pp_plain_suffix suffix)

let as_string_list (xs : (string * suffix_item list) list) : string =
  let suffs1 = List.concat (List.map snd xs) in
  let suffs2 = Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suffs1 in
  if suffs1 = suffs2 then
    (String.concat "_" (List.map fst xs)) ^ (Grammar_pp.pp_plain_suffix suffs2)
  else
    (String.concat "_" (List.map fst xs)) ^ "_list" ^ (Grammar_pp.pp_plain_suffix suffs2)

let as_list_ntmv (xs : (string * suffix_item list) list) : (string * suffix_item list) =
  let suffs1 = List.concat (List.map snd xs) in
  let suffs2 = Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suffs1 in
  if suffs1 = suffs2 then
    (String.concat "_" (List.map fst xs), suffs2 )
  else
    (String.concat "_" (List.map fst xs) ^ "_list" , suffs2)

                                                        
  

let strip_index2 (nt,suff) = (nt, Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suff)
                                         
let as_strings  es : string list = List.map (fun e -> as_string (strip_index2 e) ) (extract_names es)

let distinguish_dups es = List.mapi (fun i x -> match x with
                                                  Lang_nonterm (ntr1,(ntr2,suffx)) -> let ntr3 =  ntr1 ^ (string_of_int i)
                                                                                      in Lang_nonterm (ntr1,(ntr2,(Si_num (string_of_int i)) :: suffx))
                                                 | Lang_metavar (mvr1,(mvr2,suffx)) -> 
                                                                                      Lang_metavar (mvr1,(mvr2,(Si_num (string_of_int i)) :: suffx))) es
(* Given a symterm that is inside a formula_dots, create a call to auxilary predicate *)

(* Take a nonterm/metavariable and if it is an index variable convert it to a list *)                                    
let rename_mvnt (base, (root, suffix )) = let new_suffs = Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suffix in
                                  if suffix = new_suffs then
                                    (base ,(root,suffix))
                                  else
                                    (base ^ "_list" , (root ^ "_list", new_suffs))

                                    
let make_args_from_st (st : symterm ) : nontermroot list =
  fold_st { id_fold_functions with f_nt = (fun (ntr,nt) base -> let (r,_) = rename_mvnt (ntr,nt) in List.append base [r]);
                                   f_mv = (fun (ntr,nt) base -> let (r,_) = rename_mvnt (ntr,nt) in List.append base [r]) } [] st
          
let remove_index (suff : suffix ) : suffix  = Auxl.option_map (fun s -> 
                                                  match s with
                                                    Si_index _ -> None
                                                  | _ -> Some s) suff


(*----------------------------------------------------------------------

   Changing and add new definitions

------------------------------------------------------------------------*)


let rename_nt (base, (root, suffix )) = let new_suffs = Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suffix in
                                  if suffix = new_suffs then
                                    Lang_nonterm (base ,(root,suffix))
                                  else
                                    Lang_nonterm (base ^ "_list" , (root ^ "_list", new_suffs))

let rename_mv (base, (root, suffix )) = let new_suffs = Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suffix in
                                  if suffix = new_suffs then
                                    Lang_metavar (base ,(root,suffix))
                                  else
                                    Lang_nonterm (base ^ "_list" , (root ^ "_list", new_suffs))
                                                 
let rename_nt_as_st (base, (root, suffix )) = let new_suffs = Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suffix in
                                  if suffix = new_suffs then
                                    Ste_st(dummy_loc, St_nonterm (dummy_loc, base  , (root , suffix)))
                                  else
                                    Ste_st(dummy_loc, St_nonterm (dummy_loc, base ^ "_list" , (root ^ "_list", new_suffs)))

let rename_mv_as_st (base, (root, suffix )) = let new_suffs = Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suffix in
                                  if suffix = new_suffs then
                                    Ste_metavar(dummy_loc, base ,(root,suffix))
                                  else
                                    Ste_st(dummy_loc, St_nonterm (dummy_loc, base ^ "_list" , (root ^ "_list", new_suffs)))


                                                              
let make_empty_form_nt (ntr1 : nontermroot) ntr2 suff  = if has_index_suffix suff then
                                                           Ste_st(dummy_loc, St_node (dummy_loc,
                                                                { st_rule_ntr_name = ntr1 ^ "_list";
                                                                  st_prod_name = if ntr1 = "k_b_c" then "x_b_c_list_empty" else (ntr1 ^ "_list_empty");
                                                                  st_es = [];
                                                                  st_loc = dummy_loc }))
                                else
                                  Ste_st(dummy_loc,St_nonterm(dummy_loc,ntr1,(ntr2,suff)))

                                        
let make_empty_form_mv ntr1 ntr2 suff = if has_index_suffix suff then
                                     Ste_st( dummy_loc, St_node (dummy_loc, { st_rule_ntr_name = ntr1 ^ "_list";
                                                           st_prod_name = ntr1 ^ "_list_empty";
                                                           st_es = [];
                                                           st_loc = dummy_loc }))
                                   else
                                     Ste_metavar(dummy_loc,ntr1,(ntr2,suff))

                                                
let make_aux_call_empty st =   match st with
  | St_node (l,stnb) -> let args = make_args_from_st st in
                        let aux_name = stnb.st_prod_name ^ "_" ^ (String.concat "_" args) in
                        let new_es = fold_st { id_fold_functions with
                                f_nt = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_empty_form_nt ntr1 ntr2 suff ] );
                                f_mv = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_empty_form_mv ntr1 ntr2 suff ]) } [] st in
                        St_node (l,{ stnb with 
                                     st_prod_name = aux_name;
                                     st_es = new_es 
                                })
  | _ -> st


let make_cons_form_nt (ntr1 : nontermroot) ntr2 suff  = if has_index_suffix suff then
                                     Ste_st(dummy_loc, St_node (dummy_loc, { st_rule_ntr_name = ntr1 ^ "_list";
                                                           st_prod_name = ntr1 ^ "_list_cons";
                                                           st_es = [ Ste_st (dummy_loc,
                                                                             St_nonterm(dummy_loc, ntr1, (ntr2,remove_index suff)));
                                                                     Ste_st(dummy_loc,
                                                                            St_nonterm(dummy_loc, ntr1^"_list", (ntr2^"_list",remove_index suff)))];
                                                           st_loc = dummy_loc }))
                                else
                                  Ste_st(dummy_loc,St_nonterm(dummy_loc,ntr1,(ntr2,suff)))

                                        
let make_cons_form_mv ntr1 ntr2 suff = if has_index_suffix suff then
                                     Ste_st( dummy_loc, St_node (dummy_loc, { st_rule_ntr_name = ntr1 ^ "_list";
                                                                              st_prod_name = ntr1 ^ "_list_cons";
                                                                              st_es = [ Ste_metavar (dummy_loc, ntr1, (ntr2,remove_index suff));
                                                                                        Ste_st(dummy_loc,
                                                                                               St_nonterm(dummy_loc, ntr1^"_list", (ntr2^"_list", remove_index suff)))];
                                                                              st_loc = dummy_loc }))
                                   else
                                     Ste_metavar(dummy_loc,ntr1,(ntr2,suff))

           
let make_aux_call_cons st =   match st with
  | St_node (l,stnb) -> let args = make_args_from_st st in
                        let aux_name = stnb.st_prod_name ^ "_" ^ (String.concat "_" args) in
                        let new_es = fold_st { id_fold_functions with
                                f_nt = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_cons_form_nt ntr1 ntr2 suff ] );
                                f_mv = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_cons_form_mv ntr1 ntr2 suff ]) } [] st in
                        St_node (l,{ stnb with 
                                     st_prod_name = aux_name;
                                     st_es = new_es 
                                })
  | _ -> st


let apply2 (f : 'b -> 'c) ( (x,y) : 'a * 'b) : ('a * 'c) = (x,f x)

let make_aux_call_original st = map_st {id_map_functions with
                                         f_nt = (fun (ntr1, (ntr2,suff)) -> (ntr1, (ntr2, remove_index suff)));
                                         f_mv = (fun (ntr1, (ntr2,suff)) -> (ntr1, (ntr2, remove_index suff))) } st
                                   
let make_aux_call st =   match st with
  | St_node (l,stnb) -> let args = make_args_from_st st in
                        let aux_name = stnb.st_prod_name ^ "_" ^ (String.concat "_" args) in
                        let new_es = fold_st { id_fold_functions with
                                f_nt = (fun nt base -> List.append base [ rename_nt_as_st nt ] );
                                f_mv = (fun mv base -> List.append base [ rename_mv_as_st mv ] )} [] st in
                        St_node (l,{ stnb with 
                                     st_prod_name = aux_name;
                                     st_es = new_es 
                                })
  | _ -> st


let product_pair  (xs : 'a list )  (ys : 'a list list) : 'a list list = List.concat (List.map (fun x -> List.map (fun y -> x::y) ys) xs)
  
let rec product (xs : 'a list list) : 'a list list = match xs with
    [] -> [[]] (*List.map (fun x -> [x]) xs*)
  | xs::ys -> product_pair xs (product ys)

(* Find all possible names using all possible aliases for the nonterminal name in ss; second part of return pair is the list of primary
   names for the components of the tuple *)
let find_all_ntr_names_for ( xd : syntaxdefn) ( ss : string list ) : (string list) * (string list) = 

  (* FIXME use rule of ntr to help *)
  let find_names_for s = let xs = List.concat (List.map (fun r -> let ntr_names = List.map fst r.rule_ntr_names in
                                                                  if List.mem s ntr_names then ntr_names else []) xd.xd_rs) in
                         if List.length xs = 0 then [s] else xs in  (* Handling case where s is a metavar - FIXME *)
  
  let nm = List.map find_names_for ss |> product in
  (List.map  (fun xs -> (String.concat "_" xs) ^ "_list") nm , List.hd nm)

(* Create new grammar rules for list forms having productions: empty, cons and concat *)            
let create_new_rules  ( xd : syntaxdefn ) (ess : element list list) : (rule list) * (string list) = Auxl.option_map (fun es ->
                              Printf.eprintf "** create_new_rule \n";
                              Printf.eprintf "es length = %d\n" (List.length es);
                              let ss = as_strings es in (*|> distinguish_dups in *)
                              let tuple_hom = map_sep (fun i -> Hom_index i) (Hom_string ",") (List.mapi (fun i x -> i) ss) in 
                              Printf.eprintf "ss length = %d\n" (List.length ss);
                              let tuple = es in (*map_sep (fun s -> s)  (Lang_terminal ",") (distinguish_dups es) in*)
                              let (all_names,ss) = find_all_ntr_names_for xd ss in
                              Printf.eprintf "create_new_rule all names %s\n" (String.concat " " all_names) ;
                              Printf.eprintf "all names  length = %d\n" (List.length all_names);
                              List.iter (fun e -> Printf.eprintf "  name=%s\n" e) all_names;
                              List.iter (fun e -> Printf.eprintf "  tuple=%s\n" (Grammar_pp.pp_plain_element e)) tuple;
                              if List.length all_names = 0 then
                                None
                              else
                                begin
                                  let (name ::_) = all_names in
(*                                  let all_names = if name = "T_list" then
                                                    "x_T_list" :: all_names
                                                  else
                                                    all_names in *)
                                  let ntr = (name, (name,[])) in
                                  Some ({ rule_ntr_name = name;
                                    rule_ntr_names = List.map (fun n -> (n,[])) all_names;
                                    rule_pn_wrapper = name ;
                                    rule_ps = [ newprod (name ^ "_empty") [Lang_terminal "empty"] [("isa" , [Hom_string "[]"])] ;
                                                newprod (name ^ "_cons") (List.concat [ [ Lang_terminal "("; Lang_terminal "(" ];
                                                                                        tuple;
                                                                                        [ Lang_terminal ")" ;
                                                                                          Lang_terminal "#";
                                                                                          Lang_nonterm  (name, (name,[]));
                                                                                          Lang_terminal ")" ]])
                                                        [("isa", List.concat [ [Hom_string "("; Hom_string "("] ;
                                                                               tuple_hom;
                                                                               [Hom_string ")#";
                                                                                Hom_index (List.length ss); Hom_string ")"]])];
                                                newprod (name ^ "_concat") [ Lang_terminal "("; Lang_nonterm (name , (name, [])) ;
                                                                             Lang_terminal "@" ;
                                                                             Lang_nonterm (name , (name, [Si_punct "'" ]));
                                                                             Lang_terminal ")" ]
                                                        [("isa", [ Hom_string "(" ; Hom_index 0; Hom_string " @ " ; Hom_index 1; Hom_string ")" ] )];
                                                newprod (name ^ "_singleton") (List.concat [ [ Lang_terminal "(" ]; tuple; [ Lang_terminal ")" ]])
                                                        [ ("isa", List.concat [ [Hom_string "[("] ;
                                                                               tuple_hom;
                                                                               [Hom_string ")]"]])] ;
                                              ];
                                    rule_homs = [ ("isa", [ Hom_string ("(" ^ (String.concat "*" ss) ^ ") list")])];
                                    rule_meta = false;
                                    rule_semi_meta = false;
                                    rule_phantom = true;
                                    rule_judgement = false;
                                    rule_loc = dummy_loc},name)
                                end
                                                                                    ) ess |> unzip


(* Create new grammar rules for list forms having two productions - empty and cons *)            
let create_new_rules2  ( xd : syntaxdefn ) ( new_rules : (string *element) list) : (rule list) * (string list) = List.map (fun new_rule ->
                      let (name,Lang_list elb) = new_rule in
                      let es = List.map (fun e -> match e with
                                                    Lang_nonterm(ntr,nt) -> Lang_nonterm(ntr, strip_index2 nt)
                                                  | Lang_metavar (ntr,nt) -> Lang_metavar(ntr, strip_index2 nt)
                                                  | _ -> e) elb.elb_es in
                      ({ rule_ntr_name = name;
                                rule_ntr_names = [ (name,[])];
                                rule_pn_wrapper = name ;
                                rule_ps = [ newprod (name ^ "_empty") [Lang_terminal "empty"] [("isa" , [Hom_string "[]"])];
                                            newprod (name ^ "_cons") (List.concat [ [ Lang_terminal "(" ];
                                                                                    es;
                                                                                    [ Lang_terminal ")" ;
                                                                                      Lang_terminal "#";
                                                                                      Lang_nonterm  (name, (name,[])) ]])
                                                    []];
                                rule_homs = [];
                                rule_meta = false;
                                rule_semi_meta = false;
                                rule_phantom = false;
                                rule_judgement = false;
                                rule_loc = dummy_loc},name)
                   ) new_rules |> unzip

                                                                                               
let create_new_structure ntrs = [ ("tests/isa_rewrite_input.ott" ,  Struct_rs (Auxl.option_map (fun e -> match e with
                                                                     Lang_nonterm (_,nt) -> Some ((as_string nt) ^ "_list")
                                                                   | _ -> None) ntrs ))] 
(*let pp_dep deps = String.concat "\n" (List.map (fun (b,d) -> *)
                                  
let update_structure2 ntrs structure =
  let new_ntr = List.map (fun es -> let ss = as_strings es in
                                    let n = (String.concat "_" ss)  ^ "_list" in n) ntrs in

  List.map (fun (s,e) -> match e with
                         | Struct_rs xs -> (s,Struct_rs (List.append xs new_ntr))
                         | _ -> (s,e) ) structure

let update_structure new_ntr structure =
  List.map (fun (s,e) -> match e with
                         | Struct_rs xs -> (s,Struct_rs (List.append xs new_ntr))
                         | _ -> (s,e) ) structure

           
(*let has_dot_form stnb = List.exists (fun ste -> match ste with
                                                | Ste_list (_,ls) -> List.exists (fun l -> match l with Stli_listform _ -> true | _ -> false) ls
                                                | _  -> false
                                    ) stnb.st_es*)

let has_list_form stnb = List.exists (fun ste -> match ste with
                                                 | Ste_list (_,ls) -> true (*List.length (List.filter (fun i -> true ) ls) > 1*)
                                                 | _  -> false
                                     ) stnb.st_es

                                 
(* 
   Specification of auxilary predicates that we need to add to handle lists of tuples in dotted judgements. 
   First component of tuple is the defnclass and name of the judgement,
   second is the list of parameters. Left  is for paramters that are not list; Right is for parameters that are a list of tuples 
 *)
(* defn class name, new name, original name, args to auxilary predicate, term for the call back to original predicate *)
(*type defn_spec = (string * string * string) * ((string*suffix_item list ) list) * symterm*)
type defn_spec = (string * string * string) * symterm


type ntmv = (string * suffix_item list)
                                       
(* Specification of zip lines we need to add as premises. ie premises of the form f_t_list = zip f_list t_list *)                            
type zip_spec = ( ntmv * ( ntmv  list ))

(* Specification of mapI predicate. 
   ( judgement class it is in, name suffix for predicate,  nonterm of the list , abstract term we want to    unzip/unpack ) *)
type map_spec = (string * string * ntmv * string * symterm_element list * bound )

(*
let pp_without_index (ntr,suff) = let new_suff = Auxl.option_map (fun s -> 
                                                     match s with
                                                       Si_index _ -> None
                                                     | _ -> Some s) suff in
                                  let p = if (List.length suff = List.length new_suff) then "" else ""
                                  in (ntr^Grammar_pp.pp_plain_suffix new_suff) ^ p
 *)

let remove_terminal_e es = Auxl.option_map (fun e -> match e with Lang_terminal _ -> None | _ -> Some e) es

let make_list_cons (name : string ) (x : symterm_element list) (xs : symterm_element ) : symterm_element =
      let head_forms = map_stes { id_map_functions with
                                f_nt = (fun (ntr1,(ntr2,suff)) -> (ntr1, (ntr2, remove_index suff)));
                                f_mv = (fun (ntr1,(ntr2,suff)) -> (ntr1, (ntr2, remove_index suff ))) } x in

      Ste_st(dummy_loc, St_node(dummy_loc, {
           st_rule_ntr_name = name;
           st_prod_name = if name = "k_b_c_list" then "x_b_c_list_cons" else (name ^ "_cons");
           st_es = head_forms @ [xs] ;
           st_loc=dummy_loc})) 

let make_list_concat ( name : string) ( xs : symterm_element ) ( ys : symterm_element ) : symterm_element =
  Printf.eprintf "make_list_concat %s\n" name;
  Ste_st(dummy_loc, St_node(dummy_loc, {
                              st_rule_ntr_name = name;
                              st_prod_name = name ^ "_concat";
                              st_es = [xs; ys ] ;
                              st_loc=dummy_loc}))
        
let make_list_singleton ( name : string ) ( x : symterm_element list ) : symterm_element =
  let head_forms = map_stes { id_map_functions with
                              f_nt = (fun (ntr1,(ntr2,suff)) -> (ntr1, (ntr2, remove_index suff)));
                              f_mv = (fun (ntr1,(ntr2,suff)) -> (ntr1, (ntr2, remove_index suff ))) } x in
  
  Ste_st(dummy_loc, St_node(dummy_loc, {
                              st_rule_ntr_name = name;
                              st_prod_name = name ^ "_singleton";
                              st_es = head_forms ;
                              st_loc=dummy_loc})) 

            

let map_name_from ( cname : string ) ( stes : symterm_element list ) : (string list * string * suffix ) =
  let (names1, names2,suffs) =  fold_stes { id_fold_functions with
                           f_nt = (fun (ntr1,(ntr2,suff)) base -> List.append base [ (ntr1,ntr2,suff)  ] );
                           f_mv = (fun (ntr1,(ntr2,suff)) base -> List.append base [ (ntr1,ntr2,suff)  ] )} [] stes |> unzip3 in
  let all_suffs = List.concat suffs |> Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) in 
  (names2, cname ^ "_mapI_" ^ (String.concat "_" names1), all_suffs)
        
let rec process_st' xd (cname:string) (st : symterm) : symterm  * (map_spec list) =
  match st with
  | St_node (l,stnb) -> if has_list_form stnb then
                          let prod = Auxl.prod_of_prodname xd stnb.st_prod_name in
                          let (es,ls) = List.map2 (fun ste -> update_ste xd cname  ste ) stnb.st_es  (remove_terminal_e prod.prod_es) |> unzip in
                          let es = List.concat es in
                          (St_node(l,{ stnb with st_prod_name = stnb.st_prod_name ^ "_list";
                                                st_es = es  }), List.concat ls)
                        else
                          let _ = Printf.eprintf "stnb.st_prod_name=%s\n" stnb.st_prod_name in
                          let (es,ls) = List.map (fun ste -> process_ste xd cname  ste) stnb.st_es |> unzip in
                          let es = List.concat es in
                          (St_node(l, { stnb with st_es = es }) , List.concat ls)
  | _ -> (st,[])
and process_ste xd cname (ste : symterm_element) : symterm_element list * (map_spec list) = match ste with
  | Ste_st (l,st) -> let (st, ls) = process_st' xd cname st in ([Ste_st (l, st)], ls)
  | _ -> ([ste],[])


and update_stli cname (stli : symterm_list_item ) : symterm_element list  = match stli with
    Stli_single (l,ste) -> ste 
  | Stli_listform stlb ->
     let l = dummy_loc in
     let new_es = fold_stli { id_fold_functions with
                              f_nt = (fun (ntr,nt) base -> let (r,t) = rename_mvnt (ntr,nt) in List.append base [Ste_st(l,St_nonterm(l,r,t))] );
                              f_mv = (fun (ntr,nt) base -> let (r,t) = rename_mvnt (ntr,nt) in List.append base [Ste_metavar(l,r,t)] )} [] stli
     in new_es
(*
                          let l = dummy_loc in
                          let new_es = fold_stli { id_fold_functions with
                                                   f_nt = (fun (ntr,nt) base -> let (r,t) = rename_mvnt (ntr,nt) in List.append base [Ste_st(l,St_nonterm(l,r,t))] );
                                                   f_mv = (fun (ntr,nt) base -> let (r,t) = rename_mvnt (ntr,nt) in List.append base [Ste_metavar(l,r,t)] )} [] stli
                          in
                          let new_stnb = { st_rule_ntr_name = "G_singleton_list" ;  (* HOW TO FIX THIS ?? *)
                                           st_prod_name = "G_singleton_list_GSL";
                                           st_es = new_es;
                                           st_loc = dummy_loc } in 
                          Ste_st(dummy_loc, St_node(dummy_loc,new_stnb))
                                     *)
                                                                       

(* Turn something like t1 : T1 .. tn : Tn into t_T_list and return [t,T] to indicate we want a zip function - zipI t_T_list t_list T_list *)
and update_ste xd (cname : string) (ste  : symterm_element ) ( le : element ): (symterm_element list * map_spec list ) = match ste with
  | Ste_list (l,stlis) -> Printf.eprintf "update_ste (%s) %s lang element=%s \n" (Location.pp_loc l) (Grammar_pp.pp_plain_symterm_element ste) (Grammar_pp.pp_plain_element le);

                          let (Lang_list elb) = le in
                          let nts = Auxl.option_map (fun e -> match e with
                                                         Lang_nonterm (s1,(s2,_)) -> Some s2
                                                       | Lang_metavar (s1,(s2,_)) -> Some s2  
                                                       | _ -> None ) elb.elb_es in
                          let list_name = (String.concat "_" nts ) ^ "_list" in (* FIXME Do something with suffixes *)
                          Printf.eprintf "  list_name=%s\n" list_name; 
                          (* Walk over list elements and build up list making use of cons, concat and singleton *)
                          let (Some bob) = List.fold_right (fun x xs -> match x with
                                                         Stli_single (_, stes ) -> (match xs with
                                                                                   | None -> Some (make_list_singleton list_name stes)
                                                                                   | Some xs -> Some (make_list_cons list_name stes xs))
                                                       | Stli_listform stlb ->
                                                          let ste = Ste_st (dummy_loc, St_nonterm( dummy_loc, list_name, (list_name,[]))) in
                                                          (* FIXME - Do something with suffix here *)
                                                          let (names1,names2,suffs) =  fold_stes { id_fold_functions with
                                                                                   f_nt = (fun (ntr1,(ntr2,suff)) base -> List.append base [ (ntr1,ntr2,suff)  ] );
                                                                                   f_mv = (fun (ntr1,(ntr2,suff)) base -> List.append base [ (ntr1,ntr2,suff)  ] )} [] stlb.stl_elements |> unzip3 in
                                                          let name1 = (String.concat "_" names1 ) ^ "_list" in
                                                          let name2 = (String.concat "_" names2 ) ^ "_list" in
                                                          let all_suffs = List.concat suffs |> Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) in 
                                                          let ste = Ste_st (dummy_loc, St_nonterm( dummy_loc, list_name, (name2, all_suffs))) in
                                                          Printf.eprintf "names = %s %s\n" name1 name2; 
                                                          (match xs with
                                                          | None -> Some ste
                                                          | Some xs -> Some (make_list_concat list_name (Ste_metavar (dummy_loc, name1, (name2,[]))) xs))
                                                       | _ -> None)
                                                    stlis None
                                          
                          in
                          Printf.eprintf "BOB = %s\n" (Grammar_pp.pp_plain_symterm_element bob);
                          
                          (* le is a Lang_list and nonterm/metavar will give us the list type G_list or t_T_list etc, this is 
                             then use in the construction of the St_node below  *)
                          (* FIXME should be looking over stlis just for Stli_listform and replacing just those;
                             take the relements we are replacing and use these to make mapI predicate *)

                          let map_specs = Auxl.option_map (fun stli -> match stli with
                                                                       | Stli_listform stlb -> 
                                                                          (*let ste = Ste_st (dummy_loc, St_nonterm( dummy_loc, list_name, (list_name,[]))) in*)
                                                                          let (names,map_name,suffs) = map_name_from cname stlb.stl_elements in
                                                                          Printf.eprintf "names = %s\n" (String.concat " " names);
                                                                          let list_name2 = (String.concat "_" names ) ^ "_list" in
                                                                          if List.length names > 1 then 
                                                                            Some ( cname, map_name, (list_name,suffs), list_name2 , stlb.stl_elements, stlb.stl_bound)
                                                                          else
                                                                            None
                                                                       | _ -> None
                                                          ) stlis in
                          ( [bob] , map_specs )
                                    
  | _ -> process_ste xd cname ste

                     
(*                          let ste = List.concat (List.map (fun x -> update_stli x) stlis)
                          in (ste,[])*)
                          (*
                          let ste = List.fold_left (fun y x -> Ste_st (dummy_loc,
                                                                       St_node (dummy_loc,
                                                                                { st_rule_ntr_name = list_name;
                                                                                  st_prod_name = list_name ^ "_cons";
                                                                                  st_es = [ update_stli x; y];
                                                                                  st_loc = dummy_loc })))  (update_stli (Auxl.last stlis)) (Auxl.drop_last stlis)
                          in (ste,[])
                           *)
                          (*
                          let (stlis, zipspecs ) = List.map (fun stli ->
                                                       match stli with
                                                          | (Stli_listform stlb) -> let ntms = Auxl.option_map (
                                                                       fun ste -> match ste with
                                                                                  | Ste_st (_,st) -> (match st with
                                                                                         | St_node (_,stnb) -> Some (stnb.st_rule_ntr_name, [])
                                                                                         | St_nonterm (_,_,nt) -> Some nt )
                                                                                  | Ste_metavar (_,_,mv) -> Some mv
                                                                                  | _ -> None) stlb.stl_elements in
                                                                                    let (ntr, suffs ) = as_list_ntmv ntms in 
                                                                                    let ntms = List.map (fun x -> as_list_ntmv [x]) ntms 
                                                                                    in ( Stli_single (l, [Ste_st (l, St_nonterm (l, ntr , (ntr,suffs)))]),
                                                                                         [((ntr,suffs) , ntms)])
                                                          | _ -> ( stli, [] )) stlis |> unzip
                                                 
                          in (match stlis with
                                [ Stli_single( l , [ste] ) ] -> (ste, List.concat zipspecs)
                              | _ -> (Ste_list (l,stlis), List.concat zipspecs))*)


           (*
and update_ste (ste  : symterm_element ) : (symterm_element * zip_spec list ) = match ste with
  | Ste_list (l,stlis) -> Printf.eprintf "update_ste (%s)\n" (Location.pp_loc l);
                          let ntms = List.concat (List.map (fun stli -> match stli with
                              | (Stli_listform stlb) -> Auxl.option_map (
                                      fun ste -> match ste with
                                                 | Ste_st (_,st) -> (match st with
                                                                     | St_node (_,stnb) -> Some (stnb.st_rule_ntr_name, [])
                                                                     | St_nonterm (_,_,nt) -> Some nt )
                                                 | Ste_metavar (_,_,mv) -> Some mv
                                                 | _ -> None) stlb.stl_elements
                                                           ) stlis)
                          in
                          let (ntr, suffs ) = as_list_ntmv ntms in  (*as_string_list ntms in (*(String.concat "_" (List.map fst ntms)) ^ "_list" in*)*)
                          let ntms = List.map (fun x -> as_list_ntmv [x]) ntms 
                          in (Ste_st (l, St_nonterm (l, ntr , (ntr,suffs))), [((ntr,suffs) , ntms)])
  | _ -> process_ste ste
            *)
(*let create_zip_specs ls = Auxl.option_map (fun ls -> if List.length ls > 1 then
                                                       Some ( (String.concat "_" ls) ^ "_list", (List.map (fun l -> l ^ "_list" ) ls))
                                                     else None )ls*)
                     
let rewrite_st xd (cname:string) (st : symterm) : symterm * (map_spec  list) =
  Printf.eprintf "STOld: %s\n" (Grammar_pp.pp_plain_symterm st) ;
  let (st,ls) = process_st' xd cname  st in (* FIXME *)
  Printf.eprintf "STNew: %s\n" (Grammar_pp.pp_plain_symterm st) ;
  Printf.eprintf "MAPS for: %s\n" (String.concat " " (List.map (fun ( _, name, (lhs,_),lhs2, rhs, _) -> "MAPI name=" ^ name ^ " lhs=" ^ lhs ^ " lhs2= " ^ lhs2 ^ " "  ^ (String.concat " " (List.map Grammar_pp.pp_plain_symterm_element rhs))) ls)) ;
  (st,ls)
                      

(*  Recurse down.
         If St_node has dot form
                iterate over elements in node
                        if non dot form then pass back e
                        if dot form then then pass back nonterm list form 
                change st_rule_ntr_name to be the same but with "_list" appended
         else
            identity
 *)
let cons_pair (x,y) = x::y


let create_formula cname dname args = St_node (dummy_loc, { st_rule_ntr_name = cname; st_prod_name = dname ; st_es = []; st_loc= dummy_loc })

(*
let conflate (args : (string, suffix_item list) list) = List.concat (List.map (fun x ->
                                                                         let x = rename_mvnt x in match x with
                                                                                          
                                                      Left s -> [s]
                                                    | Right s -> [(String.concat "_" s)^ "_list"] ) args)
 *)


(* Create production for new auxilary predicate *)
let create_defn_prod (cname : string ) (dname : string) (st : symterm) = newprod ( dname ) (Lang_terminal (dname ) ::
                   (fold_st { id_fold_functions with f_nt = (fun nt base -> List.append base [ rename_nt nt ]);
                                                     f_mv = (fun mv base -> List.append base [ rename_mv mv ]) } [] st)) []

                                  (*List.map (fun s -> 
                                                                                        let (s,_) = rename_mvnt s in Lang_nonterm (s,(s,[]))) args
                                                                                 ) []
                                   *)

                                                                                                            
(* 0 : empty , 0 : t_list   2 : (t # t_list ) *)
                                                                                 (*
let make_args args mode = List.map (fun (s,suff) ->
                              let a = if has_index_suffix suff then
                                        Right [s]
                                      else
                                        Left s in
         Ste_st (dummy_loc, (match a with
                               Left s -> St_nonterm (dummy_loc, s, (s,[]))
                             | Right s -> let s2 =  (String.concat "_" s) ^ "_list" in
                                          match mode with
                                          | 0 -> St_node (dummy_loc, { st_rule_ntr_name = s2;
                                                                       st_prod_name = s2 ^ "_empty";
                                                                       st_es = [];
                                                                       st_loc = dummy_loc })
                                          | 1 -> St_nonterm (dummy_loc,s2, (s2,[]))
                                          | 2 -> St_node (dummy_loc, { st_rule_ntr_name = s2;
                                                                       st_prod_name = s2 ^ "_cons";
                                                                       st_es = [ Ste_st (dummy_loc,
                                                                                         let s3 = String.concat "_" s in
                                                                                         St_nonterm(dummy_loc, s3, (s3,[])));
                                                                                 Ste_st(dummy_loc,
                                                                                        St_nonterm(dummy_loc, s2, (s2,[])))];
                                                                       st_loc = dummy_loc
                                                         })
                                          | 3 -> let s3 = String.concat "_" s in St_nonterm (dummy_loc, s3, (s3,[])) (* FIXME ?? *)
                            ))) args
                                                                                  *)

                                                                                 (*
let make_st_node cname dname (args : ( (string * (suffix_item list)) list))  mode = St_node (dummy_loc, {
                                             st_rule_ntr_name = "formula";
                                             st_prod_name = "formula_judgement";
                                             st_es = [ Ste_st (dummy_loc, St_node (dummy_loc, {
                                                                                     st_rule_ntr_name = "judgement";
                                                                                     st_prod_name = "judgement_" ^ cname;
                                                                                     st_es = [Ste_st (dummy_loc, St_node (dummy_loc, {
                                                                                                                            st_rule_ntr_name =cname;
                                                                                                                            st_prod_name = dname;
                                                                                                                            st_es = make_args args mode;
                                                                                                                            st_loc = dummy_loc
                                                                                                                         }))];
                                                                                     st_loc = dummy_loc
                                                                                   }))];
                                             st_loc = dummy_loc })
                                                                                  *)


let make_args_from (st : symterm) : ( nontermroot * nonterm) list  = fold_st { id_fold_functions with f_nt = (fun n base -> List.append base [n]);
                                                                                                      f_mv = (fun n base -> List.append base [n]) } [] st


let rec remove_dup_defn_spec (dss : defn_spec list) : defn_spec list = match dss with
    [] -> []
  | (d::dss) -> if  List.exists (fun (k,_) -> k = fst d) dss then
                  remove_dup_defn_spec dss
                else
                  d :: (remove_dup_defn_spec dss)

    
(* Create new auxilary predicates to handle dotted judgements  *)                                                                                            
let create_aux_defns (dss : defn_spec list) : ((defn*prod) list ) =
  (*Printf.eprintf "create_aux_defns lst=%s\n" (String.concat " " (List.map (fun  ( (x,y,z),args,form) -> x ^ y ^ "( " ^ 
      (String.concat " " (List.map (fun x -> Grammar_pp.pp_plain_nonterm x) args ))) dss ));*)
                (*match a with
                                                                       Left s -> "(Left " ^ s ^ ")"
                                                                     | Right ss -> "(Right " ^ (String.concat "| " ss)) args))) dss ));*)

  List.map (fun ( (cname,new_dname,old_dname), st ) -> ({
                                         d_name = new_dname ;
                                         d_form = create_formula cname (new_dname) [];
                                         d_wrapper = new_dname ^ "_";
                                         d_rules = [ PSR_Rule {
                                                         drule_name = new_dname ^ "_empty";
                                                         drule_categories = StringSet.empty;
                                                         drule_premises = [];
                                                         drule_conclusion = make_aux_call_empty st ;
                                                         drule_homs = [];
                                                         drule_loc = dummy_loc };
                                                     PSR_Rule {
                                                         drule_name = new_dname ^ "_cons";
                                                         drule_categories = StringSet.empty;
                                                         drule_premises = [ (None, make_aux_call_original st );
                                                                            (None,make_aux_call st) ];
                                                         drule_conclusion = make_aux_call_cons st ;
                                                         drule_homs = [];
                                                         drule_loc = dummy_loc } 
                                                   ];
                                         d_homs = [];
                                         d_loc = dummy_loc }, create_defn_prod cname new_dname st )) (remove_dup_defn_spec dss)



  (*if List.length suffix > 0 then
                                    (root ^ "_list", [])
                                  else
                                    (root,[])*)

let create_aux_name base_name args = base_name ^ "_" ^
                                       (String.concat "_" (List.map (fun s -> let (s,_) = rename_mvnt s in s) args))
                                         (*match s with 
                                                               Left s -> s
                                                                   | Right ss -> (String.concat "_" ss) ^ "_list" ) args))
                                          *)
(*let make_args_from es =  List.map (fun ste ->
                                                let (ntr,suffix) = match ste with
                                                  | Ste_st (_, St_nonterm (_,ntr,(_,suffix))) -> (ntr,suffix)
                                                  | Ste_st (_, St_node (_,stlb )) -> ( stlb.st_prod_name,[])
                                                  | Ste_metavar ( _, ntr, (_,suffix)) -> (ntr,suffix)
                                                  | Ste_var _ -> raise (Failure "Unexpected Ste_var")
                                                  | Ste_list _ -> raise (Failure "Unexpected Ste_list")
                                                in
                                                 let (_,new_suffix) = strip_index2 (ntr,suffix) in
                                                 if new_suffix = suffix then
                                                   Left ntr
                                                 else
                                                   Right [ ntr ] (* Want just ntr as this represents the sort/type ^Grammar_pp.pp_plain_suffix new_suffix ] *)
                                    ) es
 *)

let rename_st' st = make_aux_call st

(*                                   
let rename_st' st =
  Printf.eprintf "rename_st'\n";
  match st with
  | St_node (l,stnb) -> let args = make_args_from_st st in
                        let aux_name = stnb.st_prod_name ^ "_" ^ (String.concat "_" args) in
                        (* FIXMEGENERALISE 
                           Collect pair of lists of nonterms and metavars, left list are non-list indexed; right list is list indexed with list index removed
                           Create element list of the first and then element list of the second; this is the st_es in the record below 
                           Also return St_node (l,stnb) - this is the template for creating  auxilary predicate  OR have sep foldr for it *)
                        let new_es = fold_st { id_fold_functions with f_nt = (fun (ntr,nt) base -> let (r,s) = rename_mvnt nt in List.append base [Ste_st(l,St_nonterm(l,r,(r,s)))] );
                                                                     f_mv = (fun (ntr,nt) base -> let (r,s) = rename_mvnt nt in List.append base [Ste_metavar(l,r,(r,s))] )} [] st in
                        Printf.eprintf "** NEWES %s\n" (String.concat " " (List.map (fun x -> Grammar_pp.pp_plain_symterm_element x)  new_es));
                        St_node (l,{ stnb with 
                          st_prod_name = aux_name;
                          st_es = new_es (*List.map (fun ste -> match ste with (* FIXME THis only goes to one level; not general enough *)
                                                       | Ste_st (l, St_nonterm (_,ntr,nt)) -> Ste_st(l,St_nonterm (l,ntr,(rename_mvnt nt)))
                                                       | Ste_metavar (l,mvr,mv) -> Ste_metavar (l,mvr, (rename_mvnt mv))
                                                       | _ -> ste) stnb.st_es*)
                        })
                        *)
let rec rename_st (st : symterm)  = match st with
  | St_node (l,stnb) -> if stnb.st_rule_ntr_name = "judgement"  then
                          (Printf.eprintf "found judgement\n";
                          match stnb.st_es with
                          | [ Ste_st (l2,st) ] -> St_node(l, { stnb with st_es = [ Ste_st(l2,rename_st' st)] }))
                        else
                          St_node (l, { stnb with
                                        st_es = List.map (fun ste -> match ste with
                                                                     | Ste_st (l,st) -> Ste_st(l,rename_st st)
                                                                     | _ -> ste ) stnb.st_es })
  | _ -> st

(* 
  Process premise as follows: if the premise is formula_dots (ie dot formed judgement) then lift out judgement, 
  rename the judgement and rename the dot-indexed terms to be '_list' forms. Returns information on the new judgement
  and the lists used
  For example, converts
   check G- t1 T1 .. check G tn Tn 
  to
   check_aux G t_list T_list
 *)


                                         
let find_defns_st' (st : symterm) : (defn_spec list)  =  match st with
  | St_node (l,stnb) -> let args = make_args_from st
 in
                          [ (( stnb.st_rule_ntr_name, create_aux_name stnb.st_prod_name args, stnb.st_prod_name ), st)]

  | _ -> []
           
let rec find_defns_st st = match st with
  | St_node (l,stnb) -> if stnb.st_rule_ntr_name = "judgement"  then
                          (match stnb.st_es with
                           | [ Ste_st (l2,st) ] -> find_defns_st' st )
                        else
                          List.concat (List.map (fun ste -> match ste with
                                                                     | Ste_st (l,st) -> find_defns_st st
                                                                     | _ -> [] ) stnb.st_es)
  | _ -> []

           
let find_defns stnb = if stnb.st_prod_name = "formula_dots" then
                     match stnb.st_es with
                     | [Ste_list (_ ,[stli]) ] ->
                        (match stli with
                        | Stli_listform stlb -> (match stlb.stl_elements with
                                                 | (Ste_st (_,st)::_) -> find_defns_st st
                                                 | _ -> [])
                        | _ -> [])
                   else []
                       
           
let rewrite_premise cname (prem : (string option * symterm)) : ( (string option * symterm) * (defn_spec list) * (map_spec list)  ) =
  Printf.eprintf "rewrite_premise: %s\n" (Grammar_pp.pp_plain_symterm (snd prem));
  match prem with
    (_,St_node (l,stnb)) -> Printf.eprintf "PRODNAME %s\n" stnb.st_prod_name;
                            ((let (_,new_prem) = (if stnb.st_prod_name = "formula_dots" then
                                                    (match stnb.st_es with
                                                       [Ste_list (_ ,[stli]) ] -> let _ = Printf.eprintf "HERE\n" in
                                                                                  (match stli with
                                                                                   | Stli_listform stlb -> Printf.eprintf "HERE2\n";
                                                                                              (match stlb.stl_elements with
                                                                                               | (Ste_st (_,st)::_) -> Printf.eprintf "HERE3\n"; (None,rename_st st)
                                                                                               | _ -> prem)
                                                                                   | _ -> prem))
                                                  else
                                                    prem)
                              in
                              Printf.eprintf "NEWPREM %s\n" (Grammar_pp.pp_plain_symterm new_prem);
                              (None,new_prem)),
                             find_defns stnb , [] )

                              
                                                         
let zip_formula_name (lhs,rhs) =  "formula_" ^ (fst lhs) ^ "_" ^ (String.concat "_" (List.map fst rhs))

                                                                   
                                                                   
let create_zip_prods (zss : zip_spec list) = List.map (fun (lhs,rhs) -> newprod (zip_formula_name (lhs,rhs))
                                                              (List.concat  [[
                                                                                Lang_terminal (Grammar_pp.pp_plain_nonterm lhs);
                                                                                Lang_terminal "=" ;
                                                                                Lang_terminal "zip" ];
                                                                             List.map (fun s -> Lang_terminal (Grammar_pp.pp_plain_nonterm s)) rhs ])
                                                              [ ("isa" ,
                                                                           [ Hom_string "zipI "; Hom_terminal (Grammar_pp.pp_plain_nonterm lhs)]@
                                                                             List.concat (List.mapi (fun i x -> [Hom_string " ";
                                                                                                                 Hom_terminal (Grammar_pp.pp_plain_nonterm x)]) rhs)
                                                                )]
                                    ) zss 
                                                         
(* Add premise and new production for formula nonterminal with appropriate isa hom *)
let create_zip_premises (zss : zip_spec list) : (string option * symterm) list * (prod list) =
  (List.map (fun (lhs, rhs) -> (None,St_node (dummy_loc, {
                                                st_rule_ntr_name = "formula";
                                                st_prod_name = zip_formula_name (lhs,rhs);
                                                st_es = [];
                                                st_loc =dummy_loc }))) zss, create_zip_prods zss)



                                                 

    
let create_map_prods (mss : map_spec list) : prod list =  
  List.map (fun (cname, name,(lhs, _) , _ , rhs, _) ->
      let names =  fold_stes { id_fold_functions with
                              f_nt = (fun (ntr,nt) base -> List.append base [ rename_nt (ntr,nt) ] );
                              f_mv = (fun (ntr,nt) base -> List.append base [ rename_mv (ntr,nt) ] )} [] rhs in
      newprod name
              (List.append [ Lang_terminal name;
                             Lang_nonterm (lhs,(lhs,[])) ] names )
              [ ]
    ) mss 

let make_map_premise ((cname, name, (lhs,suff) , lhs2, rhs, _) : map_spec ) ( usesuff : bool)  =
  Printf.eprintf "make_map_premises %s %s %s %s %s\n" cname name lhs lhs2 ;
  let l = dummy_loc in 
  let new_es = fold_stes { id_fold_functions with
                           f_nt = (fun (ntr,nt) base -> List.append base [ rename_nt_as_st (ntr,nt) ] );
                           f_mv = (fun (ntr,nt) base -> List.append base [ rename_mv_as_st (ntr,nt) ] ) } [] rhs in
  (None,St_node (dummy_loc, {
                   st_rule_ntr_name = cname;
                   st_prod_name = name;
                   st_es = Ste_st( l , St_nonterm(l,lhs,(lhs2, if usesuff then suff else [])))::new_es;
                   st_loc =dummy_loc }))
    
let create_map_premises ( mss : map_spec list ) : (string option * symterm) list * (prod list) =
  (List.map (fun ms -> make_map_premise ms true) mss, create_map_prods mss )


                                                
let make_map_call_empty cname name lhs rhs =
  let new_stes = fold_stes { id_fold_functions with
                              f_nt = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_empty_form_nt ntr1 ntr2 suff ] );
                              f_mv = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_empty_form_mv ntr1 ntr2 suff ] )} [] rhs in
  let first = Ste_st(dummy_loc, St_node(dummy_loc, {
                                            st_rule_ntr_name = lhs;
                                            st_prod_name = if lhs = "k_b_c_list" then "x_b_c_list_empty" else (lhs ^ "_empty");
                                            st_es = [];
                                            st_loc = dummy_loc })) in
                                                      
  St_node (dummy_loc,{
             st_rule_ntr_name = cname;
             st_prod_name = name ;
             st_es = first :: new_stes;
             st_loc = dummy_loc
          })

(*    let head_forms = map_stes { id_map_functions with
                                f_nt = (fun (ntr1,(ntr2,suff)) -> (ntr1, (ntr2, remove_index suff)));
                                f_mv = (fun (ntr1,(ntr2,suff)) -> (ntr1, (ntr2, remove_index suff ))) } rhs in

(*    let head_forms = fold_stes { id_fold_functions with
          f_nt = (fun (ntr,(_,suff)) base -> List.append base [ Ste_st(dummy_loc, St_nonterm(dummy_loc, ntr, (ntr, remove_index suff))) ] );
          f_mv = (fun (ntr,(_,suff)) base -> List.append base [ Ste_metavar(dummy_loc, ntr, (ntr, remove_index suff ))]) } [] rhs in
 *)
    
    let first = Ste_st(dummy_loc, St_node(dummy_loc, {
           st_rule_ntr_name = lhs;
           st_prod_name = lhs ^ "_cons";
           st_es = head_forms @ [ Ste_st(dummy_loc, St_nonterm(dummy_loc, lhs  , ( lhs,[])))];
           st_loc=dummy_loc})) in
 *)

          
let make_map_call_cons cname name lhs rhs =
    let new_stes = fold_stes { id_fold_functions with
                              f_nt = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_cons_form_nt ntr1 ntr2 suff ] );
                              f_mv = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_cons_form_mv ntr1 ntr2 suff ] )} [] rhs in
    Printf.eprintf "** make_map_call_cons %s\n" (String.concat " " (List.map Grammar_pp.pp_plain_symterm_element rhs));

    let first = make_list_cons lhs rhs (Ste_st(dummy_loc, St_nonterm(dummy_loc, lhs  , ( lhs,[])))) in
    
    St_node (dummy_loc,{
             st_rule_ntr_name = cname;
             st_prod_name = name ;
             st_es = first :: new_stes;
             st_loc = dummy_loc
            })


let make_map_call_single cname name lhs rhs =
    let new_stes = fold_stes { id_fold_functions with
                              f_nt = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_cons_form_nt ntr1 ntr2 suff ] );
                              f_mv = (fun (ntr1,(ntr2,suff)) base -> List.append base [ make_cons_form_mv ntr1 ntr2 suff ] )} [] rhs in
    Printf.eprintf "** make_map_call_cons %s\n" (String.concat " " (List.map Grammar_pp.pp_plain_symterm_element rhs));

    let first = make_list_singleton lhs rhs  in
    
    St_node (dummy_loc,{
             st_rule_ntr_name = cname;
             st_prod_name = name ;
             st_es = first :: new_stes;
             st_loc = dummy_loc
            })


let bound_length b = match b with
    Bound_dotform b -> b.bd_length
  | _ -> 0
            
let create_map_defns ( mss : map_spec list ) : defn list =
  Printf.eprintf "** create_map_defns |mss|=%d\n" (List.length mss);
  let mss = rem_dupsf mss (fun (_,x,_,_,_,_) (_,y,_,_,_,_) -> x = y)  in
  List.map (fun ((cname, name, (list_name,_), _ , stes,bnd) as ms) ->
      Printf.eprintf "  map name=%s\n" name;
      let d_name = name  in
      let rules = if bound_length bnd = 0 then 
                [ PSR_Rule {
                        drule_name = d_name ^ "_empty";
                        drule_categories = StringSet.empty;
                        drule_premises = [];
                        drule_conclusion = make_map_call_empty cname d_name list_name stes ;
                        drule_homs = [];
                        drule_loc = dummy_loc };
                    PSR_Rule {
                        drule_name = d_name ^ "_cons";
                        drule_categories = StringSet.empty;
                        drule_premises = [ make_map_premise ms false ];
                        drule_conclusion =  make_map_call_cons cname d_name list_name stes;
                        drule_homs = [];
                        drule_loc = dummy_loc } 
                ]
              else
                [ PSR_Rule {
                        drule_name = d_name ^ "_cons";
                        drule_categories = StringSet.empty;
                        drule_premises = [ make_map_premise ms false ];
                        drule_conclusion =  make_map_call_single cname d_name list_name stes;
                        drule_homs = [];
                        drule_loc = dummy_loc } 
                ]
      in
      {
        d_name = d_name;
        d_form = create_formula cname d_name [];
        d_wrapper = d_name ^ "_";
        d_rules = rules;
        d_homs=[];
        d_loc = dummy_loc }) mss

  
(*let create_zip_specs dss =
  Printf.eprintf "create_zip_specs \n";
  List.iter (fun (nme, ls) -> Printf.eprintf "   nme=%s\n" nme) dss;

  let lists = List.concat (List.map (fun (_, args)  -> Auxl.option_map (fun a -> match a with
                                                                          | Right s when List.length s > 1 -> Some s
                                                                          | _ -> None) args) dss)
  in List.map (fun ts -> let nme = (String.concat "_" ts) ^ "_list" in
                         (nme,ts)) lists
 *)
  
let rewrite_rule xd cname (dr:drule) : (drule * (defn_spec list) * (prod list) * (map_spec list)) =
  let (new_conc,zip_spec1) = rewrite_st xd cname dr.drule_conclusion  in
  let (new_premises, defn_specs, zip_spec2) = List.map (fun p -> rewrite_premise cname p ) dr.drule_premises |> unzip3 in
  let zip_specs = (zip_spec1@ (List.concat zip_spec2)) in
  let (zip_premises, form_prods)  = create_map_premises zip_specs  in
  ( { dr with drule_conclusion = new_conc;
              drule_premises = new_premises @ zip_premises }, List.concat defn_specs, form_prods,zip_specs )

    
let rewrite_defn xd (cname:string) (d:defn) : (defn * ((defn*prod) list) * (prod list) * (defn list) * (map_spec list))  =
  let _ = Printf.eprintf "rewrite_defn\n%s\n\n" (Grammar_pp.pp_plain_symterm d.d_form) in
  let (ds,defn_specs,form_prods,map_specs) = (List.map (fun r -> match r with
                                                                 | PSR_Rule r -> let (r, dss,fps , mss) = rewrite_rule xd cname r in
                                                                                 (PSR_Rule r, dss,fps, mss)
                                                                 | PSR_Defncom _ -> (r,[],[],[]) ) d.d_rules) |> unzip4 in
  let new_aux_defns = create_aux_defns (rem_dups (List.concat defn_specs)) in
  let new_map_defns = create_map_defns (List.concat map_specs)  (* FIXME - change hard coded Jopp *)
  in ({ d with d_rules = ds  }, new_aux_defns, List.concat form_prods , new_map_defns , List.flatten map_specs )

       
let rewrite_defns xd cname (defns : defn list) : defn list * prod list * prod list * map_spec list =
  let (dl, pl,fp,ms) = unzip4 (List.map (fun d ->
                                   let (new_d,ds,fp,ds2,ms) = rewrite_defn xd cname d in
                                   let (ds,ps) = unzip ds in
                                   ( (new_d :: ds) @ ds2 ,ps, fp,ms) ) defns) in
  (List.concat dl, List.flatten pl, List.flatten fp, List.flatten ms)

                                                                   

let rewrite_relations rd xd : fun_or_reln_defnclass list * ((string * prod list) list) * ( (string * prod list)  list ) * (map_spec list )= 
  let ( (xs : fun_or_reln_defnclass list) ,ys , (fs : (string*prod list) list ), ms) = unzip4 (List.map (fun rd -> match rd with
                          | FDC _ -> (rd,("",[]),("",[]),[])
                          | RDC dc -> let (defs, prods, form_prods, map_specs ) = rewrite_defns xd dc.dc_name dc.dc_defns 
                                      in (RDC { dc with dc_defns = defs }, (dc.dc_name , prods ), (dc.dc_name, form_prods), map_specs )) rd)
  in  (xs, ys , fs, List.flatten ms)
        
let update_list_rule xd (_,_,(lhs1,_), lhs2, _ ,_) =
  { xd with xd_rs = List.map (fun r ->
                        if r.rule_ntr_name = lhs1 then
                          { r with rule_ntr_names = r.rule_ntr_names @ [ (lhs2,[]) ]  }   (* FIXME Should add hom for this ? *)
                        else
                          r) xd.xd_rs }
                        
        
let update_grammar_rule xd name prods = 
  { xd with xd_rs = List.map (fun r ->
                        if r.rule_ntr_name = name  then
                          { r with rule_ps = r.rule_ps @  prods }
                        else r) xd.xd_rs }

let update_grammar_rules xd prods =
  List.fold_left (fun xd (name,prods)  -> update_grammar_rule xd name prods) xd prods



let pp_drule dr = (String.concat "\n" (List.map (fun (_,st) -> Grammar_pp.pp_plain_symterm st) dr.drule_premises)) ^ "\n"
                  ^ "------------------------------------------------------------- :: " ^ dr.drule_name ^ "\n"
                  ^ (Grammar_pp.pp_plain_symterm dr.drule_conclusion) ^ "\n"
                                     
let pp_defn defn = "defn " ^ defn.d_name ^ " :: \n"
                   ^ (String.concat "\n" (List.map (fun psr -> match psr with
                                                                 PSR_Rule dr -> pp_drule dr
                                                               | _ -> "") defn.d_rules))
                   ^ "\n"
                       
                                     
let pp_relations rels = String.concat "\n" (List.map (fun rel -> match rel with
                                                                 | FDC _ -> "<fundefnclass>"
                                                                 | RDC dc -> String.concat "\n\n" (List.map pp_defn dc.dc_defns)) rels)

(* FIXME Will need to build this programmatically based on dimension of zips we need *)
let zip_embeds = Struct_embed (dummy_loc, "isa", [ Embed_string (dummy_loc, "inductive zipI :: \"('a*'b) list => 'a list => 'b list => bool\" where\n\"zipI [] [] []\"\n|\"zipI xys xs ys ==> zipI ((x,y)#xys)  (x#xs)  (y#ys)\"" ) ] )

(* For each production with a list form, add an additional production that uses the list version of the list form *)
let rewrite_rule ( r : rule ) : (element list list * rule ) =

  let extract_mvnt es = Auxl.option_map (fun e -> match e with
                                                     Lang_nonterm (n,_) -> Some (Lang_nonterm (n,(n,[])))
                                                   | Lang_metavar _ -> Some e
                                                   | _ -> None) es
  in
  let rewrite_element e = match e with
    | Lang_list elb -> extract_mvnt elb.elb_es
    | _ -> []
  in

  let has_list_element p = (List.length (Auxl.option_map (fun e -> match e with
                                                                  | Lang_list _ -> Some e
                                                                  | _ -> None) p.prod_es)) > 0
  in
  let list_term nme = Lang_nonterm (nme^"_list", (nme^"_list", [])) in
  (*let list_term nme = Lang_nonterm (nme, (nme, [])) in*)

  (* From dot form get pair of list of non terms and an expression for what will replace it in the production *)
  let convert_dot_form elb =
    let (es,vs) = unzip (Auxl.option_map (fun e -> match e with
                   | Lang_nonterm (ntr,nt) -> Printf.eprintf "convert_dot_form Lang_nonterm %s\n" ntr; Some ( Lang_nonterm (ntr,(ntr,[])),ntr)
                   | Lang_metavar (mvr,mv) ->  Printf.eprintf "convert_dot_form Lang_metavar %s\n" mvr; Some ( Lang_metavar (mvr,(mvr,[])),mvr)
                   | _ -> Some (e,"")) elb.elb_es)
    in
    let mvr_list = (String.concat "_" (List.filter (fun s -> String.length s > 0) vs)) ^ "_list"
    in Printf.eprintf "convert_dot_form length=%d\n" (List.length es);
       (es, Lang_nonterm (mvr_list,(mvr_list,[])))
  in
  
  (* Go though elements in production; on finding a list form convert it to a sequence of list non-terms and record 
     that we have to generate a rule for the list non-terms *)
  let process_prod_es es = List.flatten (List.map (fun e -> match e with
                                                              Lang_terminal _ -> []
                                                            | Lang_list elb -> [convert_dot_form elb]
                                                            | _ -> [([],e)]) es)
  in

  (* Either None if the p has not list elements or Some a new production to add to the list *)
  let process_prod p = if has_list_element p then
                         let (new_ntrs, new_prod_es ) = unzip (process_prod_es p.prod_es) in
                         let hom = map_sep (fun i -> Hom_index i) (Hom_string " ") (List.mapi (fun i x -> i) new_prod_es) in 
                         
                         Some (new_ntrs , { p with prod_name = p.prod_name ^ "_list";
                                                   prod_meta = true;
                                                   prod_es = (Lang_terminal (p.prod_name ^ "_list") :: new_prod_es);
                                                   prod_homs = [ ("isa", [ Hom_terminal "("; Hom_string p.prod_name ] @ hom @ [ Hom_terminal ")"] )]  })
                       else
                         None
  in
  
  let _ = Printf.eprintf "** Seeing if rule has Lang_list %s\n" (pp_plain_rule r) in

  let (new_ntrs, newprods) = unzip (Auxl.option_map (fun p -> process_prod p ) r.rule_ps) in 

  List.iter (fun p -> Printf.eprintf "** New prods for this rule: %s\n" (pp_plain_prod p)) newprods;
  let new_ntrs = new_ntrs |> List.concat  in
  Printf.eprintf "new_ntrs len = %d\n" (List.length new_ntrs);
  
  ( new_ntrs ,
    { r with rule_ps = List.append r.rule_ps newprods }) (* FIXME?Dont need to add new productions as after hom'ing will be isomorphic  *)


                              
let isa_rewrite1 (sd : systemdefn) =

  (* Fold over xd and get set of new list nonterms for list forms *)
  let new_ntrs = fold_xd {sd_id_fold_fn with f_element = (fun e b ->
                    match e with
                      Lang_list elb ->
                             let es = fold_es { sd_id_fold_fn with f_element = (fun e b ->
                                                match e with Lang_nonterm (ntr,_) -> ntr::b
                                                           | Lang_metavar (ntr,_) -> ntr::b
                                                           | _  -> b) } [] elb.elb_es in
                             ((String.concat "_" es ) ^ "_list" ,e)::b
                    | _ -> b)  } [] sd.syntax in
  let _ = List.iter (fun (s,e) -> Printf.eprintf "%s=%s\n" s (Grammar_pp.pp_plain_element e)) new_ntrs in

  let (new_rules, new_ntrs) = create_new_rules2 sd.syntax new_ntrs in
  let _ = List.iter (fun r -> Printf.eprintf "** New rule %s\n" (pp_plain_rule r)) new_rules in
  let updated_structure = ("", zip_embeds) :: (update_structure new_ntrs sd.structure) in
  Printf.eprintf "%s\n" (Auxl.dump_structure_fn updated_structure);
  let new_xd = { sd.syntax with xd_rs = List.append sd.syntax.xd_rs  new_rules } in
  let new_deps = Dependency.compute_dependencies new_xd "isa" in
  let new_xd = { new_xd with xd_dep = [ ( "isa", new_deps); ("ascii", new_deps) ] } in

  let new_relations = map_rel (fun x -> x) sd.relations in
  
  Printf.eprintf "*** FINISHED ISABELE REWRITING *** \n";
  Printf.eprintf "%s\n" (Auxl.dump_structure_fn updated_structure);
  Printf.eprintf "%s\n" (Grammar_pp.pp_syntaxdefn m_ascii new_xd);
  Printf.eprintf "%s\n" (pp_relations new_relations);
  
  { sd with syntax = new_xd;
            structure = updated_structure;
            relations = new_relations}

  
  (* map/fold over defns, for premises and conslusions, replace dot forms with list nonterm and add mapI to premises; add definitions of these
     mapI *)

    

let isa_rewrite (sd : systemdefn) =

  if List.length sd.syntax.xd_srs > 0 then raise (Invalid_argument "Rewrite with subrules not supported")
  else ();

  Printf.eprintf "Step 0 - Relations before rewrite\n";
  Printf.eprintf "%s\n" (pp_relations sd.relations);
  
  (* 1. Go over grammar rules and add a new production for each list form that uses the list version. For example, if there is a record 
        production like  | l1 = e1 .. ln = en then we add  a production  | l_e_list  *)
  let (new_ntrs, updated_rules) = List.map rewrite_rule (sd.syntax.xd_rs) |> unzip in
  let new_ntrs = new_ntrs |> List.concat |> rem_dups |> List.filter (fun e -> List.length e > 0) in

  Printf.eprintf "*** Step 1 - additional list form production ***\n";
  let _ = List.iter (fun e -> Printf.eprintf "  New rule needed for %s\n" (String.concat "*"
                                                            (List.map (fun e -> Grammar_pp.pp_plain_element e) e))) new_ntrs in

  (* 2. Calculate nonterms/metavars we need list forms for *)
  let new_ntrs_defns = fold_rel { id_fold_functions with f_nt = (fun (ntr1,(ntr2,suff)) base -> if has_index_suffix suff then Lang_nonterm (ntr1,(ntr2,[]))::base else base );
                                                         f_mv = (fun (ntr1,(ntr2,suff)) base -> if has_index_suffix suff then Lang_metavar (ntr1,(ntr2,[]))::base else base ) } [] sd.relations in

  (* Convert to use primary *)
  let new_ntrs_defns = List.map (fun e -> match e with
                                        Lang_nonterm (ntr,nt) -> let ntr = Auxl.primary_ntr_of_ntr sd.syntax ntr in
                                                                 Lang_nonterm (ntr,(ntr,[]))
                                      | Lang_metavar (mvr,mv) -> let mvd = Auxl.mvd_of_mvr_nonprimary sd.syntax mvr in
                                                                 let mvr = mvd.mvd_name in
                                                                 Lang_metavar(mvr,(mvr,[]))
                         ) new_ntrs_defns in
  
  Printf.eprintf "\n*** Step 2 - nonterms/metavars we need list forms for ***\n";
  Printf.eprintf "new_ntrs_defns size = %d\n" (List.length new_ntrs_defns);
  List.iter (fun n -> Printf.eprintf "  new_ntr %s\n" (Grammar_pp.pp_plain_element n)) new_ntrs_defns;

  (* 3. Calculate lists of 1-array elements. For example is we have f_T_list we also want f_list and T_list *)
  let single_new_ntrs = (List.map (fun es -> Auxl.option_map (fun e -> match e with
                                                                  Lang_nonterm _ -> Some [e]
                                                                | Lang_metavar _ -> Some [e]
                                                                | _ -> None) es) new_ntrs) |> List.concat in
  let new_ntrs = single_new_ntrs @ new_ntrs @ (List.map (fun e -> [e]) new_ntrs_defns) |> rem_dups in

  Printf.eprintf "\n*** Step 3 - new grammar rules needed***\n";
  let _ = List.iter (fun e -> Printf.eprintf "  New rule needed for %s\n" (String.concat "*"
                                                            (List.map (fun e -> Grammar_pp.pp_plain_element e (*match e with
                                                                     2             Lang_nonterm (s,_) -> s
                                                                                | Lang_metavar (s,_) -> s*) ) e))) new_ntrs in

  (* 4. Now create new grammer rules and primary name for list nonterminals *)
  let (new_rules, new_ntrs) = create_new_rules sd.syntax new_ntrs in

  Printf.eprintf "\n*** Step 4 - new grammer rules ***\n";
  let _ = List.iter (fun r -> Printf.eprintf "New rule %s\n" (pp_plain_rule r)) new_rules in

  (*let updated_structure = List.append sd.structure (create_new_structure new_ntrs) in *)
  let updated_structure = ("", zip_embeds) :: (update_structure new_ntrs sd.structure) in
  let new_xd = { sd.syntax with xd_rs = List.append updated_rules new_rules } in
  
  let new_deps = Dependency.compute_dependencies new_xd "isa" in
  let new_xd = { new_xd with xd_dep = [ ( "isa", new_deps); ("ascii", new_deps) ] } in

  Printf.eprintf "Syntax def start\n";
  let s = (try
      Grammar_pp.pp_syntaxdefn m_ascii new_xd
                with
                  _ -> (Printf.eprintf "SOMETHING HAPPENED\n"); "") in 
  Printf.eprintf "Syntax def %s\n" s;
 
  (* 5. In the definitions of inductive predicates, replace compound list with individual lists 
        and replace dotted judgements with use of auxilary predicates *)
  let (new_relations,new_jop_prods, new_form_prods, map_specs ) = rewrite_relations sd.relations new_xd in

  let new_xd = List.fold_left (fun xd ms  -> update_list_rule xd ms ) new_xd map_specs in 
  let new_xd = List.fold_left (fun xd (cname,new_jop_prods ) -> update_grammar_rule xd cname new_jop_prods) new_xd new_jop_prods in
  
  Printf.eprintf "|new_form_prods| =%d\n" (List.length new_form_prods);
  List.iter (fun (x, _) -> Printf.eprintf "Form = %s\n" x) new_form_prods;

  let new_xd = update_grammar_rules new_xd new_form_prods in (* FIXME - generalise Jopp *)

  Printf.eprintf "*** Step 5 - Updated inductive predicates ***\n";
  Printf.eprintf "%s\n" (pp_relations new_relations);
  
  let new_deps = Dependency.compute_dependencies new_xd "isa" in
  let new_xd = { new_xd with xd_dep = [ ( "isa", new_deps); ("ascii", new_deps) ] } in
  
  Printf.eprintf "*** FINISHED ISABELE REWRITING *** \n";
  Printf.eprintf "%s\n" (Auxl.dump_structure_fn updated_structure);
  Printf.eprintf "%s\n" (Grammar_pp.pp_syntaxdefn m_ascii new_xd);
  Printf.eprintf "%s\n" (pp_relations new_relations);

  List.iter (fun xs -> Printf.eprintf "[%s]\n" (String.concat "," (List.map string_of_int xs))) (product [ [1;2]; [3;4] ] );
  
  { sd with syntax = new_xd;
            structure = updated_structure;
            relations = new_relations}
