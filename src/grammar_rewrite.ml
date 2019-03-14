(* Some tools for rewriting and walking over symterms *)


open Types
  
let strip_index_suffix (nt,suff) = (nt, Auxl.option_map (fun s -> match s with Si_index _ -> None | _ -> Some s) suff)

let has_num_suffix suffix = (List.length (Auxl.option_map (fun s -> match s with Si_num _ -> Some s | _ -> None) suffix)) > 0
let has_index_suffix suffix = (List.length (Auxl.option_map (fun s -> match s with Si_index _ -> Some s | _ -> None) suffix)) > 0

                                                                                                                                  (*--------------------------------------------------------------------------------------
 
   Facilities for mapping and folding over symterm trees

----------------------------------------------------------- *)  
                                           
type map_functions = {
    f_st : symterm -> symterm;
    f_stnb : symterm_node_body -> symterm_node_body;
    f_nt : (nontermroot*nonterm) -> (nontermroot*nonterm);
    f_mv : (metavarroot*metavar) -> (metavarroot*metavar);
    f_stlb : symterm_list_body -> symterm_list_body;
    f_ste_list : symterm_list_item list -> symterm_list_item list
  }

let id_mf = {
    f_st = (fun x -> x);
    f_stnb = (fun x -> x);
    f_nt = (fun x -> x);
    f_mv = (fun x -> x);
    f_stlb = (fun x -> x);
    f_ste_list = (fun x -> x)
  }

let rec map_st (f : map_functions) st = match st with
  | St_node (l,stnb) ->  let stnb = f.f_stnb stnb in
                         St_node(l, { stnb  with st_es = List.map (map_ste f) stnb.st_es })
  | St_nonterm (l,ntr,nt) -> let (ntr,nt) = f.f_nt (ntr,nt) in St_nonterm(l,ntr,nt)
  | _ -> st
and map_ste (f : map_functions) ste = match ste with
  | Ste_st(l,st) -> Ste_st (l, f.f_st (map_st f st))
  | Ste_metavar(l,mvr,mv) -> let (mvr,mv) = f.f_mv (mvr,mv) in Ste_metavar(l,mvr,mv)
  | Ste_list (l,stlis) -> let stlis = f.f_ste_list stlis in
                          Ste_list(l,List.map (map_stli f) stlis)
and map_stli f stli = match stli with
  | Stli_single(l,stes) -> Stli_single(l,List.map (map_ste f) stes)
  | Stli_listform stlb -> Stli_listform { (f.f_stlb stlb) with stl_elements = map_stes f stlb.stl_elements } 
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
  in List.fold_left (fun x (_, p, _) -> fold_st f x p) base dr.drule_premises
                           
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

                                    
let update_grammar_rule xd name prods = 
  { xd with xd_rs = List.map (fun r ->
                        if r.rule_ntr_name = name  then
                          { r with rule_ps = r.rule_ps @  prods }
                        else r) xd.xd_rs }

let update_grammar_rules xd prods =
  List.fold_left (fun xd (name,prods)  -> update_grammar_rule xd name prods) xd prods

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

                 
let create_defn_prod (cname : string ) (dname : string) (st : symterm) = newprod ( dname ) (Lang_terminal (dname ) ::
                   (fold_st { id_fold_functions with f_nt = (fun nt base -> List.append base [ rename_nt nt ]);
                                                     f_mv = (fun mv base -> List.append base [ rename_mv mv ]) } [] st)) []
