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

(* FZ: is this comment outdated ? *)
(* FZ: only for Coq, only the bare grammar (no homs...),  *)
(*     only for very simple suffixes *)
  
type int_code =
  | Ic_None
  | Ic_Aux of auxfn * nontermroot * nt_or_mv_root
  | Ic_MetaVarListExp of auxfn * metavarroot * nt_or_mv_root
  | Ic_NonTermListExp of auxfn * nontermroot * nt_or_mv_root

let dummy_ret_type = Ntr "dummy_ret_type"

let make_aux_list_funcs (b : Buffer.t) xd t s =
  (* the variable l should be fresh wrt all types - mvrs and ntrs *)
  (* the code below is an hack and does not guarantee freshening if mv/rule homs are used *)
  let l = 
    let ntrs = List.map (fun r -> r.rule_ntr_name) xd.xd_rs in
    let mvrs = List.map (fun mvd -> mvd.mvd_name) xd.xd_mds in
    let used = ntrs @ mvrs in
    let rec find_unused_suffix n =
      let ns = string_of_int n in
      if List.mem ("l"^ns) used then find_unused_suffix (n+1) else ns in
    if List.mem "l" used then "l"^(find_unused_suffix 0) else "l"
  in
  let hl = 
    if List.length t = 1 then [ "h" ]
    else
      let c = ref (-1) in
      List.map (fun _ -> c:=!c+1; "h"^(string_of_int !c)) t in
  let h = String.concat " " hl in
  let h_comma = if List.length hl = 1 then h else "(" ^ String.concat "," hl ^ ")" in
  let t_arrow = String.concat "->" t in
  let t' = if List.length t = 1 then t_arrow else "(" ^ String.concat " * " t ^ ")" in
  (* map *)
  Printf.bprintf b "Fixpoint map_%s (A:Set) (f:%s->A) (%s:%s) : list A :=\n" s t_arrow l s;
  Printf.bprintf b "  match %s with\n" l;
  Printf.bprintf b "  | Nil_%s => nil\n" s;
  Printf.bprintf b "  | Cons_%s %s tl_ => cons (f %s) (map_%s A f tl_)\n  end.\n" s h h s;
  Printf.bprintf b "Implicit Arguments map_%s.\n\n" s;
  (* make *)
  Printf.bprintf b "Fixpoint make_%s (%s: list %s): %s :=\n" s l t' s;
  Printf.bprintf b "  match %s with\n" l;
  Printf.bprintf b "  | nil  => Nil_%s\n" s;
  Printf.bprintf b "  | cons %s tl_ => Cons_%s %s (make_%s tl_)\n  end.\n\n" h_comma s h s;
  (* unmake *)
  Printf.bprintf b "Fixpoint unmake_%s (%s: %s): list %s :=\n" s l s t';
  Printf.bprintf b "  match %s with\n" l;
  Printf.bprintf b "  | Nil_%s => nil\n" s;
  Printf.bprintf b "  | Cons_%s %s tl_ => cons %s (unmake_%s tl_)\n  end.\n\n" s h h_comma s;
  (* nth *)
  Printf.bprintf b "Fixpoint nth_%s (n:nat) (%s: %s) {struct n} : option %s :=\n" s l s t';
  Printf.bprintf b "  match n,%s with\n" l;
  Printf.bprintf b "  | O, Cons_%s %s tl_ => Some %s\n" s h h_comma;
  Printf.bprintf b "  | O, _ => None\n";
  Printf.bprintf b "  | S m, Nil_%s => None\n" s;
  Printf.bprintf b "  | S m, Cons_%s %s tl_ => nth_%s m tl_\n" s h s;
  Printf.bprintf b "  end.\n\n";
  (* app *)
  Printf.bprintf b "Fixpoint app_%s (%s m: %s): %s :=\n" s l s s;
  Printf.bprintf b "  match %s with\n" l;
  Printf.bprintf b "  | Nil_%s => m\n" s;
  Printf.bprintf b "  | Cons_%s %s tl_ => Cons_%s %s (app_%s tl_ m)\n" s h s h s;
  Printf.bprintf b "  end.\n\n"

let pp_list_rule (fd : out_channel) xd (ss:nt_or_mv_root list) : unit  =
  let to_string ntmvr =
    match ntmvr with Ntr ntr -> ntr | Mvr mvr -> mvr in
  let sss = List.map to_string ss in
  let name = String.concat "_" sss in

  let id = ("list_" ^ name) in
  let id_nt = (id,[]) in
  Printf.fprintf fd "Inductive %s : Set := Nil_%s | Cons_%s" id id id;
  List.iter (fun s -> Printf.fprintf fd " (_:%s)" s) sss;
  Printf.fprintf fd " (tl_ : %s).\n\n" id;
  let b = Buffer.create 2040 in
  make_aux_list_funcs b xd sss id;
  Buffer.output_buffer fd b


let expand_element (m:pp_mode) (xd:syntaxdefn) (bs:bindspec list) (e:element) : 
    element * bindspec list * rule list * (auxfn * auxfn_type) list =
  match e with
  | Lang_list elb -> 
      let ss = 
	Auxl.option_map 
	  ( fun e -> 
	    match e with
	    | Lang_nonterm (ntr,_) -> Some (Ntr (Auxl.promote_ntr xd ntr))
	    | Lang_metavar (mvr,_) -> Some (Mvr mvr)
            | Lang_terminal t -> None
	    | _ -> Auxl.error "internal: expand element, cannot happen.\n" )
	  elb.elb_es in

      let id = (*Auxl.pp_coq_type_name*)
		  ("list_" ^ (String.concat "_" 
                                (List.map (Grammar_pp.pp_nt_or_mv_root_ty m xd) ss))) in
      let id_nt = (id,[]) in
      let id_el = Lang_nonterm (id,id_nt) in

      (* if all ntmvr are in Set then the universe of the list type is Set, otherwise it is Type *)
      (* FZ: this is sensible in some common cases, not sure it is always correct *)
      let id_universe = 
        let universes = 
          List.map (fun mvntr -> 
            match mvntr with
            | Ntr ntr -> 
                ( try Grammar_pp.pp_hom_spec m xd (List.assoc "coq-universe" (Auxl.rule_of_ntr xd ntr).rule_homs) 
                with Not_found -> "Set" )
            | Mvr _ -> "Set") ss in
        if List.for_all (fun s -> String.compare s "Set" = 0) universes
        then "Set"
        else "Type"
      in

      let rec update_bs bs ss =
        ( match bs with

        | AuxFnDef (f,AuxList (g,(nt,s),b)) :: t ->
            if List.mem (Ntr nt) ss   (* FZ add primary? *)
            then ((AuxFnDef (f,Aux (g,id_nt))), Ic_Aux (g,nt,dummy_ret_type)) :: (update_bs t ss)
            else ((AuxFnDef (f,AuxList (g,(nt,s),b))), Ic_None) :: (update_bs t ss) 

        | AuxFnDef (f,NonTermListExp ((ntr,s),b)) :: t -> 
            if List.mem (Ntr (Auxl.primary_ntr_of_ntr xd ntr)) ss
            then ((AuxFnDef (f,Aux (f,id_nt))), Ic_NonTermListExp (f,ntr,dummy_ret_type) ) :: (update_bs t ss)
            else ((AuxFnDef (f,NonTermListExp ((ntr,s),b))), Ic_None) :: (update_bs t ss) 

        | AuxFnDef (f,MetaVarListExp ((mvr,s),b)) :: t -> 
            if List.mem (Mvr (Auxl.primary_mvr_of_mvr xd mvr)) ss
            then ((AuxFnDef (f,Aux (f,id_nt))), Ic_MetaVarListExp (f,mvr,dummy_ret_type) ) :: (update_bs t ss)
            else ((AuxFnDef (f,MetaVarListExp ((mvr,s),b))), Ic_None) :: (update_bs t ss) 

        | Bind ((NonTermListExp ((ntr,s),b)), nt) :: t ->  
            let auxfnname= "bind_"^id in
            if List.mem (Ntr (Auxl.primary_ntr_of_ntr xd ntr)) ss
            then (Bind ((Aux (auxfnname,id_nt)),nt), Ic_NonTermListExp (auxfnname,ntr,Ntr ntr)) :: (update_bs t ss)
            else (Bind ((NonTermListExp ((ntr,s),b)),nt), Ic_None) :: (update_bs t ss) 

        | Bind ((MetaVarListExp ((mvr,s),b)), nt) :: t ->  
            let auxfnname= "bind_"^id in
            if List.mem (Mvr (Auxl.primary_mvr_of_mvr xd mvr)) ss
            then (Bind ((Aux (auxfnname,id_nt)),nt), Ic_MetaVarListExp (auxfnname,mvr,Mvr mvr)) :: (update_bs t ss)
            else (Bind ((MetaVarListExp ((mvr,s),b)),nt), Ic_None) :: (update_bs t ss) 
                
        | b :: t -> (b,Ic_None)::(update_bs t ss)
        | [] -> [] ) in

      let bs_n,aux_to_def = (List.split (update_bs bs ss)) in

      let nil_prod = 
	{ prod_name = "Nil_" ^ id;  
	  prod_flavour = Bar;
	  prod_meta = false;
	  prod_sugar = false;
          prod_categories = StringSet.empty;
	  prod_es = [];
	  prod_homs = [];
          prod_disambiguate = None;
	  prod_bs = Auxl.option_map
            ( fun i -> 
              match i with 
              | Ic_None -> None
              | Ic_Aux (f,_,_) -> Some (AuxFnDef (f,Empty))
              | Ic_MetaVarListExp (f,_,_) -> Some (AuxFnDef (f,Empty))
              | Ic_NonTermListExp (f,_,_) -> Some (AuxFnDef (f,Empty)) )
            aux_to_def;
	  prod_loc = dummy_loc } in

      let cons_prod = 
	let remove_suffix e = (* FZ works only for very simple suffixes *)
	  ( match e with
	  | Lang_nonterm (ntr,(ntr',_)) -> Lang_nonterm (ntr,(ntr',[]))
	  | Lang_metavar (mvr,(mvr',_)) -> Lang_metavar (mvr,(mvr',[])) 
          | Lang_terminal t -> Lang_terminal t
          | _ -> Auxl.error "internal: remove suffix, cannot happen\n" ) in
	{ prod_name = "Cons_" ^ id;  
	  prod_flavour = Bar;
	  prod_meta = false;
	  prod_sugar = false;
          prod_categories = StringSet.empty;
	  prod_es = (List.map remove_suffix elb.elb_es) @ [ id_el ];
	  prod_homs = [];
          prod_disambiguate = None;
	  prod_bs = Auxl.option_map
            ( fun i ->
              match i with
              | Ic_None -> None
              | Ic_Aux (f,nt,_) ->         (* FZ simple suffixes only *)
                  let mse = Union (Aux (f,(nt,[])), Aux (f,id_nt)) in
                  Some (AuxFnDef (f,mse))
              | Ic_MetaVarListExp (f,mvr,_) -> 
                  let mse = Union ((MetaVarExp (mvr,[])), Aux (f,id_nt) ) in
                  Some (AuxFnDef (f,mse)) 
              | Ic_NonTermListExp (f,ntr,_) -> 
                  let mse = Union ((NonTermExp (ntr,[])), Aux (f,id_nt) ) in
                  Some (AuxFnDef (f,mse)) )
            aux_to_def;
	  prod_loc = dummy_loc } in

      let aux_rule = 
	{ rule_ntr_name = id; 
	  rule_ntr_names = [ (id,[]) ];
	  rule_pn_wrapper = "";
	  rule_ps = [ nil_prod; cons_prod ];
	  rule_homs = [("coq-universe", [Hom_string id_universe])];
	  rule_meta = false;
	  rule_semi_meta = false;
          rule_phantom = false;
	  rule_judgement = false;
	  rule_loc = dummy_loc } in

      let xtd_auxfns = 
        Auxl.option_map
          ( fun i ->
            match i with
            | Ic_None -> None
            | Ic_Aux (f,_,rt) -> Some (f,([id],rt))
            | Ic_MetaVarListExp (f,_,rt) -> Some (f,([id],rt))
            | Ic_NonTermListExp (f,_,rt) -> Some (f,([id],rt)) )
          aux_to_def in

      id_el, bs_n, [ aux_rule ], xtd_auxfns

  | _ -> e, bs, [], []

let expand_prod (m:pp_mode) (xd:syntaxdefn) (p:prod) : prod * rule list * (auxfn * auxfn_type) list =
  let rec expand_prod_int 
      (bs:bindspec list) (els:element list) : element list * bindspec list * rule list * (auxfn * auxfn_type) list =
    match els with
    | h::t -> 
        let e',bs',r',x' = expand_element m xd bs h in
        let els'',bs'',rl'',x'' = expand_prod_int bs' t in
        (e'::els'', bs'', r' @ rl'', x' @ x'')
    | [] -> [], bs ,[], [] in
  let els_n, bs_n, rl_n, x_n = expand_prod_int p.prod_bs p.prod_es in
  ( { p with prod_es = els_n; prod_bs = bs_n }, rl_n, x_n )

let expand_rule (m:pp_mode) (xd:syntaxdefn) (r:rule) : rule list * string list * (auxfn * auxfn_type) list =
  if 
    (String.compare r.rule_ntr_name "formula" = 0) || 
    (List.exists (fun (h,_) -> String.compare h "coq" = 0) r.rule_homs)
  then ([r],[],[])
  else
    let expanded_prods, new_rules, extended_auxfns = 
      (fun (x,y,z) -> x, List.concat y, List.concat z)
        (Auxl.split3 (List.map (expand_prod m xd) r.rule_ps)) in
    (* loc of the new rules to be the same of r *)
    let new_rules = List.map (fun nr -> { nr with rule_loc = r.rule_loc }) new_rules in
    let new_rule_names = List.map (fun r -> r.rule_ntr_name) new_rules in
    ({ r with rule_ps = expanded_prods } :: new_rules, new_rule_names, extended_auxfns)

let rec remove_duplicates_expanded_rules er =
  match er with
  | x::xs -> 
      if (List.exists (fun r -> r.rule_ntr_name = x.rule_ntr_name) xs) 
      then remove_duplicates_expanded_rules xs 
      else x::(remove_duplicates_expanded_rules xs)
  | [] -> []

let expand_lists_in_syntaxdefn (m:pp_mode) (xd:syntaxdefn) (structure: structure) : syntaxdefn * structure =
  match m with 
  | Coq co when co.coq_expand_lists ->
      let expanded_list_ntrs = ref [] in
      let newstruct = ref [] in

      let stre_to_expanded br =
        newstruct := [];
        let exp =  (* the rules *)
          List.map 
            (fun ntr ->
              let r = Auxl.rule_of_ntr xd ntr in
              let ers,nntrs,eauxfns = expand_rule m xd r in
              let newntrs = Auxl.remove_duplicates 
                  (List.filter (fun ntr -> not (List.mem ntr !expanded_list_ntrs)) nntrs) in
              expanded_list_ntrs := newntrs @ !expanded_list_ntrs;
              newstruct := newntrs @ !newstruct;
              (ers, nntrs, eauxfns))
            br in

        let exp_list_aux_funcs = (* and the auxiliary list functions *)
          let extract_type x =
            let rec remove_last l =
              match l with
              | [] -> Auxl.int_error "expand_lists_in_syntaxdefn"
              | h1::[] -> []
              | h::t -> h::(remove_last t) in
            let expanded_rules = List.concat (List.map (fun (x,_,_) -> x) exp) in
            let r = List.find (fun r -> r.rule_ntr_name = x) expanded_rules in
            let p = List.hd (List.tl r.rule_ps) in
            let e = remove_last p.prod_es in
            Auxl.option_map (fun e -> Grammar_pp.pp_element m xd [] true e) e in
          match !newstruct with
          | [] -> ""
          | l ->  let b = Buffer.create (2000 * List.length l) in
          List.iter (fun x -> make_aux_list_funcs b xd (extract_type x) x) l;
          Buffer.contents b
        in

        if exp_list_aux_funcs = ""
        then [(Struct_rs (!newstruct@br), Some exp)]
        else [(Struct_rs (!newstruct@br), Some exp); 
              (Struct_embed (dummy_loc, "coq", [Embed_string (dummy_loc, exp_list_aux_funcs)]), None)] in 
      
      let (expanded_structure,exp) = 
        List.split (List.concat (List.map
          (fun (fn,stre) -> 
            match stre with
            | Struct_rs ntrs -> (List.map (fun (stre,x) -> ((fn,stre),x)) (stre_to_expanded ntrs))  (* FZ suspicious *)
            | _ -> [((fn,stre), None)]
          )
          structure)) in
      
      let expanded_rules, new_rule_names, extended_auxfns =
        (fun (x,y,z) -> 
          (remove_duplicates_expanded_rules (List.concat x)), 
          (Auxl.remove_duplicates (List.concat y)), 
          (Auxl.remove_duplicates (List.concat z)))
        (Auxl.split3 (List.concat (Auxl.option_map (fun x -> x) exp))) in
        
      
      (* let expanded_rules, new_rule_names, extended_auxfns =  *)
      (*   (fun (x,y,z) ->  *)
      (*     (remove_duplicates_expanded_rules (List.concat x)),  *)
      (*     (Auxl.remove_duplicates (List.concat y)),  *)
      (*     (Auxl.remove_duplicates (List.concat z))) *)
      (*     (Auxl.split3 (List.map (expand_rule xd) xd.xd_rs)) in *)

      co.coq_list_types := new_rule_names;

      (* WILL BE DEAD CODE FROM HERE *)
      let list_aux_funcs =
        let extract_type x =
          let rec remove_last l =
            match l with
            | [] -> Auxl.int_error "list_aux_funcs, transform.ml"
            | h1::[] -> []
            | h::t -> h::(remove_last t) in
          let r = List.find (fun r -> r.rule_ntr_name = x) expanded_rules in
          let p = List.hd (List.tl r.rule_ps) in
          let e = remove_last p.prod_es in
          Auxl.option_map (fun e -> Grammar_pp.pp_element m xd [] true e) e in
        match new_rule_names with [] -> "" | l -> 
        let b = Buffer.create (2000 * List.length l) in
        List.iter (fun x -> make_aux_list_funcs b xd (extract_type x) x) l;
        Buffer.contents b
      in

      (* first update the aux list funcs *)
      Auxl.the (co.coq_list_aux_funcs) := list_aux_funcs;
      (* TO HERE *)

      (* concat and merge later *)
      let expanded_auxfns = 
        let tmp_auxfns = xd.xd_axs @ extended_auxfns in (* HACK: this order is important *)
        let rec merge axs =
          ( match axs with
          | [] -> []
          | (f,(ntl,ntmvr))::tl -> 
              let new_tail = List.filter (fun (g,d) -> not (String.compare f g = 0)) tl in
              let all_same = List.filter (fun (g,d) -> (String.compare f g = 0)) tl  in
              let collected_ntl = 
                List.concat 
                  (List.map 
                     (fun (_,(ntl',ntmvr')) -> (* FZ add a test on ntmvr *) ntl') 
                     all_same) in
              (f,(collected_ntl@ntl,ntmvr)) :: (merge new_tail) )
        in merge tmp_auxfns 
      in
 
      let expanded_deps = 
	Dependency.compute_dependencies 
	  { xd with xd_rs = expanded_rules; xd_dep = [] } "coq" in
      { xd with
	xd_rs = expanded_rules;
	xd_dep = [ ("coq", expanded_deps); ("ascii", expanded_deps) ];
        xd_axs = expanded_auxfns },
      expanded_structure

  | _ -> xd, structure

