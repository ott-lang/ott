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

open Types;;

(* ************************************ *)
(*  merging                             *)
(* ************************************ *)

(* code to take the two endpoints of a putative ... form *)
(* and try to construct the list *)

(* here pbo ("pre-bound-option") range overs (suffix_item*suffix_item) option*)

exception Merge of string;;

exception Abstract_indexvar_non_linear;;

(* suffixes *)

let is_num_or_var : suffix_item -> bool  
    = fun suffi -> 
      match suffi with
      | Si_num _ -> true 
      | Si_punct _ -> false 
      | Si_var (_,_) -> true 
      | Si_index _ -> false 
            
let is_index : suffix_item -> bool  
    = fun suffi -> 
      match suffi with
      | Si_num _ -> false
      | Si_punct _ -> false
      | Si_var (_,_) -> false
      | Si_index _ -> true
            

let merge_suffix_item :  int 
  -> (suffix_item * suffix_item) 
    -> ((suffix_item * suffix_item) option * suffix_item) 
        = function depth -> function (suffi,suffi') -> 
          if suffi=suffi' then (None,suffi)
          else if (is_num_or_var suffi && is_num_or_var suffi') then 
            (Some(suffi,suffi'),Si_index depth)
          else
            raise (Merge "merge_suffix_item") 
      
let rec merge_suffix : int 
  -> (suffix * suffix) 
    -> ((suffix_item * suffix_item) option * suffix) 
        = fun depth -> function (suff,suff') -> 
          let xs = List.map 
              (merge_suffix_item depth) 
              (try List.combine suff suff' with 
                Invalid_argument _ -> raise 
                    (Merge "merge_suffix1 suffixes of nonequal length")) in
          let new_pbos = Auxl.option_map  (function (pbo,suffi)->pbo) xs in
          let pbo' = match new_pbos with
            [] -> None
          | [y] -> Some y
          | _ -> raise (Merge"merge_suffix2 too many suffix items changing") in
          let suff' = List.map (function (pbo,suffi)->suffi) xs in
          (pbo',suff') 



(* metavars and nonterms, in mses *)
let merge_metavar :
    int -> (metavar * metavar) -> ( bound option * metavar)
        = function dotlength -> function (mv,mv') -> 
          let (mvr,suff),(mvr',suff')=mv,mv' in
          if mvr=mvr' then 
            let pbo'',suff'' = merge_suffix 0 (suff,suff') in
            let bo''_external = match pbo'' with
            | None -> None
            | Some (suffil,suffiu)->Some (Bound_dotform {bd_lower=suffil;bd_upper=suffiu;bd_length=dotlength}) in
            (bo''_external, (mvr,suff''))
          else raise (Merge "merge_metavar - mvr does not match")

let merge_nonterm :
    int -> (nonterm * nonterm) -> ( bound option * nonterm)
        = function dotlength -> function (nt,nt') -> 
          let (ntr,suff),(ntr',suff')=nt,nt' in
          if ntr=ntr' then 
            let pbo'',suff'' = merge_suffix 0 (suff,suff') in
            let bo''_external = match pbo'' with
            | None -> None
            | Some (suffil,suffiu)->Some (Bound_dotform {bd_lower=suffil;bd_upper=suffiu;bd_length=dotlength}) in
            (bo''_external, (ntr,suff''))
          else raise (Merge "merge_nonterm - ntr does not match")


(* elements, in productions *)

let rec merge_element :
    (element * element) -> ( (suffix_item * suffix_item) option * element)
        = function (e,e') -> match e,e' with
        | Lang_nonterm(ntrp,nt),Lang_nonterm(ntrp',nt') ->
            let (ntr,suff),(ntr',suff')=nt,nt' in
            if ntr=ntr' then 
              let pbo'',suff'' = merge_suffix 0 (suff,suff') in
              if pbo''=None then raise (Merge "merge_element8 - non-varying nt");
              (pbo'',Lang_nonterm (ntrp,(ntr,suff'')))
            else raise (Merge "merge_element1 - ntr does not match")
        | Lang_metavar(mvrp,mv),Lang_metavar(mvrp',mv') ->
            let (mvr,suff),(mvr',suff')=mv,mv' in
            if mvr=mvr' then 
              let pbo'',suff'' = merge_suffix 0 (suff,suff') in
              if pbo''=None then raise (Merge "merge_element9 - non-varying mv");
              (pbo'',Lang_metavar (mvrp,(mvr,suff'')))
            else raise (Merge "merge_element2 - mvr does not match")
        | Lang_terminal tm, Lang_terminal tm' ->
            if tm=tm' then (None,Lang_terminal tm)
            else raise (Merge "merge_element3 - tm does not match")
        | Lang_sugaroption tm, Lang_sugaroption tm' ->
            if tm=tm' then (None,Lang_sugaroption tm)
            else raise (Merge "merge_element4 - tm does not match")
        | ((Lang_sugaroption _), _ | _,(Lang_sugaroption _)) ->
            raise (Merge "merge_element5 - cannot merge sugaroptions")
        | ((Lang_list _), _ | _,(Lang_list _)) ->
            raise (Merge "merge_element6 - cannot merge lists")
        | _,_ ->
            raise (Merge "merge_element7 - constructors do not match")

let rec merge_element_list : 
   int ->  (element list * element list) 
  ->  (* was ( (suffix_item * suffix_item) option * element list) *)
    (bound option * element list)
      = function dotlength -> function (es,es') -> 
        let ys = (try List.combine es es' with 
          Invalid_argument _ -> raise 
              (Merge "merge_element_list1 - lists of nonequal length")) in
        let xs = List.map merge_element ys in
        let new_pbos = Auxl.option_map  (function (pbo,suffi)->pbo) xs in
        let pbo'' = (match new_pbos with
        | [] -> None
        | y :: new_pbos' -> 
            if List.for_all (function y' -> y' = y) new_pbos' then Some y 
            else raise(Merge"merge_element_list2 - nonequal pbos")) in
        let es'' = List.map (function (pbo,suffi)->suffi) xs in
        let bo''_external = match pbo'' with
        | None -> None
        | Some (suffil,suffiu)->Some (Bound_dotform {bd_lower=suffil;bd_upper=suffiu;bd_length=dotlength}) in
        (bo''_external,es'') 


(* symterms *)
          
let rec merge_symterm : int 
  -> (symterm * symterm )
    -> ( (suffix_item * suffix_item) option * symterm)
        = fun depth -> function (st,st') -> match st,st' with
        | St_node (l,stnb), St_node (l',stnb') -> 
            let pbo'',stnb'' = 
              merge_symterm_node_body depth (stnb,stnb') (l,l') in
            pbo'', St_node (Location.merge_loc l l',stnb'')
        | St_nonterm (l,ntrp,nt), St_nonterm(l',ntrp',nt') ->
            let (ntr,suff),(ntr',suff')=nt,nt' in
            if ntr=ntr' then 
              let pbo'',suff'' = merge_suffix depth (suff,suff') in
              (pbo'',St_nonterm ((Location.merge_loc l l'),ntrp,(ntr,suff'')))
            else raise (Merge "merge_symterm1 - ntr does not match")
        | St_nontermsub(l,ntrpl,ntrpt,nt),St_nontermsub(l',ntrpl',ntrpt',nt')->
            let (ntr,suff),(ntr',suff')=nt,nt' in
            if ntrpl=ntrpl' && ntrpt=ntrpt' && ntr=ntr' then 
              let pbo'',suff'' = merge_suffix depth (suff,suff') in
              (pbo'',St_nontermsub 
                 ((Location.merge_loc l l'),ntrpl,ntrpt,(ntr,suff'')))
            else raise (Merge "merge_symterm1b - ntr does not match")
        | St_uninterpreted (l,s), St_uninterpreted (l',s') ->
            if s=s' then 
              (None,St_uninterpreted ((Location.merge_loc l l'),s))
            else raise (Merge "merge_symterm4 - string in St_uninterpreted does not match")
        | _,_ ->
            raise (Merge "merge_symterm5 - St_ constructors do not match")

                
and  merge_symterm_element : int 
  -> (symterm_element * symterm_element )
    -> ( (suffix_item * suffix_item) option * symterm_element)
        = fun depth -> function (ste,ste') -> match ste,ste' with
        | Ste_st (l,st), Ste_st (l',st') ->
            let pbo'',st'' = merge_symterm depth (st,st') in
            (pbo'',Ste_st (Location.merge_loc l l', st''))
        | Ste_metavar (l,mvrp,mv), Ste_metavar(l',mvrp',mv') ->
            let (mvr,suff),(mvr',suff')=mv,mv' in
            if mvr=mvr' then 
              let pbo'',suff'' = merge_suffix depth (suff,suff') in
              (pbo'',Ste_metavar ((Location.merge_loc l l'),mvrp,(mvr,suff'')))
            else raise (Merge "merge_symterm_element1 - mvr does not match")
        | Ste_var (l,mvrp,s), Ste_var (l',mvrp',s') ->
            if mvrp=mvrp' && s=s' then 
              (None,Ste_var ((Location.merge_loc l l'),mvrp,s))
            else raise (Merge "merge_symterm_element3 - mvr or s in Ste_var does not match")
        | Ste_list (l,stlis), Ste_list (l',stlis') -> 
            let (pbo'',stlis'') = 
              merge_symterm_list_items depth (stlis,stlis') (l,l') in
            (pbo'',Ste_list ((Location.merge_loc l l'),stlis''))
        | _ -> raise (Merge "symterm_element - incompatible structure")
              
and merge_symterm_element_list : int 
  -> (symterm_element list * symterm_element list) 
    ->  ( (suffix_item * suffix_item) option * symterm_element list)
        = function depth -> function (es,es') -> 
          let ys = (try List.combine es es' with 
            Invalid_argument _ -> raise 
                (Merge "merge_symterm_element_list7 - st lists of nonequal length")) in
          let xs = List.map (merge_symterm_element depth) ys in
          let new_pbos = Auxl.option_map  (function (pbo,suffi)->pbo) xs in
          let pbo'' = (match new_pbos with
          | [] -> None
          | y :: new_pbos' -> 
              if List.for_all (function y' -> y' = y) new_pbos' then Some y 
              else raise(Merge"merge_symterm_element_list8 - nonequal pbos")) in
          let es'' = List.map (function (pbo,suffi)->suffi) xs in
          (pbo'',es'') 
            
and merge_symterm_node_body : int 
  -> (symterm_node_body * symterm_node_body )
    -> loc * loc 
      -> ( (suffix_item * suffix_item) option * symterm_node_body)
          = fun depth -> function (stnb,stnb') -> function (l,l') ->
            if stnb.st_rule_ntr_name <> stnb'.st_rule_ntr_name then 
              raise (Merge "merge_symterm_node_body - rnn does not match");
            if stnb.st_prod_name <> stnb'.st_prod_name then 
              raise (Merge "merge_symterm_node_body - pn does not match");
            let (pbo'',es'')= merge_symterm_element_list 
                depth 
                (stnb.st_es,stnb'.st_es) in
            let stnb'' = 
              {st_rule_ntr_name=stnb.st_rule_ntr_name;
               st_prod_name=stnb.st_prod_name;
               st_es=es'';
               st_loc=Location.merge_loc l l'} in
            (pbo'',stnb'')
        
and merge_symterm_list_items : int 
  -> (symterm_list_item list * symterm_list_item list )
    -> loc * loc
      -> ( (suffix_item * suffix_item) option * symterm_list_item list)
          = fun depth -> function (stlis,stlis') -> function (l,l') ->
            let ys = (try List.combine stlis stlis' with 
              Invalid_argument _ -> raise 
                  (Merge "merge_symterm_list_items - stlis lists of nonequal length")) in
            let xs = List.map (merge_symterm_list_item depth) ys in
            let new_pbos = Auxl.option_map  (function (pbo,suffi)->pbo) xs in
            let pbo'' = (match new_pbos with
            | [] -> None
            | y :: new_pbos' -> 
                if List.for_all (function y' -> y' = y) new_pbos' then Some y 
                else raise(Merge"merge_symterm_list_items - nonequal pbos")) in
            let stlis'' = List.map (function (pbo,suffi)->suffi) xs in
            (pbo'',stlis'') 

and merge_symterm_list_item : int 
  -> (symterm_list_item * symterm_list_item )
      -> ( (suffix_item * suffix_item) option * symterm_list_item)
          = fun depth -> function (stli,stli') -> 
            match stli,stli' with 
            | Stli_single (l1,stes),Stli_single(l1',stes') ->
                let (pbo'',stes'') = merge_symterm_element_list depth (stes,stes') in
                (pbo'',Stli_single(Location.merge_loc l1 l1',stes''))
            | Stli_listform stlb,Stli_listform stlb'->
                let (pbo'',stlb'') = merge_symterm_list_body depth (stlb,stlb') in
                (pbo'',Stli_listform stlb'')
            | _ -> raise (Merge "merge_symterm_list_item - structure does not match")

and merge_symterm_list_body : int 
  -> (symterm_list_body * symterm_list_body )
      -> ( (suffix_item * suffix_item) option * symterm_list_body)
          = fun depth -> function (stlb,stlb') -> 
            if stlb.stl_bound <> stlb'.stl_bound then 
              raise (Merge "merge_symterm_list_body - bound parts do not match");
            let (pbo'',es'') = merge_symterm_element_list
                (depth+1) 
                (stlb.stl_elements,stlb'.stl_elements) 
            in
            (* TODO sort out these depths *)
            let stlb'' = 
              { stl_bound=stlb.stl_bound;
                stl_elements=es'';
              (*  stl_indexed_things=stlb.stl_indexed_things (* TODO WHY?*); *)
                stl_loc = Location.merge_loc stlb.stl_loc stlb'.stl_loc} in
            (pbo'',stlb'')



(* merging a suffix against one with a single index, for bound extraction *)
let merge_suffix_item_against_index :  int 
  -> (suffix_item * suffix_item) 
    -> ((suffix_item * suffix_item) option * suffix_item) 
        = function depth -> function (suffi,suffi') -> 
          if suffi=suffi' then (None,suffi)
          else if (is_num_or_var suffi && is_index suffi') then 
            (Some(suffi,suffi'),Si_index depth)
          else
            raise (Merge "merge_suffix_item_against_index") 
      
let rec merge_suffix_against_index : int 
  -> (suffix * suffix) 
    -> ((suffix_item * suffix_item) option * suffix) 
        = fun depth -> function (suff,suff') -> 
          let xs = List.map 
              (merge_suffix_item_against_index depth) 
              (try List.combine suff suff' with 
                Invalid_argument _ -> raise 
                    (Merge "merge_suffix_against_index1 suffixes of nonequal length")) in
          let new_pbos = Auxl.option_map  (function (pbo,suffi)->pbo) xs in
          let pbo' = match new_pbos with
            [] -> None
          | [y] -> Some y
          | _ -> raise (Merge"merge_suffix_against_index2 too many suffix items changing") in
          let suff' = List.map (function (pbo,suffi)->suffi) xs in
          (pbo',suff') 

(* abstracting an indexvar from a suffix *)

let abstract_indexvar_suffix_item : metavarroot -> int -> suffix_item -> suffix_item
    = fun ivr depth suffi ->
      match suffi with
      | Si_num _ 
      | Si_punct _
      | Si_index _ -> suffi
      | Si_var (ivr',n') when ivr'=ivr -> 
          if n'=0 then Si_index depth
          else failwith "non-zero suffix offset in abstract_indexvar_suffix_item"
      | Si_var (_,_) -> suffi

let abstract_indexvar_suffix : metavarroot -> int -> suffix -> suffix
    = fun ivr depth suff ->
      List.map (abstract_indexvar_suffix_item ivr depth) suff

(* ... and the same, but count how many occurrences of ivr we replaced *)
let abstract_indexvar_suffix_item_count : metavarroot -> int -> suffix_item -> suffix_item * int
    = fun ivr depth suffi ->
      match suffi with
      | Si_num _ 
      | Si_punct _
      | Si_index _ -> suffi,0
      | Si_var (ivr',n') when ivr'=ivr -> 
          if n'=0 then Si_index depth,1
          else failwith "non-zero suffix offset in abstract_indexvar_suffix_item_count"
      | Si_var (_,_) -> suffi,0

let rec abstract_indexvar_suffix_count : metavarroot -> int -> suffix -> suffix*int
    = fun ivr depth suff ->
      match suff with
      | [] -> [],0
      | suffi::suff -> 
          let suffi',x = abstract_indexvar_suffix_item_count ivr depth suffi in
          let suff',y = abstract_indexvar_suffix_count ivr depth suff in
          suffi'::suff',(x+y)

let abstract_indexvar_suffix_linear : metavarroot -> int -> suffix -> suffix
    = fun ivr depth suff ->
      let suff',y = abstract_indexvar_suffix_count ivr depth suff in
      if y=1 then suff' 
      else raise Abstract_indexvar_non_linear 

(* abstracting an indexvar from a symterm, replacing it by the (suitably adjusted) de bruijn index, and checking that each nonterm or metavar does mention the indexvar *)
let rec abstract_indexvar_element : metavarroot -> int -> element -> element
    = fun ivr depth e -> 
      match e with
      | Lang_nonterm (ntrp,(ntr,suff)) -> 
          Lang_nonterm(ntrp, (ntr,abstract_indexvar_suffix_linear ivr depth suff))
      | Lang_metavar (mvrp,(mvr,suff)) -> 
          Lang_metavar(mvrp, (mvr,abstract_indexvar_suffix_linear ivr depth suff))
      | Lang_terminal tm -> e
      | Lang_option _ -> failwith "abstract_indexvar_element Lang_option not implemented"
      | Lang_sugaroption _ -> failwith "abstract_indexvar_element Lang_sugaroption not implemented"
      | Lang_list elb ->
          Lang_list
            {elb with elb_es = List.map (abstract_indexvar_element ivr (depth+1)) elb.elb_es }

(* abstracting an indexvar from a symterm, replacing it by the (suitably adjusted) de bruijn index *)


let rec abstract_indexvar_symterm : metavarroot -> int -> symterm -> symterm
    = fun ivr depth st -> match st with
    | St_node(l,stnb)->St_node(l,abstract_indexvar_symterm_node_body ivr depth stnb)
    | St_nonterm(l,ntrp,(ntr,suff)) -> St_nonterm(l,ntrp, (ntr,abstract_indexvar_suffix ivr depth suff))
    | St_nontermsub(l,ntrpl,ntrpt,(ntr,suff)) -> St_nontermsub(l,ntrpl,ntrpt,(ntr,abstract_indexvar_suffix ivr depth suff))
    | St_uninterpreted(l,s) -> st

and abstract_indexvar_symterm_node_body : metavarroot -> int -> symterm_node_body -> symterm_node_body
    = fun ivr depth stnb -> 
      { stnb with st_es = List.map (abstract_indexvar_symterm_element ivr depth) stnb.st_es }

and abstract_indexvar_symterm_element : metavarroot -> int -> symterm_element -> symterm_element
    = fun ivr depth ste -> match ste with
    | Ste_st(l,st) -> Ste_st(l,abstract_indexvar_symterm ivr depth st)
    | Ste_metavar(l,mvrp,(mvr,suff)) -> Ste_metavar(l,mvrp, (mvr,abstract_indexvar_suffix ivr depth suff))
    | Ste_var(l,mvr,var) -> ste
    | Ste_list(l,stlis) -> Ste_list(l,List.map (abstract_indexvar_symterm_list_item ivr depth) stlis)

and abstract_indexvar_symterm_list_item : metavarroot -> int -> symterm_list_item -> symterm_list_item
    = fun ivr depth stli -> match stli with
    | Stli_single(l,stes) -> Stli_single(l,List.map (abstract_indexvar_symterm_element ivr depth) stes)
    | Stli_listform(stlb) -> Stli_listform(abstract_indexvar_symterm_list_body ivr depth stlb)

and abstract_indexvar_symterm_list_body : metavarroot -> int -> symterm_list_body -> symterm_list_body
    = fun ivr depth stlb -> 
      {stlb with stl_elements=List.map (abstract_indexvar_symterm_element ivr (depth+1)) stlb.stl_elements}


