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

exception NotImplementedYet;;

open Types;;
open Location;;

exception Bounds of string


(** ******************************** *)
(** bounds extraction                *)
(** ******************************** *)

(* let pp_plain_b (suffil,suffiu) = *)
(*       "(" *)
(*       ^ Grammar_pp.pp_plain_suffix_item suffil ^"," *)
(*       ^ Grammar_pp.pp_plain_suffix_item suffiu  *)
(*       ^ ")" *)

(*let sie_project = [Si_var ("_",0)]  *)
let sie_project = [Si_punct "_"] 
let sie_null = [Si_punct ""]                                         

(* given a bounds environment be and a suffix suff, return at most one bound *)
(* referenced in the suffix. fail if the suffix references >1 bound*)
let findbounds (be : bound list) (suff : suffix) : bound option
    = let rec indices suff = 
      match suff with
      | [] -> []
      | (Si_num _ | Si_punct _ | Si_var (_,_))::suff' -> indices suff'
      | Si_index i :: suff' ->  i :: indices suff' in
    (*print_string (String.concat " " (List.map pp_plain_bound be) ^"\n");flush stdout;*)
    match indices suff with
    | [] -> None
    | [i] -> (*print_string ("<<<< "^string_of_int i^" >>>>");flush stdout;*)
        Some(List.nth be i)
    | _ -> raise (Bounds "findbounds: multiple suffix indices in a suffix")

(* collect all the nonterms/metavars in a symterm *)
(* (and their nontermsub-lower-and-top data if they have it), *)
(* together with their bounds and length constraints if they have them  *)
let rec nt_or_mv_of_symterm (be : bound list) st 
: ((nt_or_mv * subntr_data) * bound option ) list = 
  match st with
  | St_node (_,stnb) -> nt_or_mv_of_symterm_node_body be stnb
  | St_nonterm (_,_,(ntr,sf)) -> [ (((Ntr ntr),sf),None),findbounds be sf ]  
  | St_nontermsub (_,ntrl,ntrt,(ntr,sf)) -> [(((Ntr ntr),sf),Some(ntrl,ntrt(*ntru*))),findbounds be sf ]
  | St_uninterpreted (_,_)-> []
and nt_or_mv_of_symterm_element be ste =
  match ste with
  | Ste_st (_,st) -> nt_or_mv_of_symterm be st
  | Ste_metavar (_,_,(mvr,sf)) -> [ (((Mvr mvr),sf),None),findbounds be sf ]
  | Ste_var _ -> []
  | Ste_list (_,stlis)  -> 
      List.concat (List.map (nt_or_mv_of_symterm_list_item be) stlis)
and nt_or_mv_of_symterm_list_item be stli = 
  match stli with
  | Stli_single(_,stes) ->
      List.concat (List.map (nt_or_mv_of_symterm_element be) stes)
  | Stli_listform stlb -> 
      nt_or_mv_of_symterm_list_body be stlb
and nt_or_mv_of_symterm_node_body be stnb = 
  List.concat (List.map (nt_or_mv_of_symterm_element be) stnb.st_es)
and nt_or_mv_of_symterm_list_body be stlb =    
  let be' = stlb.stl_bound :: be in
  List.concat (List.map (nt_or_mv_of_symterm_element be') stlb.stl_elements)
    
let nt_or_mv_of_symterms sts = 
  List.concat (List.map (nt_or_mv_of_symterm []) sts)


(* check for each Bound_dotform bound that it occurs with only one length constraint. Return the bounds without duplicates *)
let check_length_consistency : 
    ((nt_or_mv* subntr_data) * bound option ) list ->  bound list 
        = 
      function xys ->
        let bounds = Auxl.remove_duplicates
            (Auxl.option_map (function (_,bo)->bo) xys) in
        let rec f acc bounds = 
            match bounds with
            | [] -> acc
            | ((Bound_dotform bd) as b)::bounds' -> 
                (try  (
                  let i=List.assoc (bd.bd_lower,bd.bd_upper) acc in
                  if i=bd.bd_length then f acc bounds' 
                  else raise (Bounds ("bound "^Grammar_pp.pp_plain_bound b^" has inconsistent length constraints, \""^Grammar_pp.pp_plain_dots i ^"\" and \""^ Grammar_pp.pp_plain_dots bd.bd_length ^ "\"")))
                with
                  Not_found -> f (((bd.bd_lower,bd.bd_upper),bd.bd_length)::acc) bounds' )
            | b::bounds' -> f acc bounds' in
        ignore(f [] bounds);
        bounds
          


(* function xys -> *)
(*           let rec f acc xys =  *)
(*             match xys with *)
(*             | [] -> acc *)
(*             | (x,None)::xys' -> f acc xys' *)
(*             | (x,Some(b,i))::xys' ->  *)
(*                 try  ( *)
(*                   let i'=List.assoc b acc in *)
(*                   if i=i' then f acc xys'  *)
(*                   else raise (Bounds ("bound "^Grammar_pp.pp_plain_bound b^" has multiple distinct length constraints, \""^Grammar_pp.pp_plain_dots i ^"\" and \""^ Grammar_pp.pp_plain_dots i' ^ "\""))) *)
(*                 with *)
(*                   Not_found -> f ((b,i)::acc) xys' in *)
(*           f [] xys *)



(* check for each nt_or_mv (and subntr data) that it doesn't appear with *)
(* multiple different bounds, and return a list without duplicates *)
let check_bounds_consistency : 
    ((nt_or_mv*subntr_data) * bound option) list -> 
      ((nt_or_mv*subntr_data) * bound option) list 
        = function xbos ->
          let rec f acc xbos =
            (match xbos with
            | [] -> acc
            | (x,bo)::xbos' -> 
                match (try(Some(List.assoc x acc)) with Not_found -> None) with
                | None -> f ((x,bo)::acc) xbos'
                | Some bo' -> 
                    (if bo=bo' then f acc xbos'
                    else 
                      raise (Bounds ("inconsistent bounds for "^Grammar_pp.pp_plain_nt_or_mv (fst x)^": "^Grammar_pp.pp_plain_bound_option bo ^" and "^Grammar_pp.pp_plain_bound_option bo'  )))) in
          f [] xbos

(* split into those without a bound and those with one *)
let split_bounded : 
 ((nt_or_mv*subntr_data) * bound option) list ->  ((nt_or_mv*subntr_data) list) * ((nt_or_mv*subntr_data) * bound) list 
     = function xbos ->
       let rec f acc1 acc2 xbos = match xbos with
       | [] -> (acc1,acc2)
       | (x,None)::xbos' -> f (x::acc1) acc2 xbos'
       | (x,Some b)::xbos' -> f acc1 ((x,b)::acc2) xbos' in
       f [] [] xbos


(*invert, calculating, for each bound, the nt_or_mv that have that bound*)
let nt_or_mv_per_bound :
 ((nt_or_mv*subntr_data) * bound ) list ->  (bound * (nt_or_mv*subntr_data) list) list 
        = function xys ->
          let rec f acc xys =
            match xys with
            | [] -> acc
            | (x,y)::xys' -> 
                try 
                  let xs0 = List.assoc y acc in
                  let acc0 = List.remove_assoc y acc in 
                  f ((y,xs0@[x])::acc0) xys'
                with
                  Not_found ->
                    f ((y,[x])::acc) xys' in
          f [] xys

let pp_plain_foo m xd x = 
  String.concat "\n                   " 
    (List.map 
       (function (bound,ntmvsns) ->
         Grammar_pp.pp_plain_bound bound
         ^ ": "
         ^ String.concat "," 
             (List.map (function (ntmv,subntr_data)->Grammar_pp.pp_plain_nt_or_mv ntmv) ntmvsns)) 
       x)
  ^ "\n"

let pp_plain_bar m xd x = 
  String.concat "," 
    (List.map (function (ntmv,subntr_data)->Grammar_pp.pp_plain_nt_or_mv ntmv) x)
  ^ "\n"




(* for an nt_or_mv with no bound, try to merge it with each of those *)
(* that do have bounds - eg to find xj in x1..xn *)
let rec merge_nobound : ((nt_or_mv*subntr_data) * bound) list -> (nt_or_mv*subntr_data) -> (nt_or_mv*subntr_data) * (suffix*suffix_item * bound) option =
  function xbs -> function ((ntmvr,suff),subntr_data) -> 
    match xbs with
    | [] -> ((ntmvr,suff),subntr_data),None
    | (((ntmvr',suff'),subntr_data'),bound)::xbs' -> 
        if ntmvr=ntmvr' && subntr_data=subntr_data' then
          try
            let(pbo'',suff'')=Merge.merge_suffix_against_index 0 (suff,suff')in
            let foo_b'' = 
              (match pbo'' with 
              | Some (suffi,suffi') -> suffi     (* TODO: CHECK? *)
              | None -> failwith "cannot happen") in
            (((ntmvr,suff),subntr_data),Some(suff'',foo_b'',bound))
          with
            Merge.Merge _ -> merge_nobound xbs' ((ntmvr,suff),subntr_data)
        else 
          merge_nobound xbs' ((ntmvr,suff),subntr_data)


(*  de1 gives, for each bound (eg (1,m)) *)
(*    - the list of ntmv (with subntr data) for that bound,  *)
(*       eg [ l[0],None; p[0],None; s[0],None ] *)
(*    - a string for the compound isa/coq/hol identifier,  *)
(*       eg "l_p_s_list" *)
(*    - a string for the isa/coq pattern to deconstruct an element,  *)
(*       eg "(l_,p_,s_)" *)
(*    - a string for the coq type of the pattern *)
(*    - a string for the hol type of the compound identifier *)
(* todo: perhaps refactor.  The second two components are derived from the first, so *)
(* we could do that on-the-fly in grammar_pp *)

let dotenv1 m xd x : dotenv1 = 
  List.map 
    (function (bound,ntmvsns) ->
      let pp1 = 
	(List.map 
	   (function (ntmv,subntr_data) -> 
	     Grammar_pp.pp_nt_or_mv_with_sie m xd sie_project ntmv) ntmvsns) in
      let pp1_null = 
	(List.map 
	   (function (ntmv,subntr_data) -> 
	     Grammar_pp.pp_nt_or_mv_with_sie m xd sie_null ntmv) ntmvsns) in
(*       (\* horrible hack to get a Hol and Coq pp_mode - here our "clean" passing of mode-specific parameters as arguments to the mode constructor hurts us *\) *)

(*       let m_hol = Hol { pph_theory_name="dummy"; hol_library = None } in *)
(*       let m_coq = Coq { coq_expand_lists = false ;  (\* ARGH - DOES THIS MATTER HERE, WHERE ALL WE'RE DOING IS PRINTING A TYPE? *\) *)
(* 		        coq_quantified_vars_from_de = ref []; *)
(* 		        coq_non_local_hyp_defn = ref ""; *)
(* 		        coq_non_local_hyp_defn_vars = ref []; *)
(*                         coq_list_types = ref []; *)
(*                         coq_list_aux_funcs = Some (ref ""); *)
(*                         coq_list_aux_defns = { defined = ref []; newly_defined = ref [] }; *)
(*                         coq_library = Some (ref ("",[])); *)
(* 		        coq_locally_nameless = ref false } in *)
      let coq_type_pp1 = (match m with
      | Coq _ -> 
	  (List.map (function ((ntmv_root,_),subntr_data) -> 
	    (Grammar_pp.pp_nt_or_mv_root_ty m xd 
	       (Auxl.promote_ntmvr xd
		  (Auxl.primary_nt_or_mv_of_nt_or_mv xd ntmv_root)))
            (*^"ZZZ"*))
             ntmvsns)
      | _ -> ["dummy"]) in
      let hol_type_pp1 = (match m with
      | Hol _ | Lem _ -> 
	  (List.map (function ((ntmv_root,_),subntr_data) -> 
(* new *)
            Grammar_pp.pp_nt_or_mv_root_ty m xd 
              (Auxl.promote_ntmvr xd 
                 (Auxl.primary_nt_or_mv_of_nt_or_mv xd ntmv_root))
(* old *)
(*  	  Auxl.pp_hol_type_name  *)
(* 	    (Grammar_pp.pp_nt_or_mv_root m xd  *)
(* 	       (Auxl.promote_ntmvr xd *)
(* 		  (Auxl.primary_nt_or_mv_of_nt_or_mv xd ntmv_root))) *)
(* end *)
            (*^"ZZZ"*))
             ntmvsns)
      | _ -> ["dummy"]) in
      let pp_squished_vars =  String.concat "_" pp1_null ^"_list" in
      
      let pp_pattern =  
	let tmp = String.concat "," pp1 in
	if (List.length pp1) > 1 then "("^tmp^")" else tmp in
      let pp_coq_type = (* the coq type of the pattern *)
	let tmp = String.concat "*" coq_type_pp1 in
	if (List.length pp1) > 1 then "("^tmp^")" else tmp in
      let pp_hol_type_var = (* the hol type of the whole variable *)
	let tmp = String.concat "#" hol_type_pp1 in
	(if (List.length pp1) > 1 then "("^tmp^")" else tmp) 
        ^ " list" in
      ( bound, 
        { de1_ntmvsns = ntmvsns;
          de1_compound_id = pp_squished_vars;
          de1_pattern = pp_pattern;
          de1_coq_type_of_pattern = pp_coq_type;
          de1_hol_type_of_compound_id = pp_hol_type_var }) )
    x

(* de2 gives a list of ntmv (without subntr data) that are projections *)
(* from a list form. For example, if there is a list l'1..l'n, a use of *)
(* l'j will be indicated here as l'j, ('[0] , j , (1,n) ) *)

(* de3 gives a list of ntmv (with subntr data) that are not *)
(* projections from list forms. This is not part of a dot environment *)
(* (which just contains de1 and de2) *)

let dotenv23 ntmvsn_without_bounds ntmvsn_with_bounds  =
  let y = List.map (merge_nobound ntmvsn_with_bounds) ntmvsn_without_bounds in
  let de2 = Auxl.option_map (function ((ntmv,subntr_data),zo)->match zo with None->None|Some z -> Some(ntmv,z)) y in
  let de3 = Auxl.option_map (function ((ntmv,subntr_data),zo)->match zo with None->Some(ntmv,subntr_data)|Some z -> None) y in
  de2,de3



let bound_extraction m xd loc sts : dotenv * dotenv3 * string = 
  try  
    let x = nt_or_mv_of_symterms sts in
    let bounds = check_length_consistency x in
    let pp_bounds = String.concat "  " 
        (List.map Grammar_pp.pp_plain_bound bounds) in
    let ntmvsn_with_boundopts = check_bounds_consistency x in
    let ntmvsn_without_bounds,ntmvsn_with_bounds = split_bounded ntmvsn_with_boundopts in
    let bound_with_ntmvsnss = nt_or_mv_per_bound ntmvsn_with_bounds in
    let de1 = dotenv1 m xd bound_with_ntmvsnss in
    let de2,de3 = dotenv23 ntmvsn_without_bounds ntmvsn_with_bounds in
    let de = de1,de2 in
    let all_null = (bounds=[] && de1=[] && de2=[] && bound_with_ntmvsnss=[]) in
    let s = 
      (* Grammar_pp.pp_plain_dotenv3 de3 ^"\n" ^ *)
      if all_null then ""
      else (* pp_plain_bar m xd x'' ^ *) 
        "bounds: "^pp_bounds ^ "\n" 
        ^ "bound_with_ntmvss: "^pp_plain_foo m xd bound_with_ntmvsnss 
        ^ Grammar_pp.pp_plain_dotenv de in
    de, de3, s
  with 
    Bounds s' -> raise (Bounds (s'^" at "^Location.pp_loc loc))
(*  with e ->  *)
 (*   "exception in bound_extraction" *)

