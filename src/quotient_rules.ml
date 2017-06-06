(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2017                                                   *)
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

(* Support more ramified grammars for parser generation, which are
quotiented for all other purposes.

- each rule may have a {{ quotient-with ntr }} hom (at most one),
  where ntr is some other nonterminal root (which does not itself have
  such a hom)

- productions may have {{ quotient-remove }} homs

In the quotiented grammar, for each rule with a {{ quotient-with ntr }} hom:
- the productions of that rule are merged with those of ntr
- all nonterminals of that rule (throughout the grammar block) are
   added merged with those of ntr, with an added nonterminalroot tex hom to pretty print them as ntr 
- the homs and categories of that rule are discarded
- the production-name prefix of that rule is checked to be identical with that of ntr

Any productions with a {{ quotient-remove }} hom is discarded.

Implementation: This is done on raw_syntaxdefn's, in the first part of
Grammar_typecheck.check_and_disambiguate.  It should be before aux
rule synthesis, which makes it easier to do on a per-item basis, ie
*within* each "grammar" block (perhaps an unfortunate limitation).

*)

open Types


(* Old implementation: rename merged-in ntrs to have root ntr (this is
   debatable - its done in a crude way, so the user has to avoid
   clashes, and those will only be detected late) (also, renaming
   could be needed for later grammar blocks, but that is not done) *)

(* rename nonterminalroots in a raw production, as specified by the
quotient-with hom *)

(* this is happening on the raw representation of the grammar, before
we've properly lexed the nonterminals and metavars, so this is a bit
awkward.  For now we'll just check the string prefix, though in
general that's wrong; really we should do this part w.r.t the non-raw
grammar *)

(* a renaming is a list of (ntrs,ntr), where all the ntrs (the primary
or secondary ntrs of a rule that's being quotiented away) get splatted
to the ntr mentioned in the quotient-with hom *)
(*
let rec rename_raw_string renaming s = match renaming with
| [] -> s 
| (ntrs,ntr)::renaming' -> 
    match rename_raw_string' (ntrs,ntr)  s with
    | None -> rename_raw_string renaming' s 
    | Some s' -> s'

and rename_raw_string' (ntrs,ntr) s = match ntrs with
| [] -> None
| ntr'::ntrs'' -> 
    if String.length s >= String.length ntr' 
        && String.sub s 0 (String.length ntr') = ntr' 
    then
      Some (ntr ^ String.sub s (String.length ntr') (String.length s - String.length ntr'))
    else
      rename_raw_string' (ntrs'',ntr) s

let rec rename_raw_prod renaming p =
  { p with 
    raw_prod_es = List.map (rename_raw_element renaming) p.raw_prod_es;
    raw_prod_homs = List.map (rename_raw_homomorphism renaming) p.raw_prod_homs;
    raw_prod_bs = List.map (rename_raw_bindspec renaming) p.raw_prod_bs
  } 
    
and rename_raw_element renaming e = match e with
  | Raw_ident (l,i) -> Raw_ident(l, rename_raw_ident renaming i)
  | Raw_option (l,es) -> Raw_option(l, List.map (rename_raw_element renaming) es)
  | Raw_list (l,es) ->  Raw_list(l, List.map (rename_raw_element renaming) es)
  | Raw_nelist (l,es) ->  Raw_nelist(l, List.map (rename_raw_element renaming) es)
  | Raw_sugaroption (l,e) -> Raw_sugaroption(l, rename_raw_element renaming e)
  | Raw_dots(l,n) ->    Raw_dots(l,n) 
  | Raw_comp(l,es,cb,tmo) -> Raw_comp(l, List.map (rename_raw_element renaming) es, cb, tmo)

and rename_raw_homomorphism renaming (hn, hs, l) =
  (hn, List.map (rename_raw_hom_spec_el renaming) hs, l)
    
and rename_raw_hom_spec_el renaming el = match el with
  | Raw_hom_string s -> Raw_hom_string s
  | Raw_hom_blanks s -> Raw_hom_blanks s  
  | Raw_hom_ident is -> Raw_hom_ident (List.map (rename_raw_ident renaming) is)
  | Raw_hom_ident_dots (l, is, n, is') -> Raw_hom_ident_dots (l, List.map (rename_raw_ident renaming) is, n, List.map (rename_raw_ident renaming) is')
  | Raw_hom_ident_comp (l, is, cb) -> Raw_hom_ident_comp (l, List.map (rename_raw_ident renaming) is, cb)

and rename_raw_ident renaming (l, s) = (l, rename_raw_string renaming s)

and rename_raw_bindspec renaming bs = match bs with
| Raw_Bind(l,mse,i)-> Raw_Bind(l,rename_raw_mse renaming mse,rename_raw_ident renaming i)
| Raw_AuxFnDef(l,i,mse)-> Raw_AuxFnDef(l,rename_raw_ident renaming i, rename_raw_mse renaming mse)
| Raw_NamesEqual(l,mse,mse')-> Raw_NamesEqual(l,rename_raw_mse renaming mse,rename_raw_mse renaming mse')
| Raw_NamesDistinct(l,mse,mse')-> Raw_NamesDistinct(l,rename_raw_mse renaming mse,rename_raw_mse renaming mse')
| Raw_AllNamesDistinct(l,mse)-> Raw_AllNamesDistinct(l,rename_raw_mse renaming mse)

and rename_raw_mse renaming mse = match mse with
| Raw_MVorNTExp(l,i)-> Raw_MVorNTExp(l, rename_raw_ident renaming i)
| Raw_MVorNTListExp_dotform(l,i,n,i') -> Raw_MVorNTListExp_dotform(l, rename_raw_ident renaming i,n, rename_raw_ident renaming i') 
| Raw_MVorNTListExp_comp(l,i,cb) -> Raw_MVorNTListExp_comp(l, rename_raw_ident renaming i,cb) 
| Raw_Aux(l,i,i') -> Raw_Aux(l, rename_raw_ident renaming i, rename_raw_ident renaming i')
| Raw_AuxList_dotform(l,i,i',n,i'') -> Raw_AuxList_dotform(l, rename_raw_ident renaming i, rename_raw_ident renaming i',n, rename_raw_ident renaming i'')
| Raw_AuxList_comp(l,i,i', cb) -> Raw_AuxList_comp(l, rename_raw_ident renaming i, rename_raw_ident renaming i', cb) 
| Raw_Union(l,mse,mse') -> Raw_Union(l,rename_raw_mse renaming mse,rename_raw_mse renaming mse')  
| Raw_Empty(l) -> Raw_Empty(l) 
*)
      
  
    

let quotient_rules m_tex (rs: raw_rule list) :  raw_rule list = 

(* find the quotient-with homs and check they are to legal ntrs *)

  let rec singleton_string_of_raw_hom_spec1 hs = 
    match hs with
    | Raw_hom_blanks s :: hs' -> singleton_string_of_raw_hom_spec1 hs' 
    | Raw_hom_string s :: hs' -> singleton_string_of_raw_hom_spec2 s hs' 
    | _ -> None
  and singleton_string_of_raw_hom_spec2 s hs = 
    match hs with
    | Raw_hom_blanks s' :: hs' -> singleton_string_of_raw_hom_spec2 s hs' 
    | [] -> Some s
    | _ -> None in

  let quotient_data : (nontermroot(*primary*) * (nontermroot list)(*all*) * ((nontermroot(*what it should be quotiented with, not necessarily primary*) * loc) option)) list = 
    List.map 
      (function r ->
        let ntrls : (nontermroot * loc) list = 
          Auxl.option_map
            (function (hn,hs,l) -> 
              if hn = "quotient-with" then
                match singleton_string_of_raw_hom_spec1 hs with
                | Some ntr  -> Some (ntr, l)
                | None -> ty_error2 l ("quotient-with hom must have a single nonterminal root argument, not "^ Grammar_pp.pp_raw_homomorphism (hn,hs,l)) ""
              else 
                None)
            r.raw_rule_homs in
        (r.raw_rule_ntr_name, 
         List.map fst r.raw_rule_ntr_names, 
         (match ntrls with
         | [] -> None
         | [ntrl] -> Some ntrl
         | _ -> ty_error2 r.raw_rule_loc ("rule " ^ r.raw_rule_ntr_name ^ " has multiple quotient-with homs") "")))
      rs in

  let () = 
    List.iter 
      (function (ntr, ntrs, ntrlo) -> 
        match ntrlo with 
        | None -> () 
        | Some (ntr',l) -> 
            let (_,_,ntrlo'') = 
              try 
                List.find 
                  (function (ntr'', ntrs'', ntrlo'') -> List.mem ntr' ntrs'') quotient_data
              with
                Not_found -> ty_error2 l ("quotient-with hom of " ^ ntr ^ " to " ^ ntr' ^ ", but the latter is not a nonterminal root in the same grammar block") "" in
            (match ntrlo'' with
            | None -> ()
            | Some _ -> ty_error2 l ("quotient-with hom of " ^ ntr ^ " to " ^ ntr' ^ ", but the latter also has a quotient-with hom") "" ) )
      quotient_data in

(*
  let renaming = 
    Auxl.option_map 
      (function (ntr,ntrs,ntrlo) -> 
        match ntrlo with
        | None -> None
        | Some (ntr',l) -> Some (ntrs,ntr')
      )
      quotient_data in
*)
  
  (* construct one quotiented rule *)
  let quotient_rule (r:raw_rule) (rs: (raw_rule * nontermroot) list) : raw_rule = 
    
    (* check the production-name prefixes are identical *)
    let () = List.iter (function (r',_) -> if r'.raw_rule_pn_wrapper <> r.raw_rule_pn_wrapper then ty_error2 r'.raw_rule_loc ("quotiented rule production-name prefix "^r'.raw_rule_pn_wrapper^" does not match that of the target rule ("^r.raw_rule_pn_wrapper^")") "") rs in

    let strip_quotient_remove_prods ps = 
      List.filter
        (function p -> 
          not 
            (List.exists 
               (function (hn,hs,l) -> 
                 if hn = "quotient-remove" then
                   match hs with
                   | [ ]  -> true
                   | _ -> ty_error2 l "quotient-remove hom must not have any arguments" ""
                 else 
                   false)
               p.raw_prod_homs))
        ps in


    let add_tex_ntr_hom fake_loc ntr_target (ntr,homs) = 
      let tex_hom = ("tex", [Raw_hom_string (Grammar_pp.pp_tex_NT_NAME m_tex ^ "{" ^ ntr_target ^ "}")], fake_loc) in
      let homs' = tex_hom :: List.filter (function (hn,_,_)-> hn<>"tex") homs in
      (ntr,homs') in

    { r with 
      raw_rule_ntr_names = List.flatten (r.raw_rule_ntr_names :: List.map (function (r',ntr_target) -> List.map (add_tex_ntr_hom r'.raw_rule_loc ntr_target) r'.raw_rule_ntr_names) rs);
      raw_rule_ps = strip_quotient_remove_prods 
        (List.flatten
           (r.raw_rule_ps ::
           (List.map 
              (function (r',_) -> (*List.map (rename_raw_prod renaming)*) r'.raw_rule_ps)
              rs)));
    }  in

  let rec f qd rs_all rs = 
    match (qd, rs) with
    | (((ntr,ntrs,ntrlo)::qd'),  r::rs') ->
        (match ntrlo with
        | Some _ -> f qd' rs_all rs' 
        | None -> 
            (* find the primary ntrs of the rules that should be quotiented in, with the ntr target for each *)
            let rs_ntrs_to_be_quotiented_in = Auxl.option_map (function (ntr',ntrs',ntrlo') -> match ntrlo' with Some (ntr'',l) when List.mem ntr'' ntrs -> Some (ntr',ntr'') | _ -> None) quotient_data in
            (* the actual rules, with the ntr target for each *)
            let rs_to_be_quotiented_in = List.map (function (ntr,ntr_target) -> (List.find (function r' -> r'.raw_rule_ntr_name = ntr) rs_all, ntr_target)) rs_ntrs_to_be_quotiented_in in
            (quotient_rule r rs_to_be_quotiented_in) :: f qd' rs_all rs')
    | ([], []) -> []
    | _ -> raise (Failure "quotient rules")

  in
   f quotient_data rs rs 

