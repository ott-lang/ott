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

open Location
open Types

exception ThisCannotHappen
exception Unimplemented

(* library functions *)

let no_rbcatn = ref true

let pp_list_filter_coq =
  ( "Fixpoint list_filter A (f:A->bool) (l:list A) {struct l} : list A :=\n"
  ^ "  match l with\n"
  ^ "  | nil => nil\n"
  ^ "  | cons h t => if (f h) then cons h (list_filter A f t) else (list_filter A f t)\n"
  ^ "end.\n"
  ^ "Implicit Arguments list_filter.\n\n")

let pp_list_minus_caml = 
  ( "let rec list_minus (l1:'a list) (l2:'a list) : 'a list =\n"
  ^ "  match l1 with\n"
  ^ "  | [] -> []\n"
  ^ "  | h::t -> if (List.mem h l2) then list_minus t l2 else h::(list_minus t l2)\n"
  ^ "\n")
let pp_list_minus_lem = 
  ( "let rec list_minus (l1:list 'a) (l2:list 'a) : list 'a=\n"
  ^ "  match l1 with\n"
  ^ "  | [] -> []\n"
  ^ "  | h::t -> if (List.elem h l2) then list_minus t l2 else h::(list_minus t l2)\n"
  ^ "  end\n"
  ^ "\n")
let pp_list_minus_isa =
  ( "primrec\n"
  ^ "list_minus :: \"'a list => 'a list => 'a list\"\n"
  ^ "where\n"
  ^ "  \"list_minus Nil ys = Nil\"\n"
  ^ "| \"list_minus (Cons x xs) ys = (if Not(x : set ys) then Cons x (list_minus xs ys) else list_minus xs ys)\"\n\n")

let pp_list_minus_hol =
  ( "val _ = Define `\n"
  ^ "  (list_minus [] ys = [])  /\\\n"
  ^ "  (list_minus (x::xs) ys = (if ~(MEM x ys) then x::(list_minus xs ys) else list_minus xs ys))"
  ^"`;\n")

let pp_list_minus_coq = 
  ( "Fixpoint list_minus A (eq:forall a b:A,{a=b}+{a<>b}) (l1:list A) (l2:list A) {struct l1} : list A :=\n"
  ^ "  match l1 with\n"
  ^ "  | nil => nil\n"
  ^ "  | cons h t => if (list_mem (A:=A) eq h l2) then list_minus A eq t l2 else cons h (list_minus A eq t l2)\n"
  ^ "end.\n"
  ^ "Implicit Arguments list_minus.\n\n")

let pp_list_minus2_coq =
  ( "Fixpoint list_minus2 A B (eq:forall a b:A,{a=b}+{a<>b}) (l1:list (A*B)) (l2:list A) {struct l1} : list (A*B) :=\n"
  ^ "  match l1 with\n"
  ^ "  | nil => nil\n"
  ^ "  | cons a t => if (list_mem (A:=A) eq (@fst A B a) l2) then list_minus2 A B eq t l2 else cons a (list_minus2 A B eq t l2)\n"
  ^ "end.\n"
  ^ "Implicit Arguments list_minus2.\n\n")

let pp_list_mem_coq =
  ( "Fixpoint list_mem A (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list A) {struct l} : bool :=\n"
  ^ "  match l with\n"
  ^ "  | nil => false\n"
  ^ "  | cons h t => if eq h x then true else list_mem A eq x t\n"
  ^ "end.\n"
  ^ "Implicit Arguments list_mem.\n\n")

let pp_list_assoc_isa =
  ( "primrec\n"
  ^ "list_assoc :: \"'a => ('a*'b) list => 'b option\"\n"
  ^ "where\n"
  ^ "  \"list_assoc x0 Nil = None\"\n"
  ^ "| \"list_assoc x0 (Cons xy  xys) = (if x0=fst xy then Some (snd xy) else list_assoc x0 xys)\"\n\n")

let pp_list_assoc_hol =
  ( "val _ = Define `\n"
  ^ "  (list_assoc x [] = NONE)  /\\\n"
  ^ "  (list_assoc x ((x',y')::xys) = (if x=x' then SOME y' else list_assoc x xys))"
  ^"`;\n")

let pp_list_assoc_coq =
  ( "Fixpoint list_assoc A B (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list (A*B)) {struct l} : option B :=\n"
  ^ "  match l with\n"
  ^ "  | nil => None\n"
  ^ "  | cons (a,b) t => if (eq a x) then Some b else list_assoc A B eq x t\n"
  ^ "end.\n"
  ^ "Implicit Arguments list_assoc.\n\n")

(* this is a temporary workaround, to be replaced when the Lem library
List.assoc have been updated to return an option type *)
let pp_list_assoc_lem =
  ( lemTODO "ASSOC" "let rec list_assoc_option x0 xys =\n"
  ^ "  match xys with\n"
  ^ "  | [] -> Nothing\n"
  ^ "  | (x,y)::xys' -> if x0=x then Just y else list_assoc_option x0 xys'\n"
  ^ "  end\n\n")

let pp_list_mono_lemmas_isa =
  ( "lemma [mono]:\"\n"
  ^ "         (!! x. f x --> g x) ==> list_all (%b. b) (map f foo_list)-->\n"
  ^ "                    list_all (%b. b) (map g foo_list) \"\n"
  ^ "   apply(induct_tac foo_list, auto) done\n"
  ^ "\n"
  ^ "lemma [mono]: \"split f p = f (fst p) (snd p)\" by (simp add: split_def)\n")

let pp_list_all_cong_lemma_isa =
  ( "\n(* general lemma, should be in isa lib *)\n"
  ^ "lemma list_all_cong[fundef_cong]:\n"
  ^ "     \"xs = ys ==> (!!x. x:set ys ==> P x = Q x) ==> list_all P xs = list_all Q ys\"\n"
  ^ "  unfolding list_all_iff\n"
  ^ "  by auto\n\n")
 
let pp_list_mem m = match m with 
  | Coq co -> Auxl.add_to_lib co.coq_library "list_mem" pp_list_mem_coq
  | Caml _ | Hol _ | Lem _ | Isa _ | Tex _ | Twf _ | Ascii _ | Lex _ | Yacc _ 
    -> Auxl.errorm m "pp_list_mem"

let pp_list_filter m = match m with
  | Coq co -> Auxl.add_to_lib co.coq_library "list_filter" pp_list_filter_coq
  | Isa _ | Hol _ | Lem _ | Caml _ | Tex _ | Twf _ | Ascii _ | Lex _ | Yacc _ 
    -> Auxl.errorm m "pp_list_filter"

let pp_list_minus m = match m with 
  | Caml oo -> Auxl.add_to_lib oo.caml_library "list_minus" pp_list_minus_caml
  | Lem oo -> Auxl.add_to_lib oo.lem_library "list_minus" pp_list_minus_lem
  | Isa io  -> Auxl.add_to_lib io.isa_library "list_minus" pp_list_minus_isa
  | Hol ho  -> ()
  | Coq co  ->
      pp_list_mem m;
      Auxl.add_to_lib co.coq_library "list_minus" pp_list_minus_coq
  | Tex _ | Twf _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_list_minus"

let pp_list_minus2 m = match m with 
  | Coq co ->
      pp_list_mem m;
      Auxl.add_to_lib co.coq_library "list_minus2" pp_list_minus2_coq
  | Caml _ | Hol _ | Lem _ | Isa _ | Twf _ | Tex _ | Ascii _ | Lex _ | Yacc _ 
    -> Auxl.errorm m "pp_list_minus2"

let pp_list_assoc m = match m with 
  | Isa io -> Auxl.add_to_lib io.isa_library "list_assoc" pp_list_assoc_isa
  | Hol ho -> ()
  | Lem lo -> Auxl.add_to_lib lo.lem_library "list_assoc" pp_list_assoc_lem
  | Coq co -> Auxl.add_to_lib co.coq_library "list_assoc" pp_list_assoc_coq
  | Caml _ | Twf _ | Tex _ | Ascii _ | Lex _ | Yacc _ 
    -> Auxl.errorm m "pp_list_assoc"

let pp_list_mono_lemmas m = match m with 
  | Isa io when io.ppi_isa_primrec ->
      Auxl.add_to_lib io.isa_library "list_mono_lemmas" pp_list_mono_lemmas_isa
  | _ -> ()

let pp_list_all_cong_lemma m = match m with
  | Isa io when not io.ppi_isa_primrec ->
      Auxl.add_to_lib io.isa_library "list_all_cong_lemma" pp_list_all_cong_lemma_isa
  | _ -> ()

let pp_list_simp_lemmas m xd = () (* FZ REMOVE ?*)
(*   let pp_list_simp_lemma_rule (r:rule) : string = *)
(*     let id = Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name in *)
(*     let ids = id^"s" in *)
(*     let no_list = Auxl.uses_lists_rule r in *)
(*     if no_list > 0  *)
(*     then *)
(*       let rec tmp_no n =  *)
(* 	if n = 0 then [] *)
(* 	else n::(tmp_no (n-1)) in *)
(*       "lemma [simp]:\"\n"  *)
(*       ^ "("^id^"::"^id^") : set " ^ids^" ==>\n" *)
(*       ^ String.concat "& "  *)
(* 	  (List.map (fun n -> *)
(* 	    "size "^id^" < Suc ("^id^"_list_size"^string_of_int n^" "^ids^")\n") (List.rev (tmp_no no_list))) *)
(*       ^"\"\n" *)
(*       ^ "by (induct "^ids^", auto)\n\n" *)
(*     else "" *)
(*   in *)
(*   ( match m with  *)
(*   | Isa io when io.ppi_isa07_syntax -> *)
(*       ( match io.isa_library with *)
(*       | None -> Auxl.error "internal: None found for isa_library - list_simp_lemmas" *)
(*       | Some r -> *)
(* 	  let s,l = !r in *)
(*  	  if not (List.mem "list_simp_lemmas" l) then *)
(* 	    r :=  *)
(* 	      ( s  *)
(* 		^ String.concat ""  *)
(* 		  (List.map *)
(* 		     pp_list_simp_lemma_rule  *)
(* 		     xd.xd_rs) *)
(*                   , *)
(* 		("list_simp_lemmas"::l))) *)
(*   | _ -> ()) *)

(** ******************************** *)
(** ******************************** *)
(** auxfns                           *)
(** ******************************** *)
(** ******************************** *)

let rec auxfn_usages_in_mse mse =
  match mse with
  | MetaVarExp _ -> []
  | NonTermExp _ -> []
  | MetaVarListExp _ -> []
  | NonTermListExp _ -> []
  | Aux(f,nt) | AuxList(f,nt,_) -> [(f,nt)]
  | Union(mse,mse') -> auxfn_usages_in_mse mse @ auxfn_usages_in_mse mse'
  | Empty -> [] 

let auxfn_usages (bs : bindspec list) : (auxfn * nonterm) list =
  let all_binding_mses = 
    Auxl.option_map 
      (function b -> match b with
      | Bind(mse,nt) -> Some(mse)
      | _ -> None)
      bs in
  Auxl.remove_duplicates 
    (List.concat
       (List.map 
          auxfn_usages_in_mse 
          all_binding_mses))

let pp_auxfn_clauses m xd f ntr ntmvr =
  let dep = ref [] in
  
  let compute_mse_dep mse = 
    List.map 
      (function (f,(ntr,suff)) -> 
        let ntr'= Grammar_pp.pp_nontermroot m xd (Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd ntr)) in
        Auxl.auxfn_name f ntr' ntr') (* FZ *)
      (auxfn_usages_in_mse mse) in
  
  let ntrn = Grammar_pp.pp_nontermroot_ty m xd ntr in

  let id = Auxl.auxfn_name f ntrn ntrn in (* FZ *)

  let pp_auxfn_prod m xd isa_list_name_flag f ntr ntmvr p =
    (* the lhs is constructed by synthesising a *)
    (* canonical symterm from the production and then pping that *)
    let lhs_stnb = 
      Grammar_pp.canonical_symterm_node_body_of_prod ntr p in 
    let lhs_st = St_node(dummy_loc,lhs_stnb) in
    let ((de1,de2) as de,de3,pptbe) 
        = Bounds.bound_extraction m xd dummy_loc [lhs_st]  in
    let lhs = Grammar_pp.pp_symterm m xd [] de lhs_st in

    Grammar_pp.mse_split_inprod_counter := [];

    (* find the (unique) mse defining f for this production *)
    let mse =
      match 
        Auxl.option_map 
          ( fun b -> 
	    match b with 
	    | AuxFnDef(f',mse) when f'=f -> Some mse
	    | _ -> None ) 
          p.prod_bs with
      | [mse] -> mse
      | _ -> raise ThisCannotHappen (*Empty*) in

    dep := (compute_mse_dep mse) @ !dep;
    
    let (rhs, deps, aux_funcs) = 
      Grammar_pp.pp_mse m xd [] de isa_list_name_flag p.prod_name (Some ntmvr) mse in
    dep := deps @ !dep;
    (*List.iter (fun f -> print_endline ("== " ^ f.r_fun_id)) aux_funcs; (* FZ *)*)
    (("",lhs,rhs), aux_funcs)  (* FZ add prefix here *)

  in
  
  let header =
    ( match m with
    | Isa _ -> 
	( Auxl.auxfn_name f ntrn ntrn (* FZ *)
	  ^ " :: \""
	  ^ Grammar_pp.pp_nontermroot_ty m xd ntr ^" => "
	  ^ Grammar_pp.pp_nt_or_mv_root_ty m xd ntmvr  ^" list\"\n", "", "")
    | Hol _ -> "", "", ""
    | Coq _ -> 
        let nts_used = Context_pp.nts_used_in_lhss m xd (Auxl.rule_of_ntr xd ntr) in
        let fresh_var_ntr = Auxl.secondary_ntr xd ntr  in
	let pat_var  = Auxl.fresh_nt nts_used (fresh_var_ntr,[]) in
	( Auxl.auxfn_name f ntrn ntrn (* FZ *)
	  ^ " (" ^ Grammar_pp.pp_nonterm m xd pat_var 
	  ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd ntr ^ ")", 
          "", 
          " : list " ^ Grammar_pp.pp_nt_or_mv_root_ty m xd ntmvr ^ " :=\n" 
	  ^ "  match " ^ Grammar_pp.pp_nonterm m xd pat_var ^ " with\n" ) 
    | Lem _ 
    | Caml _ -> 
        let nts_used = Context_pp.nts_used_in_lhss m xd (Auxl.rule_of_ntr xd ntr) in
        let fresh_var_ntr = Auxl.secondary_ntr xd ntr  in
	let pat_var  = Auxl.fresh_nt nts_used (fresh_var_ntr,[]) in
	( Auxl.auxfn_name f ntrn ntrn (* FZ *)
	  ^ lemTODOm m "17" " (" ^ Grammar_pp.pp_nonterm m xd pat_var 
	  ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd ntr ^ ")", 
          "", 
          " : " ^ 
          (match m with 
          | Caml _ -> Grammar_pp.pp_nt_or_mv_root_ty m xd ntmvr ^ " list" 
          | Lem _ -> "list " ^Grammar_pp.pp_nt_or_mv_root_ty m xd ntmvr
          )
          ^" =\n" 
	  ^ "  match " ^ Grammar_pp.pp_nonterm m xd pat_var ^ " with\n" ) 
    | Twf _ | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_auxfn_clauses" ) 
  in

  let isa_list_name_flag = Auxl.compute_isa_list_name_flag (Auxl.rule_of_ntr xd ntr) in

  let clauses, aux_funcs = 
    List.split
      (List.map 
         (pp_auxfn_prod m xd isa_list_name_flag f ntr ntmvr) 
         (List.filter 
            (function p-> not p.prod_meta) 
            (Auxl.rule_of_ntr xd ntr).rule_ps))
  in

  { r_fun_id = id;
    r_fun_dep = !dep;
    r_fun_type = ntr;
    r_fun_header = header;
    r_fun_clauses = clauses } :: (List.concat aux_funcs)
    
let pp_auxfns m xd axs =
  let pp_auxfn = 
    function (f,(ntrs,ntmvr)) ->
      List.concat (List.map 
	(fun ntr -> pp_auxfn_clauses m xd f ntr ntmvr) 
	ntrs)
  in 
  Dependency.collapse m xd 
    { i_funcs = (List.concat (List.map pp_auxfn axs (* xd.xd_axs *) ));
      i_funcs_proof = None }


(** ***************************************************** *)
(** ***************************************************** *)
(** generic code for pp function definitions, with deps   *)
(** ***************************************************** *)
(** ***************************************************** *)

let pp_foo_with_dependencies m xd 
    (foo_manifestly_needed: syntaxdefn -> nontermroot -> prod -> bool) 
    (pp_foo_rule: pp_mode -> syntaxdefn -> nontermroot list -> rule -> int_func list)
    : int_funcs = 

  (* 1- build rs *)
     
  (* calculate whether we manifestly have to define a foo function, *)
  (* for a production, and rule, by checking whether there exists a *)
  (* production with a rhs which satisfies foo_manifestly_needed  *)

  let foo_manifestly_needed_prod ntr p = 
    (not p.prod_meta) && foo_manifestly_needed xd ntr p in
  
  let foo_manifestly_needed_rule r = 
    (not r.rule_meta)  && 
    List.exists (foo_manifestly_needed_prod r.rule_ntr_name) r.rule_ps in
  
  let free_rs = 
    List.filter (fun r -> 
      (not r.rule_meta)
	&& (Auxl.hom_spec_for_pp_mode m r.rule_homs = None)
	        ) xd.xd_rs in
  
  let foo_manifestly_needed_rules = 
    List.filter foo_manifestly_needed_rule free_rs in
  
  let domain_rs = 
    List.filter 
      (fun r ->
        ( List.mem r foo_manifestly_needed_rules
        || List.exists 
            (function r' -> 
                (* r depends on r' *)
              List.mem 
                (Ntr r'.rule_ntr_name) 
                (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep))
            )
            foo_manifestly_needed_rules))
      free_rs in
  
  (* 2- build domain *)
  let domain = 
    List.map 
      ( fun r -> r.rule_ntr_name )
(*	  if foo_manifestly_needed_rule subst r *)
(*	  then Some r.rule_ntr_name else None ) *)
      domain_rs in

  (* 3- computing foo code *)
  { i_funcs = List.concat (List.map (pp_foo_rule m xd domain) domain_rs);
    i_funcs_proof = None }
  

(** ******************************** *)
(** ******************************** *)
(** Substitution                     *)
(** ******************************** *)
(** ******************************** *)

let subst_split_inprod_counter = ref []

(** ******************************** *)
(** subst over a symterm             *)
(** ******************************** *)

(* generate the result of applying a subst to a symterm  *)
(* - but only for the forms of symterm that can be created as the *)
(* canonical symterm of a prod *)


(* calculate the bound things for an occurrence of nonterm nt, *)
(* ie the bound things that we should remove from the domain of *)
(* any substitution pushed down into nt *)
let glommed_bound_things_for_nonterm 
    (xd :syntaxdefn) (p :prod) (that_var_root : nt_or_mv_root) (nt : nonterm) : mse =

  (* first, the mse' from any [[bind mse' in nt]] -- things that bind in nt *)
  (* eg [[x]] from [[bind x in nt]], for which we should remove [[x]] *)
  let relevant_bind_clauses_around_this_nonterm : (mse * nonterm) list = 
    Auxl.option_map 
      (function b -> match b with
      | Bind(mse',nt') -> 
          if nt'=nt &&
            Auxl.result_type_of_mse xd mse'= that_var_root then Some (mse',nt)
          else None
      | _ -> None) 
      p.prod_bs in
  
  (* second, the relevant f(nt) and f(nt1..ntn) which occur in the mse''  *)
  (* of any [[bind mse'' in nt'' ]] *)
  (* eg (f,nt) from [[bind f(nt) in nt'']], for which we should remove f(nt) *)
  (* &  (f,nt_) from [[bind f(nt1..ntn) in nt'']], for which we should remove f(nt_) *)
  let relevant_auxfn_usages_of_this_nonterm : (auxfn * nonterm) list = 
    if !no_rbcatn then [] else
    List.filter 
      (function (f,nt'') -> 
        nt'' = nt 
          &&  that_var_root = (snd(List.assoc f xd.xd_axs)))
      (auxfn_usages p.prod_bs) in
  
  (* third, any [[nt]] and nt1..ntn which occur in the mse'' of *)
  (* any [[bind mse'' in nt'' ]] *)
  (* --- indications that nt binds in something else *)
  (* eg true if there is a clause [[bind nt in nt'']] *)
  (*                           or [[bind nt1..ntn in nt'']] where nt=nt_ *)
  let directly_binding_usages_of_this_nonterm : bool = 
    let rec nt_occurs mse = match mse with
    | MetaVarExp mv' ->  false
    | NonTermExp nt' -> nt=nt'
    | MetaVarListExp (mv',_) ->  false
    | NonTermListExp (nt',_) -> nt=nt'
    | Aux (f',nt') -> false
    | AuxList (f',nt',_) -> false
    | Union (mse',mse'') -> nt_occurs mse' || nt_occurs mse''
    | Empty -> false in
    List.exists
      (function bs -> match bs with
      | Bind (mse'',nt'') -> nt_occurs mse''
      | _ -> false)
      (p.prod_bs) in 

  (* all three *)
  let bound_things : mse list = 
    List.map 
      fst
      relevant_bind_clauses_around_this_nonterm
    @ List.map 
        (function (f,_) -> Aux(f,nt)) 
        relevant_auxfn_usages_of_this_nonterm 
    @ 
      if directly_binding_usages_of_this_nonterm then
        [NonTermExp nt]
      else
        [] in

  (* glommed together into a single mse *)
  let bound_things_glommed : mse = 
    let rec f mses = match mses with
    | [] -> Empty
    | [mse] -> mse
    | mse::mses' -> Union(mse,f mses') in
    f bound_things in

  bound_things_glommed

let directly_binding_usages_of_this_metavar  
    (xd :syntaxdefn) (p :prod) (mv : metavar) : bool =
  let rec mv_occurs mse = match mse with
  | MetaVarExp mv' ->  mv=mv'
  | NonTermExp nt' -> false
  | MetaVarListExp (mv',_) ->  mv=mv'
  | NonTermListExp (nt',_) -> false
  | Aux (f',nt') -> false
  | AuxList (f',nt',_) -> false
  | Union (mse',mse'') -> mv_occurs mse' || mv_occurs mse''
  | Empty -> false in
  List.exists
    (function bs -> match bs with
    | Bind (mse'',nt'') -> mv_occurs mse''
    | _ -> false)
    (p.prod_bs) 

(* todo: is there a better idiom than this insane list of arguments? *)
let rec pp_subst_symterm
    (m : pp_mode) (xd : syntaxdefn) 
    (subst : subst) (domain : nontermroot list) (rule_ntr_name : nontermroot)
    (this_var : nonterm) (that_var : nt_or_mv) (that_var_fresh_suffix : suffix)
    (sub_var : string) (in_var : nonterm)
    (p : prod) 
    (dependencies) 
    (sie : suffix_index_env) (de : dotenv)
    (st : symterm) : string =
  match st with
  | St_node (l,stnb) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
  | St_nonterm (l,ntrp,nt)  -> 
      let nt_s = Grammar_pp.pp_nonterm_with_de_with_sie m xd sie de nt in
      (* if there isn't a dependency, don't generate the recursive call *)
      if not(List.mem ntrp domain) then 
        (* - just repeat the nonterm instead *)
        nt_s
      else
        
        (* work out what's binding in this nt *)

        let bound_things_glommed : mse = 
          glommed_bound_things_for_nonterm xd p subst.sb_that (*(root_of that_var)*) nt in
        
        let this_s = Grammar_pp.pp_nonterm m xd this_var in
        let that_s = Grammar_pp.pp_nt_or_mv m xd that_var in

        (* ??? todo: make this and that fresh wrt to the binders we're *)
        (* checking equality against *)

        let that_in_bound_things () : string = (* turned into a thunk so that library functions are printed only if needed *)
          (* could optimise this to be more pretty for simple mses, *)
          (* eg where there's just a single equality check, *)
          (* though that might make proofs less uniform *)
          match m with
          | Isa _ ->
              that_s 
              ^" : set "
              ^ Grammar_pp.pp_mse_string m xd sie de bound_things_glommed
          | Hol _ ->
              "MEM "
              ^ that_s 
              ^" "
              ^ Grammar_pp.pp_mse_string m xd sie de bound_things_glommed
          | Caml _ ->
              "List.mem "
              ^ that_s 
              ^ " "
              ^ "(" ^ Grammar_pp.pp_mse_string m xd sie de bound_things_glommed ^ ")"
          | Lem _ ->
              lemTODO "18" " List.elem "
              ^ that_s 
              ^ " "
              ^ "(" ^ Grammar_pp.pp_mse_string m xd sie de bound_things_glommed ^ ")"
          | Coq _ -> 
	      pp_list_mem m; 
	      "list_mem "
(* 	      ^ Grammar_pp.pp_nt_or_mv_root m xd (root_of that_var) ^ " " *)
	      ^ "eq_" ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that (*(root_of that_var) *)
              ^ " "
	      ^ that_s ^ " "
	      ^ ( match Grammar_pp.pp_mse m xd sie de false "" (Some subst.sb_that) bound_things_glommed with x,_,_ -> x)
	  | Twf _ -> "<<< mem FZ no idea >>>"
          | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_subst_symterm"
	in

        if subst.sb_multiple then (* code for multiple subst *)
      	  ( 
	    let dep_name = Grammar_pp.pp_nontermroot m xd (Auxl.promote_ntr xd ntrp) in (* FZ PROMOTE?*)
	    dependencies := (Auxl.subst_name subst.sb_name dep_name)::!dependencies;
            match m with
            | Isa _ -> 
		"("
		^ Auxl.subst_name subst.sb_name dep_name ^ " "
		^ (match bound_things_glommed with
		| Empty -> sub_var 
		| _ -> 
                    "(List.filter "
                    ^ "(%("^ that_s ^","^ this_s ^")." 
                    ^ "Not("^that_in_bound_things()^")"
                    ^ ")"
                    ^ " "^sub_var^")")
		^ " "
		^ nt_s
		^ ")" 
            | Hol _ -> 
		"("
		^ Auxl.subst_name subst.sb_name dep_name ^ " "
		^ (match bound_things_glommed with
		| Empty -> sub_var 
		| _ -> 
                    "(FILTER "
                    ^ "(\\("^ that_s ^","^ this_s ^"). " 
                    ^ "~("^that_in_bound_things()^"))"
                    ^ " "^sub_var^")")
		^ " "
		^ nt_s
		^ ")" 
            | Caml _ -> 
		"("
		^ Auxl.subst_name subst.sb_name dep_name ^ " "
		^ (match bound_things_glommed with
		| Empty -> sub_var 
		| _ -> 
                    "(List.filter "
                    ^ "(fun ("^ that_s ^","^ this_s ^") -> " 
                    ^ "not("^that_in_bound_things()^")"
                    ^ ")"
                    ^ " "^sub_var^")")
		^ " "
		^ nt_s
		^ ")" 
            | Lem _ -> 
                lemTODO "19" ( 
		"("
		^ Auxl.subst_name subst.sb_name dep_name ^ " "
		^ (match bound_things_glommed with
		| Empty -> sub_var 
		| _ -> 
                    "(List.filter "
                    ^ "(fun ("^ that_s ^","^ this_s ^") -> " 
                    ^ "not("^that_in_bound_things()^")"
                    ^ ")"
                    ^ " "^sub_var^")")
		^ " "
		^ nt_s
		^ ")" 
               )
            | Coq co -> 
		"("
		^ Auxl.subst_name subst.sb_name dep_name ^ " "
		^ (match bound_things_glommed with
		| Empty -> sub_var 
		| _ -> 
                    if co.coq_use_filter_fn then begin
		      pp_list_filter m;
		      "(list_filter "
		      ^ "(fun (tmp:"
		      ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that
		      ^ "*" ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this  ^") => "
                      ^ "match tmp with ("^ that_s ^","^ this_s
                      ^ ") => negb (" ^ (that_in_bound_things()) ^ ") end)"
                      ^ " "^sub_var^")"
                    end else begin
	              pp_list_minus2 m; 
     	              "(list_minus2 "
	              ^ "eq_" ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that 
                      ^ " " ^sub_var^ " "
	              ^ ( match Grammar_pp.pp_mse m xd sie de false "" (Some subst.sb_that) 
                                bound_things_glommed with x,_,_ -> x)
                      ^ ")"
                    end)
		^ " "
		^ nt_s
		^ ")"
	    | Twf _ -> "<<< filter FZ no idea >>>"
            | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_subst_symterm" )
        else (* code for single subst *)
          let substituted_nonterm = 
	    let id = Grammar_pp.pp_nontermroot m xd (Auxl.promote_ntr xd ntrp) in (* FZ PROMOTE ?*)
      	    dependencies := (Auxl.subst_name subst.sb_name id)::!dependencies;
            "("
            ^ Auxl.subst_name subst.sb_name id ^" "
            ^ Grammar_pp.pp_nonterm m xd this_var ^" "
            ^ Grammar_pp.pp_nt_or_mv m xd that_var ^" "
            ^ nt_s
            ^ ")" in

          ( match bound_things_glommed with 
          | Empty -> substituted_nonterm
          | _ -> 
              "(" 
              ^ "if "^that_in_bound_things()
              ^ " then "
              ^ nt_s
              ^ " else "
              ^ substituted_nonterm
              ^ ")" )

  | St_nontermsub (l,ntrpl,ntrpt,nt)  -> 
      raise ThisCannotHappen  (* never occurs in a canonical symterm_element *)
  | St_uninterpreted (p,s) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
        
and pp_subst_symterm_element 
    (m : pp_mode) (xd : syntaxdefn) 
    (subst : subst) (domain : nontermroot list) (isa_list_name_flag : bool) (rule_ntr_name : nontermroot)
    (this_var : nonterm) (that_var : nt_or_mv) (that_var_fresh_suffix : suffix)
    (sub_var : string) (in_var : nonterm)
    (p : prod) 
    (dependencies) 
    (sie : suffix_index_env) (de : dotenv)
    (ste : symterm_element) : string * int_func list =
  match ste with
  | Ste_st(_,st) -> 
      ( pp_subst_symterm 
	  m xd subst domain rule_ntr_name 
	  this_var that_var that_var_fresh_suffix 
	  sub_var in_var p dependencies sie de st, [] )
  | Ste_metavar (l,mvrp,mv) -> 
      (* if not (boundedness_of_metavar xd p that_var mv) then *)
        ( Grammar_pp.pp_metavar_with_de_with_sie m xd sie de mv, [] )
      (* else *)
      (*  "<<wibble>>" *)

  (* TODO: it's unclear whether the Ste_metavar case above is right in *)
  (* general, or whether we need to take account of boundedness *)

  | Ste_var (l,mvrp,var) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
  | Ste_list (l,stlis) -> 
      ( match stlis with 
      | [Stli_listform stlb] -> 
	  pp_subst_symterm_list_body 
	    m xd subst domain isa_list_name_flag rule_ntr_name 
	    this_var that_var that_var_fresh_suffix 
	    sub_var in_var p dependencies sie de stlb
      | _-> 
	  raise ThisCannotHappen(*never occurs in a canonical symterm_element*) )

and freshen idl buffer = (* FZ rewrite *)
  match idl with 
  | [] -> []
  | h::t -> 
      try
	let last_n = List.assoc h buffer in
	last_n := !last_n + 1;
	let hn = (h^(string_of_int !last_n)) in
	hn :: (freshen t buffer) 
      with Not_found -> (
	let last_n = ref 1 in
	let hn = (h^(string_of_int !last_n)) in
	hn :: (freshen t ((h,last_n)::buffer))) 

and pp_subst_symterm_list_body 
    (m : pp_mode) (xd : syntaxdefn) 
    (subst : subst) (domain : nontermroot list) (isa_list_name_flag : bool) (rule_ntr_name : nontermroot)
    (this_var : nonterm) (that_var : nt_or_mv) (that_var_fresh_suffix : suffix)
    (sub_var : string) (in_var : nonterm)
    (p : prod) 
    (dependencies) 
    (sie : suffix_index_env) (de : dotenv)
    (stlb : symterm_list_body) : string * int_func list =

  (* code similar to pp_symterm_list_body in grammar_pp.ml - refactor? *)
  let (de1,de2)=de in
  (* print_string ("[[["^pp_plain_dotenv de^"]]]");flush stdout; *)
  let de1i = Grammar_pp.de1_lookup de1 stlb.stl_bound in

  let pp_body_tmp, list_funcs = 
    List.split
      (List.map 
	 (pp_subst_symterm_element 
	    m xd subst domain isa_list_name_flag rule_ntr_name 
	    this_var that_var that_var_fresh_suffix 
	    sub_var in_var p dependencies ((Si_var ("_",0))::sie) de) 
	 stlb.stl_elements) in
  
  let pp_body = 
    let tmp = String.concat "," pp_body_tmp in
    if (List.length stlb.stl_elements) > 1 then "("^tmp^")" else tmp in

  let rec make_aux_funcs_list m xd stlb subst common_lhs : string * int_func list =

    let name = Grammar_pp.make_name_elements m xd false stlb.stl_elements in

    let id = (Auxl.subst_name subst.sb_name name) ^ "_list" in
    let dep_id = Auxl.subst_name subst.sb_name name in

    match m with
    | Isa _ | Hol _ | Lem _ ->
        let typ = (Grammar_pp.make_name_elements m xd true stlb.stl_elements) ^ " list" in
	let split_suffix = 
	  ( match m with
	  | Isa io when io.ppi_isa_primrec ->
	      let pre_split_suffix = 
		if isa_list_name_flag then "_"^p.prod_name else "" in
	      let counter_suffix = 
		try 
		  let c_p = List.assoc (typ^pre_split_suffix) !subst_split_inprod_counter in
		  c_p := !c_p + 1;
		  string_of_int (!c_p)
		with Not_found -> (
		  subst_split_inprod_counter := ((typ^pre_split_suffix),ref 0)::!subst_split_inprod_counter;
		  "" ) in
	      pre_split_suffix ^ counter_suffix 
	  | _ -> "" ) 
	in
	
        let header =
          if not subst.sb_multiple
          then
	    id ^ split_suffix ^ " :: \""
	    ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^ " => "
	    ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^" => "
	    ^ typ ^ " => " ^ typ ^ "\"\n"
          else
	    id ^ split_suffix ^ " :: \""
	    ^  "(" ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^"*"
	    ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^") list => "
	    ^ typ ^ " => " ^ typ ^ "\"\n"
        in
        let lp = Auxl.hide_isa_trailing_underscore m (name^"_") in
        let rp = Auxl.hide_isa_trailing_underscore m (name^"_list_") in

        (* discover if dep_id contains a tuple, and generate appropriate funcs *)
        let dep_id, dep_funcs =
	  let dep_id_typ = Grammar_pp.make_name_elements m xd true stlb.stl_elements in
          if String.contains dep_id_typ '*'  
          then (dep_id^split_suffix,
		make_aux_funcs_tuple m xd split_suffix stlb.stl_elements subst common_lhs)
	  else (dep_id, []) in
	
        let func =
          [ { r_fun_id = id^split_suffix;
	      r_fun_dep = [dep_id; id^split_suffix ];
	      r_fun_type = typ^split_suffix;
	      r_fun_header = (header,"","");
	      r_fun_clauses = 
	      [ ("", common_lhs ^ " Nil", "Nil");
	        ("", common_lhs ^ " ("^lp^"#"^rp^")",
	         "(" ^ dep_id ^ " " ^ common_lhs ^ " "^lp^") # (" ^ id^split_suffix ^ " " ^ common_lhs ^ " "^rp^")" ) ] } ]
        in     
        (id^split_suffix, func@dep_funcs)

    | Coq co -> if not co.coq_expand_lists then ("",[]) else
        let suf =           
          "list_"
          ^ ( (Grammar_pp.make_name_elements m xd false stlb.stl_elements)) in
        let typ = (*Auxl.pp_coq_type_name*) suf in

	let header =
          ( id
            ^ ( if subst.sb_multiple 
	    then 
	      " (" ^ sub_var ^ ":list (" 
	      ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that 
	      ^ "*" ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^ "))" 
	    else 
	      " (" ^ Grammar_pp.pp_nonterm m xd this_var ^ ":"
              ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^")"
	      ^ " (" ^ Grammar_pp.pp_nt_or_mv m xd that_var ^ ":"
              ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^ ")" )
	    ^ " (" ^ Grammar_pp.pp_nonterm m xd in_var ^ ":"
            ^ typ ^ ")",
            " {struct " ^ Grammar_pp.pp_nonterm m xd in_var ^"}", 
            " : " ^ typ ^ " :=\n" 
	    ^ "  match " ^ Grammar_pp.pp_nonterm m xd in_var ^ " with\n" ) in

	let args = (* FZ find a less hacky way *)
	  Str.split (Str.regexp "(\\|*\\|)") (Grammar_pp.make_name_elements m xd true stlb.stl_elements) in
	let new_id =  (* FZ freshen properly *)
	  let c  = ref 0 in
	  fun x -> c:=!c+1; x^(string_of_int !c) in

	let fresh_args =  
	  if List.length args > 1 
	  then List.map (fun x -> new_id x) args 
	  else args in

        let lp = String.concat " " fresh_args in
        let rp = name^"_tl" in

	let rhs_deps = ref [] in
	
	let rhs =   (* FZ -- very experimental *)
	  String.concat " " 
	    (List.map2 
	       (fun n x ->   
		 if (List.mem n domain) 
		 then
		   let sn = Auxl.subst_name subst.sb_name n in
		   rhs_deps := sn :: !rhs_deps;
		   "(" ^ sn ^ " " ^ common_lhs ^ " " ^ x ^")" 
		 else x) 

	       args fresh_args ) in
	
	(id, 
         [ { r_fun_id = id;
	     r_fun_dep = id::!rhs_deps;
	     r_fun_type = typ;
	     r_fun_header = header;
	     r_fun_clauses = 
	     [ ("", "Nil_"^suf, "Nil_"^suf);
	       ("", "Cons_"^suf^" "^lp^" "^rp,
		"Cons_"^suf^" " ^ rhs ^ " (" ^ id ^ " " ^ common_lhs ^ " "^rp^")" ) ] } ])


    | Caml _ -> ("",[])

    | Twf _ | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "make_aux_func_list"


  and make_aux_funcs_tuple m xd split_suffix elements subst common_lhs : int_func list =
    let (el_hd,el_tl) = (List.hd elements, List.tl elements) in

    let name = Grammar_pp.make_name_elements m xd false elements in
    let name_tl = 
      (Grammar_pp.make_name_elements m xd false el_tl)
      ^ ( if List.length el_tl = 1 then ""
	  else split_suffix )
    in
    let id = Auxl.subst_name subst.sb_name name in

    let dep_el = 
      if List.length el_tl = 1
      then Grammar_pp.make_dep_elements elements 
      else (Grammar_pp.make_dep_elements [ el_hd ]) @ [ name_tl ] in 

    let dep_id = 
      (* id_tl is not in domain, so we add it explicitely *)
      List.map 
	(fun x -> (Auxl.subst_name subst.sb_name x))
	(name_tl :: ((List.filter (fun x -> List.mem x domain) dep_el)))  in

    let typ = 
      if List.length el_tl = 1 
      then Grammar_pp.make_name_elements m xd true elements 
      else 
        let h = Grammar_pp.make_name_elements m xd true [ el_hd ] in  
        let t = Grammar_pp.make_name_elements m xd true el_tl in
        h^"*"^t in

    let header =
      if not subst.sb_multiple
      then
	id^split_suffix ^ " :: \""
	^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^ " => "
	^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^" => "
	^ typ ^ " => " ^ typ ^ "\"\n"
      else
	id^split_suffix ^" :: \""
	^  "(" ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^"*"
	^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^") list => "
	^ typ ^ " => " ^ typ ^ "\"\n" in
    
    let lhs = " (" ^ String.concat "," (freshen dep_el []) ^ ")" in
    
    let els_hd,els_tl =
      match List.combine dep_el (freshen dep_el []) with
      | h::t::[] -> h,t
      | _ -> Auxl.int_error "never happen in make_aux_funcs_tuple" in

    let make_call (el,elf) = 
      if List.mem el domain 
      then (Auxl.subst_name subst.sb_name el) ^ " " ^ common_lhs ^ " " ^ elf
      else elf in
    
    let rhs, aux_funcs = 
      let comp_1 = make_call els_hd in
      let comp_2, aux_2 = 
        if List.length el_tl = 1 
        then (make_call els_tl),[]
        else 
          (Auxl.subst_name subst.sb_name name_tl) (* ^ split_suffix *) ^ " "^common_lhs 
          ^" "^(snd els_tl) , (make_aux_funcs_tuple m xd split_suffix el_tl subst common_lhs) 
          
      in (comp_1 ^" , "^comp_2, aux_2) in
  
    let func1 =
      { r_fun_id = id^split_suffix;
	r_fun_dep = dep_id;
	r_fun_type = typ^split_suffix;
	r_fun_header = (header,"","");
	r_fun_clauses = [ ("", common_lhs ^ lhs, rhs) ] } :: aux_funcs
    in func1
  in
        
  (* hacky optimisation to remove identity maps *)
  if de1i.de1_pattern=pp_body then ( de1i.de1_compound_id, [] )  
  else
    let id,parent_id, common_lhs =
      if not subst.sb_multiple
      then
	( Auxl.subst_name subst.sb_name (Grammar_pp.make_name_elements m xd false stlb.stl_elements) ^ "_list",
	  Auxl.subst_name subst.sb_name rule_ntr_name,
	  Grammar_pp.pp_nonterm m xd this_var ^ " " ^ Grammar_pp.pp_nt_or_mv m xd that_var  ) 
      else
	( Auxl.subst_name subst.sb_name (Grammar_pp.make_name_elements m xd false stlb.stl_elements) ^ "_list",
	  Auxl.subst_name subst.sb_name rule_ntr_name,
          sub_var )
    in

    let id,funcs = make_aux_funcs_list m xd stlb subst common_lhs in

    let body =  "(" ^ id ^ " " ^ common_lhs ^ " " ^ de1i.de1_compound_id ^ ")" in

    match m with
    | Isa _ ->   
(*           "(List.map (%"^pp_pattern^"."^pp_body^") "  *)
(*           ^ pp_squished_vars *)
(*           ^ ")", [] *)
	(body, funcs)
    | Hol _ -> 
        ( "(MAP (\\"^de1i.de1_pattern^". "^pp_body^") "
        ^ de1i.de1_compound_id
        ^ ")", [] )
    | Coq co ->
        if co.coq_expand_lists 
        then (body, funcs)
        else
          let l = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in
          if List.length l = 1 then	
            ( "(map (fun ("^de1i.de1_pattern^":" ^ de1i.de1_coq_type_of_pattern ^ ") => "^pp_body^") "
              ^ de1i.de1_compound_id
              ^ ")", [] )
          else
            ( "(map (fun (pat_:" ^ de1i.de1_coq_type_of_pattern ^ ") => match pat_ with " (* FZ freshen pat_ *)
              ^ de1i.de1_pattern^" => " ^pp_body^" end) "  
              ^ de1i.de1_compound_id
              ^ ")", [] )

    | Caml _ ->
        ( "(List.map (fun "^de1i.de1_pattern^" -> "^pp_body^") "
        ^ de1i.de1_compound_id
        ^ ")", [] )
    | Lem _ ->
        ( lemTODO "20" " (List.map (fun "^de1i.de1_pattern^" -> "^pp_body^") "
        ^ de1i.de1_compound_id
        ^ ")", [] )
    | Twf _ | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "make_aux_funcs"
        

(** ******************************** *)
(** subst for a prod                 *)
(** ******************************** *)

let pp_subst_prod 
    (m : pp_mode) (xd : syntaxdefn) 
    (subst : subst) (domain : nontermroot list) (isa_list_name_flag : bool) 
    (rule_ntr_name : nontermroot)
    (this_var : nonterm) (that_var : nt_or_mv) (that_var_fresh_suffix : suffix)
    (sub_var : string) (in_var : nonterm)
    (p : prod) 
    : (nontermroot list * (string * string * string) * (int_func list)) list = 

    let lhs_stnb = 
      Grammar_pp.canonical_symterm_node_body_of_prod rule_ntr_name p in
(* TODO: that rule_ntr_name above used to be subst.sb_this - which is wrong??*)
    let lhs_st = St_node(dummy_loc,lhs_stnb) in
    let sie = [] in
    let ((de1,de2) as de,de3,pptbe) 
        = Bounds.bound_extraction m xd dummy_loc [lhs_st]  in
    let lhs_pat = Grammar_pp.pp_symterm m xd sie de lhs_st in
    let lhs = 
      ( match m with 
      | Coq _ | Caml _ | Lem _ -> lhs_pat  
      | Isa _ | Hol _ | Twf _ -> 
(*           Auxl.subst_name subst.sb_name rule_ntr_name  ^ " " *)
          ( if subst.sb_multiple then sub_var
          else Grammar_pp.pp_nonterm m xd this_var ^ " " ^ Grammar_pp.pp_nt_or_mv m xd that_var )
          ^ " " ^ lhs_pat 
      | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_subst_prod") in
    
    (* all the bind clauses from the production with an mse of the *)
    (* same type as that_var*)

(*    let all_relevant_bind_clauses =      (*unused*)
      Auxl.option_map 
        (function b -> match b with
        | Bind(mse,nt) -> 
            if Auxl.result_type_of_mse xd mse = subst.sb_that (*root_of(that_var)*) then Some (mse,nt) 
            else None
        | _ -> None) 
        p.prod_bs in
*)

    let dependencies = ref [] in
    subst_split_inprod_counter := [];

    let substituted_singleton_rhs thing_s =
      ( match m with
      | Coq _ | Isa _ | Hol _ | Lem _ | Caml _ ->
	  let ssr = 
	    if subst.sb_multiple then 
              (match m with
              | Isa _ -> 
		  pp_list_assoc m;
		  (* tentative isa code for multiple subst *)
		  "(case list_assoc " 
		  ^ thing_s ^ " " 
		  ^ sub_var 
		  ^ " of None => " ^ lhs_pat
		  ^ " | Some " ^ Grammar_pp.pp_nonterm m xd this_var 
		  ^ " => " ^ Grammar_pp.pp_nonterm m xd this_var 
		  ^ ")"
              | Hol _ -> 
		  pp_list_assoc m;
		  (* tentative hol code for multiple subst *)
		  "(case list_assoc " 
		  ^ thing_s ^ " " 
		  ^ sub_var 
		  ^ " of NONE => " ^ lhs_pat
		  ^ " | SOME " ^ Grammar_pp.pp_nonterm m xd this_var 
		  ^ " => " ^ Grammar_pp.pp_nonterm m xd this_var 
		  ^ ")"
              | Lem _ -> 
		  pp_list_assoc m;
		  (* tentative hol code for multiple subst *)
                  lemTODO "21" (
		  "(match list_assoc_option " 
		  ^ thing_s ^ " " 
		  ^ sub_var 
		  ^ " with "
		  ^ "| Nothing -> " ^ lhs_pat
		  ^ "| Just " ^ Grammar_pp.pp_nonterm m xd this_var 
		  ^ " -> " ^ Grammar_pp.pp_nonterm m xd this_var 
		  ^ " end)"
                 )
              | Coq coq_opt -> 
		  pp_list_assoc m;
		  "(match list_assoc " (* A B eq *)
(*   ^ "(A:=" ^ Grammar_pp.pp_nt_or_mv_root m xd (root_of that_var) ^ ") " *)
(*   ^ "(B:=" ^ (root_of this_var) ^ ") " *)
		  ^ "eq_" ^ (Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that (*(root_of that_var)*)) 
		  ^ " "
		  ^ thing_s ^ " "
		  ^ sub_var 
		  ^ " with None => " ^ lhs_pat 
		  ^ " | Some " ^ Grammar_pp.pp_nonterm m xd this_var 
		  ^ " => " ^ Grammar_pp.pp_nonterm m xd this_var
		  ^ " end)"
              | Caml oo -> 
		  "(try List.assoc "
(*   ^ "(A:=" ^ Grammar_pp.pp_nt_or_mv_root m xd (root_of that_var) ^ ") " *)
(*   ^ "(B:=" ^ (root_of this_var) ^ ") " *)
		  ^ thing_s ^ " "
		  ^ sub_var 
		  ^ " with Not_found -> " ^ lhs_pat 
		  ^ ")" 
	      | Twf _ | Tex _ | Ascii _ | Lex _ | Yacc _ -> raise Auxl.ThisCannotHappen )
		
	    else
	      let that_s = Grammar_pp.pp_nt_or_mv m xd that_var in
	      let eq_s = 
		( match m with
		| Isa _ | Hol _ | Lem _ | Caml _ -> thing_s ^ "=" ^ that_s
		| Twf _ -> raise Auxl.ThisCannotHappen
		| Coq _ ->
		    ( if Auxl.require_locally_nameless xd 
		    then "eq_var"
		    else "eq_" ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that (*(root_of that_var)*) )
		    ^ " "
		    ^ thing_s ^ " " 
		    ^ that_s
		| Tex _ | Ascii _ | Lex _ | Yacc _ -> raise Auxl.ThisCannotHappen ) in
              "(if " ^ eq_s 
	      ^ " then " ^ Grammar_pp.pp_nonterm m xd this_var         
	      ^ " else " ^ lhs_pat ^ ")" 
	  in ["", ssr,[]]

      | Twf _ -> 
	  if subst.sb_multiple 
	  then 
	    ["", "<<<multiple subst not implemented>>>",[]]
	  else 
	    [ ( "/same", Grammar_pp.pp_nonterm m xd this_var, []) ; 
	      ( "/diff", lhs_pat ^ " <- neq " ^ thing_s ^ " " ^ Grammar_pp.pp_nt_or_mv m xd that_var,[]) ]

      | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_subst_prod"

       )

    in
    
    let list_of_prefix_and_rhs_and_list_funcs = 
      match p.prod_es with 
      | [ Lang_nonterm (ntrp,(ntr,suff)) ]  
        when (rule_ntr_name=subst.sb_this(*root_of(this_var)*) && subst.sb_that = Ntr ntrp) ->
	  let ntr_s = (* Grammar_pp.pp_nonterm m xd (ntr,suff)*)
            match lhs_stnb.st_es with
            | [Ste_st(_,St_nonterm(_,_,ntr0))] ->
		Grammar_pp.pp_nonterm m xd ntr0
            | _ -> failwith "internal error: lhs_stnb not of the right form" in
          (substituted_singleton_rhs ntr_s)

      | [ Lang_metavar (mvrp,(mvr,suff)) ] 
        when (rule_ntr_name=subst.sb_this(*root_of(this_var)*) && subst.sb_that = Mvr mvrp) ->
	  let mvr_s = (* Grammar_pp.pp_metavar m xd (mvr,suff) in *)
            match lhs_stnb.st_es with
            | [Ste_metavar(_,_,mvr0)] ->
		Grammar_pp.pp_metavar m xd mvr0
            | _ -> failwith "internal error: lhs_stnb not of the right form" in
          (substituted_singleton_rhs mvr_s)

      | es -> 
	  let pp_body, list_funcs =
	    List.split
	      (List.map 
                 (pp_subst_symterm_element 
		    m xd subst domain isa_list_name_flag rule_ntr_name 
		    this_var that_var that_var_fresh_suffix 
		    sub_var in_var p dependencies sie de)
                 lhs_stnb.st_es) in
          [ "",
	    ( match m with 
            | Caml _ -> 
                String.capitalize lhs_stnb.st_prod_name  
                ^ " "
                ^ ( if List.length pp_body = 0
                    then ""
                    else if List.length pp_body = 1 
                    then List.hd pp_body 
                    else "(" ^ String.concat "," pp_body ^ ")" )
            | Lem _ -> 
                String.capitalize lhs_stnb.st_prod_name  
                ^ " "
                ^ ( if List.length pp_body = 0
                    then ""
                    else if List.length pp_body = 1 
                    then List.hd pp_body 
                    else "" ^ String.concat " " pp_body ^ "" )
	    | Twf _ ->                                             (* FZ HACK HACK HACK *)
		let comp = List.tl (Str.split (Str.regexp "(\\| \\|)") lhs_pat) in
		let fresh_vars = ref [] in
		let pat = 
		  List.map2
		    (fun x y -> 
		      if (String.compare x y = 0) 
		      then begin
 			fresh_vars := ""::!fresh_vars;
			y 
		      end else begin
			let v = Auxl.fresh_nl() in
			fresh_vars := v::!fresh_vars;
			v
		      end )
		    pp_body comp in
		fresh_vars := List.rev !fresh_vars;
		"(" ^ lhs_stnb.st_prod_name 
                ^ " "
		^ String.concat " " pat ^ ")"
                ^ " <- " 
		^ String.concat " <- " 
		    (Auxl.option_map (fun x -> x)
		       (List.map2 (fun (x,y) fv ->           
			 if (String.compare x y = 0) 
			 then None
			 else begin
			   let l = String.length x in
			   let s = String.sub x 0 (l-1) in
			   Some (s^" "^fv^")") end )
			  (List.combine pp_body comp) !fresh_vars))
            | _ -> 
                lhs_stnb.st_prod_name 
                ^ " "
                ^ String.concat " " pp_body ),
	    List.concat list_funcs ]
    in
    
    List.map 
      (fun (pfx,rhs,list_funcs) -> (!dependencies, (p.prod_name^pfx, lhs, rhs), list_funcs) )
      list_of_prefix_and_rhs_and_list_funcs 
    
(** ******************************** *)
(** subst for a rule                 *)
(** ******************************** *)

let pp_subst_rule_const : subst -> pp_mode -> syntaxdefn -> nontermroot -> string = 
  fun subst m xd r_ntr_name ->
    match m with 
    | Isa _ ->  (* FZ move into pp_subst_rule ? *)
        Auxl.subst_name subst.sb_name (Grammar_pp.pp_nontermroot m xd r_ntr_name) (* FZ promote? *)
        ^ " :: \""
        ^ (if subst.sb_multiple then
          "(" ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^"*"
          ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^") list => "
          ^ Grammar_pp.pp_nontermroot_ty m xd r_ntr_name ^" => "
          ^ Grammar_pp.pp_nontermroot_ty m xd r_ntr_name 
        else
          Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^" => "
          ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^" => "
          ^ Grammar_pp.pp_nontermroot_ty m xd r_ntr_name ^" => "
          ^ Grammar_pp.pp_nontermroot_ty m xd r_ntr_name 
          )
        ^ "\"\n" 
    | _ -> Auxl.errorm m "pp_subst_rule_const"

let pp_subst_rule : subst -> pp_mode -> syntaxdefn -> nontermroot list -> rule -> int_func list = 
  fun subst m xd domain r ->

    (* TODO!!! this is no longer freshening w.r.t. the right things - need *)
    (* to fresh w.r.t. the secondaryised ntrs and mvrs *)
    (* probably also true elsewhere *)
    
    (* freshen these this and that wrt the things appearing in the rule *)
    (* let nts_used = ref (Auxl.nts_used_in_rule r) in *)
    (* let mvs_used = ref (Auxl.mvs_used_in_rule r) in *)
    let nts_used = ref (Context_pp.nts_used_in_lhss m xd r) in
    let mvs_used = ref (Context_pp.mvs_used_in_lhss m xd r) in

    let this_fresh_ntr = Auxl.secondary_ntr xd subst.sb_this in
    let that_fresh_ntmvr = Auxl.secondary_ntmvr xd subst.sb_that in

    let this_var = Auxl.fresh_nt !nts_used (this_fresh_ntr,[]) (*subst.sb_this*) in
    nts_used := this_var :: !nts_used;

    let that_var,that_var_fresh_suffix = 
      ( match that_fresh_ntmvr (* subst.sb_that*) with
      | Ntr ntr -> 
          let nt=Auxl.fresh_nt !nts_used (ntr,[]) in
	  nts_used := nt ::  !nts_used;
	  ((Ntr (fst nt),snd nt),snd nt)
      | Mvr mvr ->
          let mv=Auxl.fresh_mv !mvs_used (mvr,[]) in
          ((Mvr (fst mv),snd mv),snd mv) ) in


    let in_fresh_ntr = Auxl.secondary_ntr xd r.rule_ntr_name in
    let in_var = Auxl.fresh_nt !nts_used (in_fresh_ntr,[]) in
    
    let sub_var = "sub" in 
    (* tentative hack for multiple subst - todo: make it fresh *)

    let prods = List.filter (function p -> not p.prod_meta) r.rule_ps in

    let isa_list_name_flag = Auxl.compute_isa_list_name_flag r in

    let dep,clauses,list_funcs = 
      (fun (a,b,c) -> List.concat a, b, List.concat c)
	(Auxl.split3 
	   (List.concat
	      (List.map 
		 (pp_subst_prod 
		    m xd subst domain isa_list_name_flag r.rule_ntr_name 
		    this_var that_var that_var_fresh_suffix sub_var in_var) 
		 prods))) in

    let id = Auxl.subst_name subst.sb_name (Grammar_pp.pp_nontermroot m xd r.rule_ntr_name) in

    let header =
      ( match m with 
      | Coq _ ->       
	  ( (id
             ^ ( if subst.sb_multiple 
	     then 
	       " (" ^ sub_var ^ ":list (" 
	       ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that 
	       ^ "*" ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^ "))" 
	     else 
	       " (" ^ Grammar_pp.pp_nonterm m xd this_var ^ ":"
               ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^")"
	       ^ " (" ^ Grammar_pp.pp_nt_or_mv m xd that_var ^ ":"
               ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^ ")" )
	     ^ " (" ^ Grammar_pp.pp_nonterm m xd in_var ^ ":"
             ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name ^")",
             " {struct " ^ Grammar_pp.pp_nonterm m xd in_var ^"}", 
             " : " ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name ^ " :=\n" 
	     ^ "  match " ^ Grammar_pp.pp_nonterm m xd in_var ^ " with\n" ) )
      | Lem _ 
      | Caml _ ->       
          
	   (lemTODOm m "22" id
             ^ ( if subst.sb_multiple 
	     then 
	       " (" ^ sub_var ^ ": "
	       ^ 
		 (match m with 
		 | Caml _ -> 	
		     "(" 
	             ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that 
		     ^ "*" ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this 
		     ^ ") list"
		 | Lem _ -> 		  
		     "list "
	             ^ "(" 
		     ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that 
		     ^ "*" ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this 
		     ^ ")"
		 )
		 ^ ")" 
	     else 
	       " (" ^ Grammar_pp.pp_nonterm m xd this_var ^ ":"
               ^ Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^")"
	       ^ " (" ^ Grammar_pp.pp_nt_or_mv m xd that_var ^ ":"
               ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^ ")" )
	     ^ " (" ^ Grammar_pp.pp_nonterm m xd in_var ^ ":"
             ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name ^")",
             "", 
             " : " ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name ^ " =\n" 
	     ^ "  match " ^ Grammar_pp.pp_nonterm m xd in_var ^ " with\n" ) 
      | Isa _ -> 
	  (pp_subst_rule_const subst m xd r.rule_ntr_name, "", "")
      | Hol _ -> ("","","")
      | Twf _ -> 
	  ( (id ^ " : " 
	     ^ ( if subst.sb_multiple 
	     then 
	       " <<<FZ mult not impl>> "
	     else 
	       Grammar_pp.pp_nontermroot_ty m xd subst.sb_this ^ " -> "
               ^ Grammar_pp.pp_nt_or_mv_root_ty m xd subst.sb_that ^ " -> " 
               ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name ^ " -> "
	       ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name ^ " -> type.\n")
	    )  , "", "")
      | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.error "pp_subst_rule")
  
    in 
    
    let added_deps = List.map (fun x -> x.r_fun_id) list_funcs in

    { r_fun_id = id;
      r_fun_dep = dep @ added_deps;
      r_fun_type = r.rule_ntr_name;
      r_fun_header = header;
      r_fun_clauses = clauses } :: list_funcs

let subst_manifestly_needed subst xd ntr p = 
  if subst.sb_this=ntr then 
    match p.prod_es with 
    | [ Lang_nonterm (ntrp,(ntr,suff)) ]  
      when (subst.sb_that = Ntr ntrp)  -> true
    | [ Lang_metavar (mvrp,(mvr,suff)) ] 
      when (subst.sb_that = Mvr mvrp) -> true
    | _ -> false 
  else
    false

(** ********************************* *)
(** substitution: putting it together *)
(** ********************************* *)

let pp_subst_dep : pp_mode -> syntaxdefn -> subst -> int_funcs =
  fun m xd subst ->
    pp_foo_with_dependencies m xd 
      (subst_manifestly_needed subst)
      (pp_subst_rule subst)

let pp_substs : pp_mode -> syntaxdefn -> subst list -> int_funcs_collapsed =
  fun m xd sbs -> 
    List.concat (List.map (fun x -> 
      Dependency.collapse m xd (pp_subst_dep m xd x)) sbs )

(** ***************************************************** *)
(** ***************************************************** *)
(** free variables                                        *)
(** ***************************************************** *)
(** ***************************************************** *)

let has_isa_set_hom (fv : freevar) =
  List.exists (fun (x,_) -> x = "isa-set") fv.fv_homs


let pp_freevar_rule_const (fv : freevar) (m: pp_mode) (xd: syntaxdefn)
  (r_ntr_name: nontermroot): string = 
    match m with 
    | Isa _ ->  (* FZ move into pp_subst_rule ? *)
        Auxl.fv_name fv.fv_name (Grammar_pp.pp_nontermroot m xd r_ntr_name)
        ^ " :: \""
        ^ Grammar_pp.pp_nontermroot_ty m xd r_ntr_name ^" => "
        ^ Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that
        ^ (if has_isa_set_hom fv then " set" else " list")
        ^ "\"\n" 
    | _ -> Auxl.errorm m "pp_freevar_rule_const"

(** **************** *)
(** fv for a symterm *)
(** **************** *)

let list_append m = match m with | Lem _ | Hol _ -> " ++ " | _ -> " @ "

(* todo: is there a better idiom than this insane list of arguments? *)
let rec pp_fv_symterm
    (m : pp_mode) (xd : syntaxdefn) 
    (fv : freevar) (domain : nontermroot list) (rule_ntr_name : nontermroot)
    (p : prod) 
    (dependencies) 
    (sie : suffix_index_env) (de : dotenv)
    (st : symterm) : string option =
  match st with
  | St_node (l,stnb) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
  | St_nonterm (l,ntrp,nt)  -> 

      let nt_s = Grammar_pp.pp_nonterm_with_de_with_sie m xd sie de nt in

      (* if this nt is the type we're collecting, maybe collect it *)
      let fv_direct = 
 (** new code **)

	None in

(** old code **)


(*         if fv.fv_that = Ntr ntrp then  *)
(*           Some (match m with Isa _ | Hol _ | Caml _ -> "["^nt_s^"]"  *)
(*                            | Coq _ -> "(cons "^nt_s^" nil)" *)
(*                            | Tex _ | Ascii _ -> Auxl.error "internal: pp_fv_symterm\n") *)
(*         else None in *)

(** end of old code **)

      (* if there's a dependency, generate a recursive call *)
      let fv_recursive =
	let id = Grammar_pp.pp_nontermroot m xd ntrp in  (* FZ HERE *)
        if List.mem ntrp domain then 
      	  ( dependencies := (Auxl.fv_name fv.fv_name id (* (Auxl.promote_ntr xd ntrp) *) )::!dependencies;
	    let call = Auxl.fv_name fv.fv_name id (* (Auxl.promote_ntr xd ntrp) *) ^ " " ^ nt_s in
	    ( match m with 
	    | Twf _ -> Some call
	    | Isa _ | Hol _ | Lem _ | Caml _ | Coq _ -> Some ("("^call^")")
            | Tex _ | Ascii _ | Lex _ | Yacc _ -> assert false))
        else 
          None in

      let fv_both = match fv_direct,fv_recursive with
      | Some s,Some s' -> Some (s^list_append m^s')
      | Some s,None | None,Some s-> Some(s)
      | None,None -> None in

      (* work out what's binding in this nt *)
      let bound_things_glommed : mse = 
        glommed_bound_things_for_nonterm xd p fv.fv_that nt in

      (* calculate fv_both minus the bound things *)
      (* TODO: later optimise the singleton case *)
      let fv_both_real = match fv_both,bound_things_glommed with
      | None,_ -> None
      | Some s,Empty -> 
          Some s
      | Some s,_ ->  
          Some ( 
	  ( match m with
	  | Twf _ -> 
	      let result = Auxl.fresh_nl () in
	      let interm = Auxl.fresh_nl () in
	      result ^ " <- " ^ s ^ " " ^ interm ^ " <- " 
	      ^ "list_minus/natlist " ^ interm ^ " " 
	      ^ Grammar_pp.pp_mse_string m xd sie de bound_things_glommed ^ " " ^ result

	  | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "list_minus"
	  | Isa _ when has_isa_set_hom fv ->
	      "(" ^ s ^ " - set "
              ^ Grammar_pp.pp_mse_string m xd sie de bound_things_glommed ^")"
          | Isa _ | Hol _ | Lem _ | Caml _ | Coq _ -> 
	      pp_list_minus m;
              "(list_minus "
	      ^ 
		(match m with (* HACK is the name eq_thing always correct? *) 
		| Ascii _ | Tex _ | Twf _ | Lex _ | Yacc _ -> Auxl.errorm m "list_minus"
		| Isa _ | Hol _ | Lem _ | Caml _ -> "" 
		| Coq _ -> "eq_" ^ (Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that) ^ " " ) 
              ^ s ^" "
              ^ Grammar_pp.pp_mse_string m xd sie de bound_things_glommed ^")")  )
      in

      fv_both_real
           
  | St_nontermsub (l,ntrpl,ntrpt,nt)  -> 
      raise ThisCannotHappen  (* never occurs in a canonical symterm_element *)
  | St_uninterpreted (p,s) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
        
        
and pp_fv_symterm_element 
    (m : pp_mode) (xd : syntaxdefn) 
    (fv : freevar) (domain : nontermroot list) (rule_ntr_name : nontermroot)
    (p : prod) 
    (dependencies) 
    (sie : suffix_index_env) (de : dotenv) (isa_list_name_flag : bool)
    (ste : symterm_element) : string option * int_func list =
  match ste with
  | Ste_st(_,st) -> 
      pp_fv_symterm m xd fv domain rule_ntr_name p dependencies sie de st, []
  | Ste_metavar (l,mvrp,mv) -> 

(** new code starts here **)

   if false then 

(** new code ends here **)

      (* TODO: TAKE ACCOUNT OF BINDING *)
      let mv_s = Grammar_pp.pp_metavar_with_de_with_sie m xd sie de mv in
        
      (* if this mv is of the type we're collecting, and it's not used as a binder, collect it*)
      if fv.fv_that = Mvr mvrp 
          && not(directly_binding_usages_of_this_metavar xd p mv)
      then
        Some 
          (match m with 
          | Isa _ | Hol _ | Lem _ | Caml _ -> ("["^mv_s^"]") 
          | Coq _ -> ("(cons "^mv_s^" nil)") 
	  | Twf _ -> ("(natlist/cons "^mv_s^" natlist/nil)") 
          | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_fv_symterm_element"
          ), []
      else
        None, []
(** new code starts here **)
      else
        None, []
(** new code ends here **)

  | Ste_var (l,mvrp,var) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
  | Ste_list (l,stlis) -> 
      ( match stlis with 
      | [Stli_listform stlb] -> 
	  pp_fv_symterm_list_body m xd fv domain rule_ntr_name p dependencies sie de isa_list_name_flag stlb
      | _-> raise ThisCannotHappen (* never occurs in a canonical symterm_element *) )

and make_aux_funcs_tuple_fv m xd fv domain rule_ntr_name p dependencies sie de isa_list_name_flag split_suffix els pattern =
  let (el_hd,el_tl) = (List.hd els, List.tl els) in

  let name = Grammar_pp.make_name_elements m xd false els in
  let name_tl = Grammar_pp.make_name_elements m xd false el_tl in
  let id = Auxl.fv_name fv.fv_name name in
  let id_tl = Auxl.fv_name fv.fv_name name_tl in

  let typ = 
    if List.length el_tl = 1 
    then Grammar_pp.make_name_elements m xd true els 
    else         
      let h = Grammar_pp.make_name_elements m xd true [ el_hd ] in  
      let t = Grammar_pp.make_name_elements m xd true el_tl in
      h^"*"^t in
  
  let output_typ = Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that ^" list" in
  
  let lhs = 
    if List.length el_tl = 1 
    then "("^String.concat "," 
		(List.map 
		   (fun s -> Auxl.hide_isa_trailing_underscore m (s^"_")) 
		   pattern)^")"
    else   
      "("^(Auxl.hide_isa_trailing_underscore m ((List.hd pattern)^"_"))
      ^","^(Auxl.hide_isa_trailing_underscore m ((String.concat "_" (List.tl pattern))^"_"))^")" in

  let rhs,aux_funcs =
    if List.length el_tl = 1
    then
      String.concat (list_append m) (Auxl.option_map (fun x -> x)
        (fst 
           (List.split 
              ( List.map
	          ( pp_fv_symterm_element 
		      m xd fv domain rule_ntr_name 
		      p dependencies ((Si_var ("_",0))::sie) de isa_list_name_flag) 
	          els )))), []
    else
      let arg_tl = (Auxl.hide_isa_trailing_underscore m ((String.concat "_" (List.tl pattern))^"_")) in

      dependencies := (id_tl^split_suffix)::!dependencies;
      ( ( match (fst (pp_fv_symterm_element 
			m xd fv domain rule_ntr_name 
			p dependencies ((Si_var ("_",0))::sie) de isa_list_name_flag el_hd )) with
      | Some s -> s ^ list_append m
      | None -> (* Auxl.warning "empty symterm_element\n" *) " " )
      ^ "(" ^ id_tl^split_suffix ^ " " ^ arg_tl ^")" ), 
      make_aux_funcs_tuple_fv m xd fv domain rule_ntr_name p dependencies sie de isa_list_name_flag split_suffix el_tl (List.tl pattern) in

  { r_fun_id = id^split_suffix;
    r_fun_dep = !dependencies;
    r_fun_type = typ^split_suffix;
    r_fun_header = (id ^split_suffix ^ " :: \"" ^ typ ^ " => " ^ output_typ ^ "\"\n","","");
    r_fun_clauses = [ "", lhs, rhs ] } :: aux_funcs  (* FZ add prefix here *)

(* used to add suffixes when splitting functions over the same list type in a production *)
and fv_list_split_inprod_counter = ref [] 

and pp_fv_symterm_list_body 
    (m : pp_mode) (xd : syntaxdefn) 
    (fv : freevar) (domain : nontermroot list) (rule_ntr_name : nontermroot)
    (p : prod) 
    (dependencies) 
    (sie : suffix_index_env) (de : dotenv) (isa_list_name_flag : bool)
    (stlb : symterm_list_body) : string option * int_func list =

  (* code similar to pp_symterm_list_body in grammar_pp.ml - refactor? *)
  let (de1,de2)=de in
  (* print_string ("[[["^pp_plain_dotenv de^"]]]");flush stdout; *)
  let de1i = Grammar_pp.de1_lookup de1 stlb.stl_bound in
  (* TODO optimise the output in the common case of a list of singletons *)
  match m with
  | Twf _ | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_fv_symterm_list_body"
  | Isa _ | Coq _ | Hol _ | Lem _ | Caml _ ->
      let pp_body_elements, funcs =
	let body_options, funcs = 
	  List.split
	    ( List.map
		( pp_fv_symterm_element 
		    m xd fv domain rule_ntr_name 
		    p dependencies ((Si_var ("_",0))::sie) de isa_list_name_flag) 
		stlb.stl_elements ) in
	(Auxl.option_map (fun x -> x) body_options, List.concat funcs) in

      let body_elements = 
        let tmp = 
          ( match m with
          | Coq _ -> Auxl.insert_append m pp_body_elements
          | Isa _ when has_isa_set_hom fv -> String.concat " \\<union> " pp_body_elements
          | _ -> String.concat (list_append m) pp_body_elements ) in
        if List.length pp_body_elements = 1 
        then tmp
        else "(" ^ tmp ^ ")" in

      ( match pp_body_elements with
      | [] -> (match m with
                 | Coq _ -> Some "nil"
                 | Isa _ when has_isa_set_hom fv -> Some "{}"
                 | _ -> Some "[]"), funcs
      | _ -> 
	  ( match m with 
          | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.error "pp_fv_symterm_list_body"
	  | Isa io when io.ppi_isa_primrec ->
              let args = 
	        String.concat "_" 
		  (List.map (fun (x,y) -> 
		    Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_var ("",0))::sie) x) de1i.de1_ntmvsns) in

              let post_name = Grammar_pp.make_name_elements m xd false stlb.stl_elements  in 

              let typ_list = (Grammar_pp.make_name_elements m xd true stlb.stl_elements) ^ " list" in

              let id_list = Auxl.fv_name fv.fv_name post_name ^ "_list" in
              let id_tuple = Auxl.fv_name fv.fv_name post_name in

	      let split_suffix = 
		let pre_split_suffix = 
		  if isa_list_name_flag then "_"^p.prod_name else "" in
		let counter_suffix = 
		  try 
		    let c_p = List.assoc (typ_list^pre_split_suffix) !fv_list_split_inprod_counter in
		    c_p := !c_p + 1;
		    string_of_int (!c_p)
		  with Not_found -> (
		    fv_list_split_inprod_counter := 
		      ((typ_list^pre_split_suffix),ref 0)::!fv_list_split_inprod_counter;
		    "" )
		in
		pre_split_suffix ^ counter_suffix in

              let output_typ = Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that ^" list" in

	      let (rhs_sc,tuple_aux_fun, list_deps) =
	        if List.length de1i.de1_ntmvsns = 1 
	        then body_elements, [], !dependencies 
	        else (* build an aux funcs over the tuple *)
		  let pattern = 
		    (List.map (fun (x,y) -> 
		      Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_punct "")::sie) x) de1i.de1_ntmvsns) in

		  "(" ^ id_tuple^split_suffix ^ " " ^ Auxl.hide_isa_trailing_underscore m (args ^ "_")^")",
                  (make_aux_funcs_tuple_fv m xd fv domain rule_ntr_name p dependencies sie de isa_list_name_flag split_suffix stlb.stl_elements pattern),
		  [ id_tuple^split_suffix ] in

              Some ( "(" ^ id_list^split_suffix ^ " " ^ args ^ "_list)" ), 
              ( { r_fun_id = id_list^split_suffix;
                  r_fun_dep = (id_list^split_suffix)::list_deps;
                  r_fun_type = typ_list^split_suffix;
                  r_fun_header = (id_list ^split_suffix^ " :: \"" ^ typ_list ^ " => " ^ output_typ ^ "\"\n","","");
                  r_fun_clauses =
		  [ ("", "Nil", "[]");
                    ("", "(" ^ Auxl.hide_isa_trailing_underscore m (args ^"_")^"#" ^ Auxl.hide_isa_trailing_underscore m(args ^"_list_")^")", 
                     rhs_sc ^ list_append m ^ "(" ^ id_list^split_suffix ^ " " ^ Auxl.hide_isa_trailing_underscore m (args ^ "_list_")^")" ) ] } 
                   :: tuple_aux_fun )

	  | Isa io when not io.ppi_isa_primrec && has_isa_set_hom fv ->
              let pp_body = String.concat " \\<union> " pp_body_elements in
	      Some ("(\\<Union>"^de1i.de1_pattern^"\\<in> set "^ de1i.de1_compound_id^". "^ pp_body^")"), funcs
	  | Isa io when not io.ppi_isa_primrec ->
              let pp_body = String.concat (list_append m) pp_body_elements in
	      Some
		("(concat (map (%"^de1i.de1_pattern^". "^pp_body^") "
	         ^ de1i.de1_compound_id
	         ^ "))"), funcs
	  | Hol _ ->
              let pp_body = String.concat " ++ " pp_body_elements in
              Some 
		("(FLAT (MAP (\\"^de1i.de1_pattern^". "^pp_body^") "
	         ^ de1i.de1_compound_id
		 ^ "))"), funcs
	  | Caml _ ->
              let pp_body = String.concat (list_append m) pp_body_elements in
              Some 
		("(List.flatten (List.map (fun "^de1i.de1_pattern^" -> "^pp_body^") "
		 ^ de1i.de1_compound_id
		 ^ "))"), funcs
	  | Lem _ ->
              let pp_body = String.concat (lemTODO "23" " ++ ") pp_body_elements in
              Some 
		("(List.concat (List.map (fun "^de1i.de1_pattern^" -> "^pp_body^") "
		 ^ de1i.de1_compound_id
		 ^ "))"), funcs
	  | Coq co when co.coq_expand_lists -> 
	      let var_list = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in
              let args = 
	        String.concat "_" 
		  (List.map (fun (x,y) -> 
		    Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_var ("",0))::sie) x) de1i.de1_ntmvsns) in

              let post_name = Grammar_pp.make_name_elements m xd false stlb.stl_elements  in 
	      let suf =	"list_" ^ post_name in
              let typ_list = "list_" ^ (Grammar_pp.make_name_elements m xd false stlb.stl_elements) in

              let id_list = Auxl.fv_name fv.fv_name post_name ^ "_list" in

              let output_typ = "list "^Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that in
	      
	      let header =
		( id_list ^" (l:"^typ_list^")",
		  "",
		  " : " ^ output_typ ^ " :=\n"
		  ^ "  match l with\n"
		) in

              Some ( "(" ^ id_list ^ " " ^ args ^ "_list)" ), 
                  [ { r_fun_id =  id_list;
                      r_fun_dep = id_list::!dependencies;
                      r_fun_type = typ_list;
		      r_fun_header = header;
                      r_fun_clauses =
		      [ ("", "Nil_"^suf, "nil");
			("", "Cons_"^suf^" " ^ (String.concat " " var_list) ^" " ^ args ^"_list_", 
                         "app " ^ body_elements ^ " " ^ "(" ^ id_list ^ " " ^ args ^ "_list_)" ) ] }
                  ] 
	  | Coq co when not co.coq_expand_lists ->
              let pp_body = String.concat " ++ " pp_body_elements in
	      let flat_map =  if !(co.coq_locally_nameless) then "union_map" else "flat_map" in
	      if List.length (Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern) = 1
              (* TODO: pass in more info from bounds.ml to remove that regexp? *)
	      then 
		Some 
		  ("("^flat_map^" (fun ("^de1i.de1_pattern^":"^de1i.de1_coq_type_of_pattern^") => "^pp_body^") "
		   ^ de1i.de1_compound_id
		   ^ ")"), funcs
	      else
		Some (* FZ freshen pat_ *)
		  ("(flat_map (fun (pat_:"^de1i.de1_coq_type_of_pattern^") => match pat_ with " ^ de1i.de1_pattern ^ " => "^pp_body^" end) "
		   ^ de1i.de1_compound_id
		   ^ ")"), funcs
       ) )
      

(** ************* *)
(** fv for a prod *)
(** ************* *)

let pp_freevar_prod 
    (m : pp_mode) (xd : syntaxdefn) 
    (fv : freevar) (domain : nontermroot list) 
    (isa_list_name_flag : bool) (rule_ntr_name : nontermroot)
    (p : prod) 
    : nontermroot list * (string * string * string) * int_func list = 

     let lhs_stnb = 
       Grammar_pp.canonical_symterm_node_body_of_prod rule_ntr_name p in
     let lhs_st = St_node(dummy_loc,lhs_stnb) in
     let sie = [] in
     let ((de1,de2) as de,de3,pptbe) 
         = Bounds.bound_extraction m xd dummy_loc [lhs_st]  in
     let lhs = Grammar_pp.pp_symterm m xd sie de lhs_st in

    let dependencies = ref [] in
    fv_list_split_inprod_counter := [];

(** new code starts here **)    
    let freevar_singleton_rhs thing_s = 
      let rhs =
        (match m with 
	| Isa _ when (List.exists (fun (x,_) -> x = "isa-set") fv.fv_homs) -> "{"^thing_s^"}"
        | Isa _ | Hol _ | Lem _ | Caml _ -> ("["^thing_s^"]") 
        | Coq co ->
	    if not !(co.coq_locally_nameless)
	    then "(cons "^thing_s^" nil)"
	    else "{{"^thing_s^"}}"
	| Twf _ -> ("(natlist/cons "^thing_s^" natlist/nil)") 
        | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "freevar_singleton_rhs"
        ) in
      let funcs = [] (* REALLY??? *) in
      (!dependencies, (p.prod_name, lhs,rhs), funcs)  in

    match p.prod_es with 
    | [ Lang_nonterm (ntrp,(ntr,suff)) ]  
      when (rule_ntr_name=fv.fv_this(*root_of(this_var)*) && fv.fv_that = Ntr ntrp) ->
	let ntr_s = (* Grammar_pp.pp_nonterm m xd (ntr,suff)*)
          match lhs_stnb.st_es with
          | [Ste_st(_,St_nonterm(_,_,ntr0))] ->
	      Grammar_pp.pp_nonterm m xd ntr0
          | _ -> failwith "internal error: lhs_stnb not of the right form" in
        (freevar_singleton_rhs ntr_s)

    | [ Lang_metavar (mvrp,(mvr,suff)) ] 
      when (rule_ntr_name=fv.fv_this(*root_of(this_var)*) && fv.fv_that = Mvr mvrp) ->
	let mvr_s = (* Grammar_pp.pp_metavar m xd (mvr,suff) in *)
          match lhs_stnb.st_es with
          | [Ste_metavar(_,_,mvr0)] ->
	      Grammar_pp.pp_metavar m xd mvr0
          | _ -> failwith "internal error: lhs_stnb not of the right form" in
        (freevar_singleton_rhs mvr_s)
          
    | es -> 

(** new code ends here **)

        let rhs_elements, funcs = 
          let elements_options, funcs =
	    List.split 
	      (List.map
	         (pp_fv_symterm_element m xd fv domain rule_ntr_name p dependencies sie de isa_list_name_flag)
                 lhs_stnb.st_es) in
          (Auxl.option_map (fun x -> x) elements_options, List.concat funcs) in
        
        let rhs = 
          match rhs_elements with
          | [] -> 
	      (match m with 
	      | Isa _ when has_isa_set_hom fv -> "{}"
	      | Isa _ | Hol _ | Lem _ | Caml _ -> "[]" 
	      | Coq co -> 
		  if not !(co.coq_locally_nameless)
		  then "nil"
		  else "{}"
	      | Twf _ -> "natlist/nil"
              | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_freevar_prod")
          | _ -> 
	      ( match m with 
	      | Isa _ when has_isa_set_hom fv -> String.concat " \\<union> " rhs_elements
              | Isa _ | Caml _ | Lem _ -> String.concat (list_append m) rhs_elements 
              | Hol _ -> String.concat " ++ " rhs_elements 
	      | Coq co -> 
		  if not !(co.coq_locally_nameless)
		  then Auxl.insert_append m rhs_elements
		  else String.concat " \\u " rhs_elements
	      | Twf _ -> Auxl.insert_append m rhs_elements
              | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_freevar_prod")
                
        in
        
        (!dependencies, (p.prod_name, lhs,rhs), funcs) 
          
let pp_freevar_rule : freevar -> pp_mode -> syntaxdefn -> nontermroot list -> rule -> int_func list = 
  fun  fv m xd domain r ->

    let prods = List.filter (fun p -> not p.prod_meta) r.rule_ps in

    let isa_list_name_flag = Auxl.compute_isa_list_name_flag r in

    let fv_prods = 
      List.map 
        (pp_freevar_prod m xd fv domain isa_list_name_flag r.rule_ntr_name) 
        prods
    in

    let clauses = 
      List.map (fun (_,s,_) -> s) fv_prods in
    let funcs =
      List.flatten (List.map (fun (_,_,f) -> f) fv_prods) in
    let dep = 
      List.flatten (List.map (fun (d,_,_) -> d) fv_prods) in

    let header =
      ( match m with 
      | Coq co -> 
	  let nts_used = Context_pp.nts_used_in_lhss m xd r in
          let fresh_var_ntr = Auxl.secondary_ntr xd r.rule_ntr_name  in
	  let fresh_var = Auxl.fresh_nt nts_used (fresh_var_ntr,[]) in

	  ( Auxl.fv_name fv.fv_name r.rule_ntr_name 
	    ^ " (" ^ Grammar_pp.pp_nonterm m xd fresh_var
	    ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name 
	    ^ ") ",
            "",
	    (if not !(co.coq_locally_nameless) 
	    then ": list " ^ Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that
	    else ": vars")
	    ^ " :=\n  match " ^ Grammar_pp.pp_nonterm m xd fresh_var ^ " with\n" )
      | Isa _ -> 
	  (pp_freevar_rule_const fv m xd r.rule_ntr_name,"","")
      | Hol _ -> ("","","")
      | Lem _  
      | Caml _ -> 
	  let nts_used = Context_pp.nts_used_in_lhss m xd r in
          let fresh_var_ntr = Auxl.secondary_ntr xd r.rule_ntr_name  in
	  let fresh_var = Auxl.fresh_nt nts_used (fresh_var_ntr,[]) in
          let ntrn = Grammar_pp.pp_nontermroot m xd r.rule_ntr_name in

	  lemTODOm m "24" (
          Auxl.fv_name fv.fv_name ntrn (* r.rule_ntr_name *)
	  ^ " (" ^ Grammar_pp.pp_nonterm m xd fresh_var
	  ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name 
	  ^ ") "),
          "",
	  ": " 
	  ^ 
	    (match m with 
	    | Caml _ -> Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that ^ " list"
	    | Lem _ -> " list " ^ Grammar_pp.pp_nt_or_mv_root_ty m xd fv.fv_that
	    )
          ^ " =\n  match " ^ Grammar_pp.pp_nonterm m xd fresh_var ^ " with\n" 
         
      | Twf _ ->
	  ( Auxl.fv_name fv.fv_name r.rule_ntr_name ^ " : "
	    ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name ^ " -> "
	    ^ "natlist -> type.\n" ), "", ""
	  
      | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_freevar_rule")
      
    in 
    let id = Auxl.fv_name fv.fv_name (Grammar_pp.pp_nontermroot m xd r.rule_ntr_name) in

    let added_deps = List.map (fun x -> x.r_fun_id) funcs in

    { r_fun_id = id;
      r_fun_dep = dep @ added_deps;
      r_fun_type = r.rule_ntr_name;
      r_fun_header = header;
      r_fun_clauses = clauses } :: funcs

(* let freevar_manifestly_needed fv xd p =  *)
(*   match fv.fv_that with  *)
(*   | Ntr ntr -> NtrSet.mem ntr (Auxl.primary_ntrs_used_in_prod xd true p) *)
(*   | Mvr mvr -> MvrSet.mem mvr (Auxl.primary_mvrs_used_in_prod p) *)

let freevar_manifestly_needed fv xd ntr p = 
  if fv.fv_this=ntr then 
    match p.prod_es with 
    | [ Lang_nonterm (ntrp,(ntr,suff)) ]  
      when (fv.fv_that = Ntr ntrp)  -> true
    | [ Lang_metavar (mvrp,(mvr,suff)) ] 
      when (fv.fv_that = Mvr mvrp) -> true
    | _ -> false 
  else
    false

let pp_freevar_dep : pp_mode -> syntaxdefn -> freevar -> int_funcs = 
  fun m xd fv -> 
    pp_foo_with_dependencies m xd 
      (freevar_manifestly_needed fv) 
      (pp_freevar_rule fv)

let pp_freevars : pp_mode -> syntaxdefn -> freevar list -> int_funcs_collapsed =
  fun m xd fvs -> 
    List.concat (List.map (fun x -> 
      Dependency.collapse m xd (pp_freevar_dep m xd x)) fvs)
