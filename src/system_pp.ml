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


(* Print auxiliary lemmas if necessary *)

let rec uses_lists_element e =
  match e with
  | Lang_nonterm (_,_)
  | Lang_metavar (_,_)
  | Lang_terminal (_)
  | Lang_sugaroption (_) -> false 
  | Lang_option es -> List.exists uses_lists_element es
  | Lang_list _ -> true

let uses_lists_prod p =
  not p.prod_meta && List.exists uses_lists_element p.prod_es

let uses_lists_rule r =
  not r.rule_meta && List.exists uses_lists_prod r.rule_ps

let uses_lists_syntaxdefn xd =
  List.exists uses_lists_rule xd.xd_rs

let pp_auxiliary_lemmas m xd =
  if uses_lists_syntaxdefn xd then begin
    Substs_pp.pp_list_mono_lemmas m;
    Substs_pp.pp_list_all_cong_lemma m;
    Substs_pp.pp_list_simp_lemmas m xd
  end

(* EXPERIMENTAL EXPERIMENTAL EXPERIMENTAL EXPERIMENTAL EXPERIMENTAL EXPERIMENTAL *)

let pp_functions_locally_nameless fd m sd xd_transformed =
  let funcs_open = Ln_transform.pp_open m xd_transformed in
  let funcs_subrules = Subrules_pp.pp_subrules m xd_transformed xd_transformed.xd_srs in
  (* let auxfns = Substs_pp.pp_auxfns m sd.syntax in *)
  let arities = Ln_transform.pp_arities m sd.syntax xd_transformed in
  let substs = Ln_transform.pp_substs m xd_transformed xd_transformed.xd_sbs in
  let freevars = Ln_transform.pp_freevars m xd_transformed xd_transformed.xd_fvs in
  (* let contexts = Context_pp.pp_context m sd.syntax xd_transformed.xd_crs in *)
  let library = 
    ( match m with
    | Isa io -> fst (!(io.isa_library))
    | Hol ho -> fst (!(ho.hol_library))
    | Lem lo -> fst (!(lo.lem_library))
    | Coq co -> fst (!(co.coq_library))
    | Twf wo -> fst (!(wo.twf_library))
    | Caml oo-> fst (!(oo.caml_library))
    | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_functions") in
  let aux_list_functions =
    ( match m with
    | Coq co -> !(Auxl.the co.coq_list_aux_funcs) 
    | _ -> "" ) in
  output_string fd "(* EXPERIMENTAL *)\n";
  output_string fd (Auxl.big_line_comment m "auxiliary functions on the new list types");
  output_string fd aux_list_functions;
  output_string fd (Auxl.big_line_comment m "library functions");
  output_string fd library;
  output_string fd (Auxl.big_line_comment m "subrules");
  output_string fd (Dependency.compute m xd_transformed funcs_subrules);
  output_string fd (Auxl.big_line_comment m "arities");
  output_string fd (Dependency.compute m sd.syntax arities);
  output_string fd (Auxl.big_line_comment m "opening up abstractions");
  output_string fd (Dependency.compute m xd_transformed funcs_open);
  output_string fd (Auxl.big_line_comment m "terms are locally-closed pre-terms");
  Ln_transform.pp_lcs fd m xd_transformed;
(*   output_string fd (Auxl.big_line_comment m "auxiliary functions"); *)
(*   output_string fd (Dependency.compute m sd.syntax auxfns); *)
  output_string fd (Auxl.big_line_comment m "free variables");
  output_string fd (Dependency.compute m xd_transformed freevars); 
  output_string fd (Auxl.big_line_comment m "substitutions");
  output_string fd (Dependency.compute m sd.syntax substs);
(*   output_string fd (Auxl.big_line_comment m "\n" "context application"); *)
(*   output_string fd (Dependency.compute m sd.syntax contexts) *)
  ()

let set_locally_nameless m =
  match m with
  | Coq co -> co.coq_locally_nameless := true
  | _ -> Auxl.error "locally-nameless: only the Coq backend understand {{ repr-locally-nameless }}.\n"

let pp_systemdefn_core_locally_nameless fd m sd lookup = 
  set_locally_nameless m;
  let xd_ln_transformed = Ln_transform.ln_transform_syntaxdefn m sd.syntax in
  let relations_ln_transformed = Ln_transform.ln_transform_fun_or_reln_defnclass_list m sd.syntax sd.relations in 
  Embed_pp.pp_embeds fd m sd.syntax lookup sd.syntax.xd_embed_preamble;
  output_string fd (Auxl.big_line_comment m "syntax");
  output_string fd (Grammar_pp.pp_syntaxdefn m xd_ln_transformed);
  output_string fd ("\n");
  pp_functions_locally_nameless fd m sd xd_ln_transformed;
  Embed_pp.pp_embeds fd m sd.syntax lookup sd.syntax.xd_embed;
  output_string fd ("\n");
  Defns.pp_fun_or_reln_defnclass_list fd
      m xd_ln_transformed (Term_parser.make_parser xd_ln_transformed) relations_ln_transformed;
  output_string fd ("\n");
  output_string fd (Ln_transform.ln_infrastructure m xd_ln_transformed relations_ln_transformed);
  output_string fd ("\n");
  ( match m with
  | Coq co when not co.coq_expand_lists ->
	let ip = Coq_induct.pp_induction m xd_ln_transformed xd_ln_transformed.xd_rs in
	if ip <> "" then begin 
          output_string fd (Auxl.big_line_comment m "induction principles");
          output_string fd ip;
          output_string fd ("\n")
        end
    | _ -> () )
(* END EXPERIMENTAL END EXPERIMENTAL END EXPERIMENTAL END EXPERIMENTAL END EXPERIMENTAL END EXPERIMENTAL *)

let pp_functions fd m sd lookup =
  let funcs_subrules = Subrules_pp.pp_subrules m sd.syntax sd.syntax.xd_srs in
  let auxfns = Substs_pp.pp_auxfns m sd.syntax sd.syntax.xd_axs in
  let substs = Substs_pp.pp_substs m sd.syntax sd.syntax.xd_sbs in
  let freevars = Substs_pp.pp_freevars m sd.syntax sd.syntax.xd_fvs in
  let contexts = Context_pp.pp_context m sd.syntax lookup sd.syntax.xd_crs in
  let library = 
    ( match m with
    | Isa io -> fst (!(io.isa_library))
    | Hol ho -> fst (!(ho.hol_library))
    | Lem lo -> fst (!(lo.lem_library))
    | Coq co -> fst (!(co.coq_library))
    | Twf wo -> fst (!(wo.twf_library))
    | Caml oo ->fst (!(oo.caml_library))
    | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m  "pp_functions\n") in
  let aux_list_functions =
    ( match m with
    | Coq co -> !(Auxl.the co.coq_list_aux_funcs) 
    | _ -> "" ) in
  output_string fd (Auxl.big_line_comment m "auxiliary functions on the new list types");
  output_string fd aux_list_functions;
  output_string fd (Auxl.big_line_comment m "library functions");
  output_string fd library ;
  output_string fd (Auxl.big_line_comment m "subrules");
  output_string fd (Dependency.compute m sd.syntax funcs_subrules);
  output_string fd (Auxl.big_line_comment m "auxiliary functions");
  output_string fd (Dependency.compute m sd.syntax auxfns);
  output_string fd (Auxl.big_line_comment m "free variables");
  output_string fd (Dependency.compute m sd.syntax freevars);
  output_string fd (Auxl.big_line_comment m "substitutions");
  output_string fd (Dependency.compute m sd.syntax substs);
  output_string fd (Auxl.big_line_comment m "context application");
  output_string fd (Dependency.compute m sd.syntax contexts);
  ()

let pp_library fd m = 
  let pp_lib x =
    let l = fst !x in
    if l <> "" then begin
      output_string fd (Auxl.big_line_comment m "library functions");
      output_string fd l;
      x := ("", snd !x)
    end in
  match m with
    | Isa io -> pp_lib io.isa_library
    | Hol ho -> pp_lib ho.hol_library 
    | Lem lo -> pp_lib lo.lem_library 
    | Coq co -> pp_lib co.coq_library
    | Twf wo -> pp_lib wo.twf_library
    | Caml oo-> pp_lib oo.caml_library
    | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_library"

let pp_struct_entry fd m sd xd_expanded lookup stre : unit =
  pp_library fd m;
  ( let xd = sd.syntax in
  match stre with
  | Struct_md mvr -> 
      let mvd = Auxl.mvd_of_mvr xd mvr in
      let pp_loc = if !Global_option.output_source_locations >=2 then Grammar_pp.pp_source_location m mvd.mvd_loc else "" in
      output_string fd pp_loc;
      output_string fd (Grammar_pp.pp_metavardefn m xd mvd)

  | Struct_rs ntrs -> 
      let rs = List.map (fun ntr -> Auxl.rule_of_ntr xd_expanded ntr) ntrs in
      let s = List.flatten (List.map (function r -> r.rule_loc) rs) in
      let pp_locs = if !Global_option.output_source_locations >=2 then Grammar_pp.pp_source_location m s else "" in
      output_string fd pp_locs;
      output_string fd (Grammar_pp.pp_rule_list m xd_expanded rs);
      (* induction_principles_rules *)
      ( match m with
      | Coq co when not co.coq_expand_lists ->
          let ip = Coq_induct.pp_induction m xd_expanded rs in
          if ip <> "" then begin
            output_string fd (Auxl.big_line_comment m "induction principles");
            output_string fd ip
          end
      | _ -> ())

  | Struct_axs xs ->
      let axs = 
        List.map
          (fun f -> List.find (fun (f',_) -> String.compare f f' = 0) xd.xd_axs)
          xs in
      output_string fd (Dependency.compute m xd (Substs_pp.pp_auxfns m xd axs)) (* why is this needed here? *)

  | Struct_fun_or_defnclass s ->
      let frdc = 
	List.find 
	  (fun frdc -> match frdc with 
	  | FDC fdc -> if String.compare fdc.fdc_name s = 0 then true else false 
	  | RDC dc -> if String.compare dc.dc_name s = 0 then true else false )
	  sd.relations in
      Defns.pp_fun_or_reln_defnclass_list fd m xd lookup [frdc]

  | Struct_srs xs ->
      (* find the relevant funcs_subrules *)
      let subrules =
  	List.map (fun (ntrl,ntru) ->
  	  List.find
  	    (fun sr -> String.compare sr.sr_lower ntrl = 0 && String.compare sr.sr_upper ntru = 0)
  	    xd.xd_srs)
  	  xs in
      (* print their source locations *)
      let s = List.flatten (List.map (function sr -> sr.sr_loc) subrules) in
      let pp_locs = if !Global_option.output_source_locations >=2 then Grammar_pp.pp_source_location m s else "" in

      (* print them out *)
      let funcs_subrules = 
	Subrules_pp.pp_subrules m sd.syntax subrules in
      
      output_string fd 
        (Auxl.print_with_comment m "\n" "subrules"
  	   (pp_locs ^ Dependency.compute m xd funcs_subrules))

  | Struct_fvs xs ->
      (* find the relevant funcs_subrules *)
      let freevars =
  	List.map (fun (n,ntr,ntmvr) ->
	  (* print_endline ("searching: "^n^" "^ntr^" "^(Grammar_pp.pp_plain_nt_or_mv_root ntmvr)); *)
  	  List.find
  	    (fun fv -> 
	      (* print_endline ("  found: "^fv.fv_name^" "^fv.fv_this^" "^(Grammar_pp.pp_plain_nt_or_mv_root fv.fv_that)); *)
	      String.compare fv.fv_name n = 0 
		&& String.compare fv.fv_this ntr = 0 
                && compare fv.fv_that ntmvr = 0)
  	    xd.xd_fvs)
  	  xs in
      let s = List.flatten (List.map (function fv -> fv.fv_loc) freevars) in
      let pp_locs = if !Global_option.output_source_locations >=2 then Grammar_pp.pp_source_location m s else "" in

      (* print them out *)
      let funcs_freevars =
  	Substs_pp.pp_freevars m sd.syntax freevars in
      pp_library fd m;
      output_string fd 
        (Auxl.print_with_comment m "\n" "free variables"
  	  (pp_locs^Dependency.compute m sd.syntax funcs_freevars))

  | Struct_sbs xs ->
      (* find the relevant funcs_subrules *)
      let substitutions =
  	List.map (fun (n,ntr,ntmvr) ->
	  (* print_endline ("searching: "^n^" "^ntr^" "^(Grammar_pp.pp_plain_nt_or_mv_root ntmvr)); *)
  	  List.find
  	    (fun sb -> 
	      (* print_endline ("  found: "^sb.sb_name^" "^sb.sb_this^" "^(Grammar_pp.pp_plain_nt_or_mv_root sb.sb_that)); *)
	      String.compare sb.sb_name n = 0 
		&& String.compare sb.sb_this ntr = 0 
		&& compare sb.sb_that ntmvr = 0)
  	    xd.xd_sbs)
  	  xs in
      let s = List.flatten (List.map (function sb -> sb.sb_loc) substitutions) in
      let pp_locs = if !Global_option.output_source_locations >=2 then Grammar_pp.pp_source_location m s else "" in
      (* print them out *)
      let funcs_substitutions =
  	Substs_pp.pp_substs m sd.syntax substitutions in
      pp_library fd m;
      output_string fd
	(Auxl.print_with_comment m "\n" "substitutions"
  	  (pp_locs ^ Dependency.compute m sd.syntax funcs_substitutions))

  | Struct_crs xs ->
      (* find the relevant contextrules *)
      let contextrules =
  	List.map (fun (ntr,target,hole) ->
          List.find
  	    (fun cr -> String.compare cr.cr_ntr ntr = 0 && String.compare cr.cr_target target = 0 && String.compare cr.cr_hole hole = 0)
  	    xd.xd_crs)
  	  xs in
      let s = List.flatten (List.map (function cr -> cr.cr_loc) contextrules) in
      let pp_locs = if !Global_option.output_source_locations >=2 then Grammar_pp.pp_source_location m s else "" in
      let contexts = 
        Context_pp.pp_context m sd.syntax lookup contextrules in

      output_string fd
        (Auxl.print_with_comment m "\n" "context application"
  	  (pp_locs^Dependency.compute m xd contexts))

  | Struct_embed embed -> 
      Embed_pp.pp_embeds fd m sd.syntax lookup [embed] (* FIXME should be a list *)
   )

let pp_systemdefn_structure fd m sd xd_expanded structure_expanded lookup =
  List.iter (fun (_,x) -> pp_struct_entry fd m sd xd_expanded lookup x) structure_expanded

(* old algorithm that ignores the structure informations: core for isa/hol/coq/twf output *)
let pp_systemdefn_core fd m sd lookup = 
  let xd_expanded, structure_expanded = 
    Transform.expand_lists_in_syntaxdefn m sd.syntax sd.structure in (* identity if m <> Coq *)
  
  output_string fd (Auxl.big_line_comment m "warning: the backend selected ignores the file structure informations");
  Embed_pp.pp_embeds fd m sd.syntax lookup sd.syntax.xd_embed_preamble;
  pp_auxiliary_lemmas m xd_expanded;
  output_string fd (Auxl.big_line_comment m "syntax");
  output_string fd (Grammar_pp.pp_syntaxdefn m xd_expanded);
  output_string fd ("\n");
  pp_functions fd m sd lookup;
  Embed_pp.pp_embeds fd m sd.syntax lookup sd.syntax.xd_embed;
  output_string fd ("\n");
  Defns.pp_fun_or_reln_defnclass_list fd m sd.syntax lookup sd.relations;
  output_string fd ("\n\n");
  ( match m with
  | Coq co when not co.coq_expand_lists ->
      let ip = Coq_induct.pp_induction m xd_expanded xd_expanded.xd_rs in
      if ip <> "" then begin 
         output_string fd (Auxl.big_line_comment m "induction principles");
         output_string fd ip;
         output_string fd ("\n")
      end
  | _ -> () )

(* old algorithm, used only when pp with -merge true *)
let pp_systemdefn fd m sd lookup fn =

  match m with
  | Isa io ->
      let imports = 
        if Auxl.require_nominal sd.syntax
        then "\"/~~/src/HOL/Nominal/Nominal\"" :: sd.syntax.xd_isa_imports
        else "Main" :: "\"~~/src/HOL/Library/Multiset\"" :: sd.syntax.xd_isa_imports in
      Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
      Printf.fprintf fd "theory %s\nimports %s\n" fn (String.concat " " imports);
      output_string fd "begin\n\n";
      pp_systemdefn_core fd m sd lookup;
      output_string fd "\nend\n"
  | Hol ho ->
      Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
      Printf.fprintf fd "(* to compile: Holmake %sTheory.uo   *)\n" fn;
      output_string fd "(* for interactive use:\n";
      output_string fd "  app load [\"pred_setTheory\",\"finite_mapTheory\",\"stringTheory\",\"containerTheory\",\"ottLib\"];\n";
      output_string fd "*)\n\n";
      output_string fd "open HolKernel boolLib Parse bossLib ottLib;\n"  ;
      output_string fd "infix THEN THENC |-> ## ;\n";
      output_string fd "local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory \n";
      output_string fd "  finite_mapTheory in end;\n\n";
      Printf.fprintf fd "val _ = new_theory \"%s\";\n\n" fn; 
      pp_systemdefn_core fd m sd lookup;
      output_string fd "\nval _ = export_theory ();\n"
  | Coq co ->
      (* FZ keeping for now locally_nameless repr separated from the main *)
      if Auxl.require_locally_nameless sd.syntax
      then begin
        Printf.fprintf fd "(* generated by Ott %s, locally-nameless %sfrom: %s *)\n"
          Version.n (if Auxl.is_lngen m then "lngen " else "") sd.sources;
        List.iter (fun th -> Printf.fprintf fd "Require Import %s.\n" th) 
			( match co.coq_expand_lists with
			| true -> ["Metatheory"]
			| false -> ["Bool"; "Metatheory"; "List"; "ott_list_core"])

      end else begin
        Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
        List.iter (fun th -> Printf.fprintf fd "Require Import %s.\n" th) 
                     ( match co.coq_expand_lists with
                     | true -> ["Arith"; "Bool"; "List"]
                     | false -> ["Arith"; "Bool"; "List"; "ott_list_core"])
      end;
      pp_systemdefn_core fd m sd lookup
  | Twf wo ->
      Printf.fprintf fd "%%%% generated by Ott %s from: %s\n\n" Version.n sd.sources;
      pp_systemdefn_core fd m sd lookup
  | Caml oo ->
      Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
      pp_systemdefn_core fd m sd lookup
  | Lem lo ->
      Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
      pp_systemdefn_core fd m sd lookup
  | Ascii _ | Lex _ | Yacc _ | Tex _ -> Auxl.errorm m "pp_systemdefn"
     

(* multi-file stuff *)

let pp_systemdefn_core_io m sd lookup oi merge_fragments =
  (* if -merge true, ignore the new algorithm *)
  if merge_fragments
  then begin
    let o = match oi with (o,is)::[] -> o 
    | _ -> Auxl.error "must specify only one output file .\n" in
    let fn = Auxl.filename_check m o in
    let fd = open_out o in
    pp_systemdefn fd m sd lookup fn;
    close_out fd;
  end
  else if Auxl.require_locally_nameless sd.syntax
  (* keeping for now locally_nameless repr separated from the main *)    
  then 
    ( match oi with
    | (o,is)::[] ->
        let co = 
          match m with Coq co -> co 
          | _ -> Auxl.int_error "pp_systemdefn_core_io, locally nameless with a non-coq backend\n" in
        let fd = open_out o in
        Printf.fprintf fd "(* generated by Ott %s, locally-nameless %sfrom: %s *)\n"
          Version.n (if Auxl.is_lngen m then "lngen " else "") sd.sources;
        List.iter (fun th -> Printf.fprintf fd "Require Import %s.\n" th) 
			( match co.coq_expand_lists with
			| true -> ["Metatheory"]
			| false -> ["Bool"; "Metatheory"; "List"; "ott_list_core"]);
        pp_systemdefn_core_locally_nameless fd m sd lookup;
        close_out fd
    | _ -> Auxl.error "must specify only one output file in the Coq locally-nameless backend.\n" )

  else
    begin
      let is = snd(List.hd oi) in
      (* synthesize an embed for the standard preamble *)
      let std_preamble_embed fn =
        let file_sources = 
          if is = [] then "no input files" else String.concat " " is in
        (fn, Struct_embed 
          (dummy_loc, Auxl.hom_name_for_pp_mode m,
           match m with
           | Isa io ->
	       let imports = 
	         if Auxl.require_nominal sd.syntax
	         then "\"/~~/src/HOL/Nominal/Nominal\"" :: sd.syntax.xd_isa_imports
	         else "Main" :: "\"~~/src/HOL/Library/Multiset\"" :: sd.syntax.xd_isa_imports in
               [ Embed_string (dummy_loc,
                 "(* generated by Ott "^Version.n^" from: "^file_sources^" *)\n"
                 ^ "theory "^fn^"\n"
                 ^ "imports " ^ String.concat " " imports ^"\n"
                 ^ "begin\n")]
           | Hol ho ->
               [ Embed_string (dummy_loc,
                 "(* generated by Ott "^Version.n^" from: "^file_sources^" *)\n"
                 ^ "(* to compile: Holmake "^fn^"Theory.uo   *)\n" 
                 ^ "(* for interactive use:\n"
                 ^ "  app load [\"pred_setTheory\",\"finite_mapTheory\",\"stringTheory\",\"containerTheory\",\"ottLib\"];\n"
                 ^"*)\n\n"
                 ^ "open HolKernel boolLib Parse bossLib ottLib;\n"  
                 ^ "infix THEN THENC |-> ## ;\n"
                 ^ "local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory \n"
                 ^ "  finite_mapTheory in end;\n\n"
                 ^ "val _ = new_theory \""^fn^"\";\n\n")] 
           | Coq co ->
               [ Embed_string (dummy_loc,
	           "(* generated by Ott " ^ Version.n ^ " from: " ^ file_sources ^ " *)\n\n"
	           ^ String.concat "\n" (List.map (fun th -> "Require Import " ^ th ^ ".") 
				           ( match co.coq_expand_lists with
				           | true -> ["Arith"; "Bool"; "List"]
				           | false -> ["Arith"; "Bool"; "List"; "ott_list_core"]))
                   ^ "\n\n" )]
           | Twf wo ->
               [ Embed_string (dummy_loc,
                 "%% generated by Ott "^Version.n^" from: "^file_sources^" \n" )]
           | Caml oo ->
               [ Embed_string (dummy_loc,
                 "(* generated by Ott "^Version.n^" from: "^file_sources^" *)\n")]
           | Lem lo ->
               [ Embed_string (dummy_loc,
                 "(* generated by Ott "^Version.n^" from: "^file_sources^" *)\n"
                               ^ "open import Pervasives\n"
                              )]
            | _ -> 
               Auxl.errorm m "std_preamble_embed"
         ))
      in            

      let std_postamble_embed fn =
        match m with
        | Isa _ -> [(fn, Struct_embed (dummy_loc, "isa", [Embed_string (dummy_loc,"\nend\n")]))]
        | Hol _ -> [(fn, Struct_embed (dummy_loc, "hol", [Embed_string (dummy_loc,"\nval _ = export_theory ();\n")]))]
        | _ -> [] in

      let xd_expanded, structure_expanded = 
        Transform.expand_lists_in_syntaxdefn m sd.syntax sd.structure in (* identity if m <> Coq *)

      (* print_endline ("**** structure after expand ***\n "^( Auxl.dump_structure_fn structure_expanded)); *)
      
      (* special case if there is only one i file *)
      match oi with
      | (o,(i::[]))::[] ->
          let fn = Auxl.filename_check m o in 
          let fd = open_out o in
          pp_systemdefn_structure fd m sd xd_expanded ([std_preamble_embed fn]) lookup;
          pp_auxiliary_lemmas m xd_expanded;
          pp_systemdefn_structure fd m sd xd_expanded structure_expanded lookup;
          pp_systemdefn_structure fd m sd xd_expanded (std_postamble_embed fn) lookup;
          output_string fd "\n\n";
          close_out fd
      | _ ->
          List.iter 
            (fun (o,is) ->
              let fn = Auxl.filename_check m o in
              let struct_subset = 
                List.filter (fun (fn,s) -> List.mem fn is) structure_expanded in
              let fd = open_out o in
              pp_systemdefn_structure fd m sd xd_expanded ([std_preamble_embed fn]) lookup;
              pp_auxiliary_lemmas m xd_expanded;
              pp_systemdefn_structure fd m sd xd_expanded struct_subset lookup;
              pp_systemdefn_structure fd m sd xd_expanded (std_postamble_embed fn) lookup;
              output_string fd "\n\n";
              close_out fd)
            oi
    end

let is_wrap_pre (l,hn,es) = if hn = "tex-wrap-pre" then Some (l,"tex",es) else None
let is_wrap_post (l,hn,es) = if hn = "tex-wrap-post" then Some (l,"tex",es) else None

let pp_systemdefn_core_tex m sd lookup oi =
  let xo = match m with | Tex xo -> xo | _ -> Auxl.error "internal: pp_systemdefn_core_tex on non-tex pp_mode\n" in
  match oi with
  | (o,is)::[] ->
      let fd = open_out o in
      Printf.fprintf fd ("%% generated by Ott %s from: %s\n") Version.n sd.sources;
      if xo.ppt_wrap then begin
	match Auxl.option_map is_wrap_pre sd.syntax.xd_embed_preamble with
        | [] ->
            output_string fd "\\documentclass[11pt]{article}\n\\usepackage{amsmath,amssymb}\n\\usepackage{supertabular}\n";
            output_string fd "\\usepackage{geometry}\n\\usepackage{ifthen}\n\\usepackage{alltt}%hack\n";
            output_string fd "\\geometry{a4paper,dvips,twoside,left=22.5mm,right=22.5mm,top=20mm,bottom=30mm}\n";
            (if xo.ppt_colour then output_string fd "\\usepackage{color}\n")
        | pre_wrap -> Embed_pp.pp_embeds fd m sd.syntax lookup pre_wrap
      end;
      Printf.fprintf fd ("\\newcommand{%s}[4][]{{\\displaystyle\\frac{\\begin{array}{l}#2\\end{array}}{#3}\\quad%s{#4}}}\n")
        (Grammar_pp.pp_tex_DRULE_NAME m) (Grammar_pp.pp_tex_DRULE_NAME_NAME m);
      Printf.fprintf fd ("\\newcommand{%s}[1]{\\[#1\\]}\n") (Grammar_pp.pp_tex_USE_DRULE_NAME m);
      Printf.fprintf fd ("\\newcommand{%s}[1]{ #1 \\\\}\n") (Grammar_pp.pp_tex_PREMISE_NAME m );
      Printf.fprintf fd ("\\newenvironment{%s}[3][]{ \\framebox{\\mbox{#2}} \\quad #3 \\\\[0pt]}{}\n") (Grammar_pp.pp_tex_DEFN_BLOCK_NAME m );
      Printf.fprintf fd ("\\newenvironment{%s}[3][]{ \\framebox{\\mbox{#2}} \\quad #3 \\\\[0pt]\\begin{displaymath}\\begin{array}{l}}{\\end{array}\\end{displaymath}}\n")
        (Grammar_pp.pp_tex_FUNDEFN_BLOCK_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[2]{ #1 \\equiv #2 \\\\}\n") (Grammar_pp.pp_tex_FUNCLAUSE_NAME m);
      Printf.fprintf fd ("\\newcommand{%s}[1]{\\mathit{#1}}\n") (Grammar_pp.pp_tex_NT_NAME m);
      Printf.fprintf fd ("\\newcommand{%s}[1]{\\mathit{#1}}\n") (Grammar_pp.pp_tex_MV_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[1]{\\mathbf{#1}}\n") (Grammar_pp.pp_tex_KW_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[1]{#1}\n") (Grammar_pp.pp_tex_SYM_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[1]{\\text{#1}}\n") (Grammar_pp.pp_tex_COM_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[1]{\\textsc{#1}}\n") (Grammar_pp.pp_tex_DRULE_NAME_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[5]{\\overline{#1}^{\\,#2\\in #3 #4 #5}}\n") (Grammar_pp.pp_tex_COMP_LU_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[3]{\\overline{#1}^{\\,#2<#3}}\n") (Grammar_pp.pp_tex_COMP_U_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[2]{\\overline{#1}^{\\,#2}}\n") (Grammar_pp.pp_tex_COMP_NAME m );
      Printf.fprintf fd ("\\newcommand{\\%sgrammartabular}[1]{\\begin{supertabular}{llcllllll}#1\\end{supertabular}}\n")
        (Grammar_pp.pp_tex_NAME_PREFIX m);
      Printf.fprintf fd ("\\newcommand{\\%smetavartabular}[1]{\\begin{supertabular}{ll}#1\\end{supertabular}}\n")
        (Grammar_pp.pp_tex_NAME_PREFIX m);

      (* {prod_flavour}{prodnames}{meta}{bindspec}{othercategories}{com} *)
      Printf.fprintf fd ("\\newcommand{%s}[3]{$#1$ & & $#2$ & & & \\multicolumn{2}{l}{#3}}\n") (Grammar_pp.pp_tex_RULEHEAD_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[6]{& & $#1$ & $#2$ & $#3 #4$ & $#5$ & $#6$}\n") (Grammar_pp.pp_tex_PROD_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[6]{%s{#1}{#2}{#3}{#4}{#5}{#6}}\n")
        (Grammar_pp.pp_tex_FIRST_PROD_NAME m ) (Grammar_pp.pp_tex_PROD_NAME m);
      Printf.fprintf fd ("\\newcommand{%s}[2]{& & $#1$ & \\multicolumn{4}{l}{$#2$}}\n") (Grammar_pp.pp_tex_LONG_PROD_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}[2]{%s{#1}{#2}}\n")
        (Grammar_pp.pp_tex_FIRST_LONG_PROD_NAME m ) (Grammar_pp.pp_tex_LONG_PROD_NAME m);
      Printf.fprintf fd ("\\newcommand{%s}[6]{%s{#1}{#2}{#3}{#4}{#5}{#6}}\n")
        (Grammar_pp.pp_tex_BINDSPEC_PROD_NAME m ) (Grammar_pp.pp_tex_PROD_NAME m);
      Printf.fprintf fd ("\\newcommand{%s}{\\\\}\n") (Grammar_pp.pp_tex_PROD_NEWLINE_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}{\\\\[5.0mm]}\n") (Grammar_pp.pp_tex_INTERRULE_NAME m );
      Printf.fprintf fd ("\\newcommand{%s}{\\\\}\n") (Grammar_pp.pp_tex_AFTERLASTRULE_NAME m );
      Embed_pp.pp_embeds fd m sd.syntax lookup sd.syntax.xd_embed_preamble;
      output_string fd (Grammar_pp.pp_syntaxdefn m sd.syntax);
      Defns.pp_fun_or_reln_defnclass_list fd m sd.syntax lookup sd.relations;
      Printf.fprintf fd ("\\newcommand{%s}{%s\\\\[0pt]\n%s\\\\[5.0mm]\n")
        (Grammar_pp.pp_tex_ALL_NAME m)
        (Grammar_pp.pp_tex_METAVARS_NAME m)
        (Grammar_pp.pp_tex_RULES_NAME m);
      Embed_pp.pp_embeds fd m sd.syntax lookup sd.syntax.xd_embed;
      Printf.fprintf fd "%s}\n\n"
          (Grammar_pp.pp_tex_DEFNSS_NAME m);
      if xo.ppt_wrap then begin
        match Auxl.option_map is_wrap_post sd.syntax.xd_embed_preamble with
        | [] ->
            Printf.fprintf fd 
              ("\\begin{document}\n%s\n\n\\begin{verbatim}\n%s\\end{verbatim}\n\\end{document}\n")
              (Grammar_pp.pp_tex_ALL_NAME m)
              (snd (Defns.pp_counts sd))
        | post_wrap -> Embed_pp.pp_embeds fd m sd.syntax lookup post_wrap
      end;
      close_out fd;
              
  | _ -> Auxl.error "must specify only one output file in the TeX backend.\n"

