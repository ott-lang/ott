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

(* command-line options *)
let colour = ref true
let file_arguments = ref ([]:(file_argument*string) list)
let i_arguments = ref false
let dot_filename_opt = ref (None : string option)
let alltt_filename_opt = ref (None : string option)
let write_systemdefn_filename_opt = ref (None : string option)
let read_systemdefn_filename_opt = ref (None : string option)
let tex_name_prefix = ref "ott"
let tex_filter_filenames = ref ([] : (string * string) list)
let tex_filter_filename_srcs = ref ([] : string list)
let tex_filter_filename_dsts = ref ([] :  string list)
let isa_filter_filenames = ref ([] : (string * string) list)
let isa_filter_filename_srcs = ref ([] : string list)
let isa_filter_filename_dsts = ref ([] :  string list)
let hol_filter_filenames = ref ([] : (string * string) list)
let hol_filter_filename_srcs = ref ([] : string list)
let hol_filter_filename_dsts = ref ([] :  string list)
let lem_filter_filenames = ref ([] : (string * string) list)
let lem_filter_filename_srcs = ref ([] : string list)
let lem_filter_filename_dsts = ref ([] :  string list)
let coq_filter_filenames = ref ([] : (string * string) list)
let coq_filter_filename_srcs = ref ([] : string list)
let coq_filter_filename_dsts = ref ([] :  string list)
let twf_filter_filenames = ref ([] : (string * string) list)
let twf_filter_filename_srcs = ref ([] : string list)
let twf_filter_filename_dsts = ref ([] :  string list)
let caml_filter_filenames = ref ([] : (string * string) list)
let caml_filter_filename_srcs = ref ([] : string list)
let caml_filter_filename_dsts = ref ([] :  string list)
let lift_cons_prefixes = ref false
let test_parse_list = ref ([] : string list)
let sort = ref true
let generate_aux_rules = ref true
let showraw = ref false
let tex_show_meta = ref true
let tex_show_categories = ref false
let tex_colour = ref true
let tex_wrap = ref true
let process_defns = ref true
let signal_parse_errors = ref false
let ascii_ugly = ref false
let show_sort = ref false
let show_deps = ref false
let show_defns = ref false
let isa_syntax = ref false
let isa_primrec = ref true 
let isa_inductive = ref true
let isa_generate_lemmas = ref true
let coq_avoid = ref 1
let coq_expand_lists = ref true
let coq_lngen = ref false
let coq_names_in_rules = ref true
let coq_use_filter_fn = ref false
let merge_fragments = ref false
let picky_multiple_parses = ref false
let caml_include_terminals = ref false

let options = Arg.align [

(* main output stages *)
  ( "-i", 
    Arg.String (fun s -> i_arguments := true; file_arguments := (In,s) ::(!file_arguments)),
    "<filename>        Input file (can be used multiple times)" );
  ( "-o", 
    Arg.String (fun s -> file_arguments := (Out,s) ::(!file_arguments)),
    "<filename>        Output file (can be used multiple times)" );
  ( "-writesys", 
    Arg.String (fun s -> 
      match !write_systemdefn_filename_opt with
      | None -> write_systemdefn_filename_opt  := Some s
      | Some _ -> Auxl.error "\nError: multiple -writesys <filename> not suppported\n"),
    "<filename>        Output system definition" ); 
  ( "-readsys", 
    Arg.String (fun s -> 
      match !read_systemdefn_filename_opt with
      | None -> read_systemdefn_filename_opt  := Some s
      | Some _ -> Auxl.error "\nError: multiple -readsys <filename> not suppported\n"),
    "<filename>        Input system definition" ); 

(* filter filenames *)
  ( "-tex_filter", 
    Arg.Tuple[Arg.String (fun s -> tex_filter_filename_srcs := s :: !tex_filter_filename_srcs);
              Arg.String (fun s -> tex_filter_filename_dsts := s :: !tex_filter_filename_dsts)],
    "<src><dst>  Files to TeX filter" ); 
  ( "-coq_filter", 
    Arg.Tuple[Arg.String (fun s -> coq_filter_filename_srcs := s :: !coq_filter_filename_srcs);
              Arg.String (fun s -> coq_filter_filename_dsts := s :: !coq_filter_filename_dsts)],
    "<src><dst>  Files to Coq filter" ); 
  ( "-hol_filter", 
    Arg.Tuple[Arg.String (fun s -> hol_filter_filename_srcs := s :: !hol_filter_filename_srcs);
              Arg.String (fun s -> hol_filter_filename_dsts := s :: !hol_filter_filename_dsts)],
    "<src><dst>  Files to HOL filter" ); 
  ( "-lem_filter", 
    Arg.Tuple[Arg.String (fun s -> lem_filter_filename_srcs := s :: !lem_filter_filename_srcs);
              Arg.String (fun s -> lem_filter_filename_dsts := s :: !lem_filter_filename_dsts)],
    "<src><dst>  Files to HOL filter" ); 
  ( "-isa_filter", 
    Arg.Tuple[Arg.String (fun s -> isa_filter_filename_srcs := s :: !isa_filter_filename_srcs);
              Arg.String (fun s -> isa_filter_filename_dsts := s :: !isa_filter_filename_dsts)],
    "<src><dst>  Files to Isabelle filter" ); 
(*   ( "-twelf_filter",  *)
(*     Arg.Tuple[Arg.String (fun s -> twf_filter_filename_srcs := s :: !twf_filter_filename_srcs); *)
(*               Arg.String (fun s -> twf_filter_filename_dsts := s :: !twf_filter_filename_dsts)], *)
(*     "<src><dst>  Files to Twelf filter" );  *)
  ( "-ocaml_filter", 
    Arg.Tuple[Arg.String (fun s -> caml_filter_filename_srcs := s :: !caml_filter_filename_srcs);
              Arg.String (fun s -> caml_filter_filename_dsts := s :: !caml_filter_filename_dsts)],
    "<src><dst>  Files to OCaml filter" ); 
  ( "-merge", 
    Arg.Bool (fun b -> merge_fragments := b), 
    "<"^string_of_bool !merge_fragments ^">         merge grammar and definition rules" ); 

  ( "-parse", 
    Arg.String (fun s -> test_parse_list := !test_parse_list @ [s]),
    "<string>        Test parse symterm,eg \":nontermroot: term\"" ); 

(* general behaviour *)
  ( "-fast_parse",
    Arg.Bool (fun b -> New_term_parser.fast_parse := b),
    "<"^string_of_bool !New_term_parser.fast_parse^">  do not parse :rulename: pseudoterminals" );
  ( "-signal_parse_errors",
    Arg.Bool (fun b -> signal_parse_errors := b),
    "<"^string_of_bool !signal_parse_errors^">  return >0 if there are bad defns" );
  ( "-picky_multiple_parses",
    Arg.Bool (fun b -> picky_multiple_parses := b),
    "<"^string_of_bool !picky_multiple_parses^">  Picky about multiple parses" );
  ( "-generate_aux_rules",
    Arg.Bool (fun b -> generate_aux_rules := b),
    "<"^string_of_bool !generate_aux_rules^">  Generate auxiliary rules from {{ aux ... }} homs" );
  ( "-output_source_locations",
    Arg.Int (fun i -> Global_option.output_source_locations := i),
    "<"^string_of_int !Global_option.output_source_locations^">  Include source location info in output (0=none, 1=drules, 2=grammar+drules)" );

(* options for ascii output *)
  ( "-colour", 
    Arg.Bool (fun b -> colour := b), 
    "<"^string_of_bool !colour ^">         Use (vt220) colour for ASCII pretty print" ); 
  ( "-show_sort", 
    Arg.Bool (fun b -> show_sort := b), 
    "<"^string_of_bool !show_sort ^"> Show ASCII pretty print of syntax" ); 
  ( "-show_defns", 
    Arg.Bool (fun b -> show_defns := b), 
    "<"^string_of_bool !show_defns ^">     Show ASCII pretty print defns" ); 
(* this doesn't seem to work anymore *)
(*   ( "-lift_cons_prefixes",  *)
(*     Arg.Bool (fun b -> lift_cons_prefixes := b), *)
(*     "<"^string_of_bool !lift_cons_prefixes^"> Lift constructor prefixes back to rules in ASCII pretty prints" );  *)

(* options for tex output *)
  ( "-tex_show_meta", 
    Arg.Bool (fun b -> tex_show_meta := b),
    "<"^string_of_bool !tex_show_meta^">  Include meta prods and rules in TeX output" ); 
  ( "-tex_show_categories", 
    Arg.Bool (fun b -> tex_show_categories := b),
    "<"^string_of_bool !tex_show_categories^">  Signal production flags in TeX output" ); 
  ( "-tex_colour", 
    Arg.Bool (fun b -> tex_colour := b),
    "<"^string_of_bool !tex_colour^">     Colour parse errors in TeX output" ); 
  ( "-tex_wrap", 
    Arg.Bool (fun b -> tex_wrap := b),
    "<"^string_of_bool !tex_wrap ^">       Wrap TeX output in document pre/postamble" ); 
  ( "-tex_name_prefix", 
    Arg.String (fun s -> tex_name_prefix := s),
    "<string>  Prefix for tex commands (default \""^ !tex_name_prefix^"\")" );

(* options for isa output *)
  ( "-isabelle_primrec",
    Arg.Bool (fun b -> isa_primrec := b),
    "<"^string_of_bool !isa_primrec ^">       Use \"primrec\" instead of \"fun\"\n                                       for functions" );
  ( "-isabelle_inductive",
    Arg.Bool (fun b -> isa_inductive := b),
    "<"^string_of_bool !isa_inductive ^">       Use \"inductive\" instead of \"inductive_set\"\n                                       for relations" );
  ( "-isa_syntax", 
    Arg.Bool (fun b -> isa_syntax := b),
    "<"^string_of_bool !isa_syntax ^">       Use fancy syntax in Isabelle output" ); 
  ( "-isa_generate_lemmas", 
    Arg.Bool (fun b -> isa_generate_lemmas := b),
    "<"^string_of_bool !isa_syntax ^">       Lemmas for collapsed functions in Isabelle" ); 

(* options for coq output *)
  ( "-coq_avoid", 
    Arg.Int (fun i -> coq_avoid := i),
    "<"^string_of_int !coq_avoid^">          coq type-name avoidance\n                                       (0=nothing, 1=avoid, 2=secondaryify)" ); 
  ( "-coq_expand_list_types", 
    Arg.Bool (fun b -> coq_expand_lists := b),
    "<"^string_of_bool !coq_expand_lists^">  Expand list types in Coq output" ); 
  ( "-coq_lngen", 
    Arg.Bool (fun b -> coq_lngen := b),
    "<"^string_of_bool !coq_lngen^">  lngen compatibility" ); 
  ( "-coq_names_in_rules", 
    Arg.Bool (fun b -> coq_names_in_rules := b),
    "<"^string_of_bool !coq_names_in_rules^">  Copy user names in rule definitions" ); 
  ( "-coq_use_filter_fn", 
    Arg.Bool (fun b -> coq_use_filter_fn := b),
    "<"^string_of_bool !coq_use_filter_fn^">  Use list_filter instead of list_minus2 in substitutions" ); 
(* options for OCaml output *)
  ( "-ocaml_include_terminals",
    Arg.Bool (fun b -> caml_include_terminals := b),
    "<"^string_of_bool !caml_include_terminals^">  Include terminals in OCaml output (experimental!)" );

(* options for debugging *)
  ( "-pp_grammar", 
    Arg.Set Global_option.do_pp_grammar,
    "        (debug) print term grammar" ); 
  ( "-dot", 
    Arg.String (fun s -> dot_filename_opt := Some s),
    "<filename>        (debug) dot graph of syntax dependencies" ); 
  ( "-alltt", 
    Arg.String (fun s -> alltt_filename_opt := Some s),
    "<filename>        (debug) alltt output of single source file" ); 
  ( "-sort", 
    Arg.Bool (fun b -> sort := b),
    "<"^string_of_bool !sort^">           (debug) do topological sort" ); 
  ( "-process_defns", 
    Arg.Bool (fun b -> process_defns := b),
    "<"^string_of_bool !process_defns^">  (debug) process inductive reln definitions" ); 
  ( "-showraw", 
    Arg.Bool (fun b -> showraw := b),
    "<"^string_of_bool !showraw ^">       (debug) show raw grammar"); 
  ( "-ugly", 
    Arg.Bool (fun b -> ascii_ugly := b),
    "<"^string_of_bool !ascii_ugly^">          (debug) use ugly ASCII output" ); 
  ( "-no_rbcatn", 
    Arg.Bool (fun b -> Substs_pp.no_rbcatn := b),
    "<"^string_of_bool !Substs_pp.no_rbcatn^">      (debug) remove relevant bind clauses" ); 
  ( "-lem_debug", 
    Arg.Bool (fun b -> Types.lem_debug := b),
    "        (debug) print lem debug locations" ); 
] 

let usage_msg = 
    ("\n"
     ^ "usage: ott <options> <filename1> .. <filenamen> \n" 
     ^ "  (use \"OCAMLRUNPARAM=p  ott ...\" to show the ocamlyacc trace)\n"
     ^ "  (ott <options> <filename1> .. <filenamen>    is equivalent to\n   ott -i <filename1> .. -i <filenamen> <options>)\n")



let _ = print_string ("Ott version "^Version.n^"   distribution of "^Version.d^"\n")

let _ = 
  let extra_arguments = ref [] in
  Arg.parse options 
    (fun s -> 
      if !i_arguments 
      then Auxl.error "\nError: must either use -i <filename> or specify filenames at the end\n"
      else extra_arguments := (In,s) ::(!extra_arguments))
    usage_msg;
  file_arguments :=  !file_arguments @ !extra_arguments 

let _ = tex_filter_filenames := List.combine (!tex_filter_filename_srcs) (!tex_filter_filename_dsts)
let _ = hol_filter_filenames := List.combine (!hol_filter_filename_srcs) (!hol_filter_filename_dsts)
let _ = lem_filter_filenames := List.combine (!lem_filter_filename_srcs) (!lem_filter_filename_dsts)
let _ = isa_filter_filenames := List.combine (!isa_filter_filename_srcs) (!isa_filter_filename_dsts)
let _ = coq_filter_filenames := List.combine (!coq_filter_filename_srcs) (!coq_filter_filename_dsts)
let _ = twf_filter_filenames := List.combine (!twf_filter_filename_srcs) (!twf_filter_filename_dsts)
let _ = caml_filter_filenames := List.combine (!caml_filter_filename_srcs) (!caml_filter_filename_dsts)

let types_of_extensions =
    [ "ott","ott";
      "tex","tex"; 
      "v",  "coq"; 
      "thy","isa"; 
      "sml","hol"; 
      "lem","lem"; 
      "twf","twf"; 
      "ml", "ocaml";
      "mll", "lex"; 
      "mly", "yacc"] 

let extension_of_type t = List.assoc t (List.map (function (a,b)->(b,a)) types_of_extensions)

let file_type name = 
  try
    Some 
      (List.assoc 
         (let start = 1+String.length (Filename.chop_extension name) in
         String.sub name start (String.length name - start) )
         types_of_extensions)
  with
    _ -> None 

let non_tex_output_types = ["coq"; "isa"; "hol"; "lem"; "twf"; "ocaml"]
let output_types =  "tex" :: "lex" :: "yacc" :: non_tex_output_types
let input_types = "ott" :: output_types

let classify_file_argument arg =
  match arg with
  | (In,name) -> 
      (match file_type name with
      | Some e when (List.mem e input_types) -> 
          (In,e,name)
      | _ -> Auxl.error 
            ("\nError: unrecognised extension of input file \""^name
             ^ "\" (must be one of " ^ String.concat "," (List.map extension_of_type input_types) ^")\n"))
  | (Out,name) -> 
      (match file_type name with
      | Some e when (List.mem e output_types) -> 
          (Out,e,name)
      | _ -> Auxl.error 
            ("\nError: unrecognised extension of output file \""^name
             ^ "\" (must be one of "^String.concat "," (List.map extension_of_type output_types) ^")\n"))

(*   all_file_arguments collects together a list of                          *)
(*                                                                           *)
(*      (In,filetype,filename)                                               *)
(*      (Out,filetype,filename)                                              *) 
(*                                                                           *)                  
(*   values, containing first all the ott source files from the end of       *)
(*   the command line, if any, then all the explicit -in and -out arguments, *)
(*   and finally any -tex/-coq/-hol/-isabelle/-lem/-ocaml arguments               *)

let all_file_arguments = 
  List.map classify_file_argument (List.rev (!file_arguments))

(* collect the proof assistant targets *)
let targets_in ts = 
  List.filter 
    (function t -> List.mem t ts) 
    (Auxl.remove_duplicates 
       (Auxl.option_map 
          (function x -> 
            match x with 
            | (Out,t,_) -> Some t 
            | _ -> None) 
          all_file_arguments))

let targets_non_tex = targets_in non_tex_output_types
let targets = targets_in output_types
let targets_for_non_picky = targets_in [(*"lex";"ocaml";*)"hol";"lem";"isa";"twf";"coq";"tex"]

(* collect the source filenames *)
let source_filenames = 
  Auxl.option_map 
    (function x -> match x with
    | In,t,n -> Some (t,n)
    | Out,_,_ -> None) 
    all_file_arguments

let _ = if false then print_string ("source_filenames =   "^String.concat ", " (List.map (function (t,n) -> n^":"^t) source_filenames)^"\n")

(* pp modes, used both for main output and for filtered files *)
let m_ascii = Ascii { ppa_colour = !colour; 
		      ppa_lift_cons_prefixes = false; 
		      ppa_ugly= !ascii_ugly; 
		      ppa_show_deps = !show_deps; 
		      ppa_show_defns = !show_defns } 
let m_tex = Tex {ppt_colour= !tex_colour;
                 ppt_show_meta= !tex_show_meta;
                 ppt_show_categories= !tex_show_categories;
                 ppt_wrap= !tex_wrap;
                 ppt_name_prefix= !tex_name_prefix } 
let m_isa = Isa { ppi_isa_primrec = !isa_primrec;
		  ppi_isa_inductive = !isa_inductive;
                  isa_library = ref ("",[]); 
		  ppi_fancy_syntax = !isa_syntax;
		  ppi_generate_lemmas = !isa_generate_lemmas }  
let m_hol = Hol { hol_library = ref ("",[]); }
let m_lem = Lem { lem_library = ref ("",[]); }
let m_twf = Twf { twf_current_defn = ref "";
		  twf_library = ref ("",[]) }
let m_coq = Coq { coq_expand_lists = !coq_expand_lists;
		  coq_quantified_vars_from_de = ref [];
		  coq_non_local_hyp_defn = ref "";
		  coq_non_local_hyp_defn_vars = ref [];
                  coq_list_types = ref [];
                  coq_list_aux_funcs = Some (ref "");
                  coq_list_aux_defns = { defined = ref []; newly_defined = ref [] };
                  coq_library = ref ("",[]);
		  coq_locally_nameless = ref false;
                  coq_lngen = !coq_lngen;
                  coq_use_filter_fn = !coq_use_filter_fn;
                  coq_names_in_rules = !coq_names_in_rules }  
let reset_m_coq m = 
  match m with
  | Coq co ->
      co.coq_non_local_hyp_defn := "";
      co.coq_non_local_hyp_defn_vars := [];
      co.coq_list_types := [];
      Auxl.the (co.coq_list_aux_funcs) := "";
      co.coq_list_aux_defns.defined := [];
      co.coq_list_aux_defns.newly_defined := [];
      co.coq_library := ("",[]);
      co.coq_locally_nameless := false
  | _ ->
      Auxl.errorm m "reset_m_coq"  

let m_caml = Caml { ppo_include_terminals = !caml_include_terminals; caml_library = ref ("",[]) } 
let m_lex = Lex ()
let m_yacc = Yacc ()
(* finally compute the set of modes used in this run of Ott -- used
   when non-picky about multiple parses *)
(* here we used also to record the suffix-stripped filenames for hol
   and isa, for the non-picky checking, but now we feed dummy filenames
   into the m_... functions *)

   let _ =
  Global_option.is_picky := 
    ( !picky_multiple_parses,
      List.map 
        (function t -> List.assoc t
            [(* "ocaml",m_caml; *)
             "hol",m_hol;
             "lem",m_lem;
             "isa",m_isa;
             "twf",m_twf;
             "coq",m_coq ;
             "tex",m_tex ]) 
        targets_for_non_picky)

(* process *)
   
let process source_filenames = 
  let sources = String.concat " " (List.map snd source_filenames) in

  (match !alltt_filename_opt,source_filenames with
  | None,_ -> ()
  | Some alltt_filename,([] | _::_::_) -> 
      Auxl.error ("\nUsage: -alltt option can only be used with exactly one source file at a time\n");
  | Some alltt_filename,[(source_filetype,source_filename)] ->
      let c = open_in source_filename in
      let c' = open_out alltt_filename in
      output_string c' "\\begin{alltt}\n";
      let lexbuf = Lexing.from_channel c in
      let lexer = Grammar_lexer.my_lexer false Grammar_lexer.metalang in 
      let rec process_input () = 
        try
          let t = 
            lexer lexbuf in
          match t with 
          | Grammar_parser.EOF -> ()
          | _ -> 
              print_string (Grammar_lexer.de_lex_ascii t); flush stdout;
              output_string c' (Grammar_lexer.de_lex_tex t); flush c';
              process_input ()
        with 
          My_parse_error s->
         (*  Auxl.error ("\n"^s^" in file: "^filter_filename^"\n") in*)
            Auxl.error ("\n"^s^"\n") in
      process_input ();
      output_string c' "\\end{alltt}\n";
      let _ = close_in c in
      let _ = close_out c' in ());      

  let parse_file (filetype,filename) = 
    match filetype with
    | "ott" -> 
        let c = open_in filename in
        let lexbuf = Lexing.from_channel c in
        (*if List.length source_filenames <> 1 then *)
        lexbuf.Lexing.lex_curr_p <- 
          { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
        let ris = 
          (try
            Grammar_parser.main (Grammar_lexer.my_lexer true Grammar_lexer.metalang) lexbuf
          with 
            My_parse_error s->
(*      Auxl.error ("\n"^s^" in file: "^filter_filename^"\n") in*)
              Auxl.error ("\n"^s^"\n")) in
        let _ = close_in c in
        ris
    | _ -> 
        let s = Auxl.string_of_filename filename in
        let loc = Location.loc_of_filename filename (String.length s) in
        [Raw_item_embed [ (loc,filetype, [Embed_string(loc,s)])]]  in

  let document = List.map parse_file source_filenames in

  if !showraw then (
    let s = 
      (String.concat "\n" 
         (List.map 
            (fun document_part -> 
              String.concat "" (List.map Grammar_pp.pp_raw_item document_part))
          document)) in
(*     let fd = open_out "test2.txt" in  *)
(*     output_string fd s ;  *)
(*     close_out fd; *)
    print_string s);

  let xd,structure,rdcs = try
    Grammar_typecheck.check_and_disambiguate !generate_aux_rules targets_non_tex (List.map snd source_filenames) (!merge_fragments) document 
  with
  | Grammar_typecheck.Typecheck_error (s1,s2) ->
      Auxl.error ("(in checking and disambiguating syntax)\n"^s1
              ^ (if s2<>"" then " ("^s2^")" else "")
              ^ "\n")
  in

  if !show_sort then (
    print_endline "********** AFTER CHECK, DISAMBIGUATE AND SORT  *********************\n"; 
    print_endline (Grammar_pp.pp_syntaxdefn m_ascii xd));

  (* FZ sorting is now performed while checking and disambiguate *)
  (* let xd =  *)
  (*   try *)
  (*     Grammar_typecheck.sort_syntaxdefn xd structure targets  *)
  (*   with *)
  (*   | Grammar_typecheck.Typecheck_error (s,_)-> Auxl.error ("\nError sorting the grammar:\n"^s^"\n") *)
  (* in *)
  (* if !show_post_sort then ( *)
  (*   print_endline "********** AFTER SORTING  *********************\n";  *)
  (*   print_endline (Grammar_pp.pp_syntaxdefn m_ascii xd)); *)

  (* make parser for symbolic terms *)

  let lookup = Term_parser.make_parser xd in 
  
  begin try
    Grammar_typecheck.check_with_parser lookup xd
  with
  | Grammar_typecheck.Typecheck_error (s1,s2) ->
      Auxl.error ("(in checking syntax)\n"^s1
              ^ (if s2<>"" then " ("^s2^")\n" else "\n"))
  end;


  let sd = 
    if !process_defns then 
      (if !show_defns then (print_endline "********** PROCESSING DEFINITIONS *****************\n"; flush stdout);
       try
         let dcs = Defns.process_raw_defnclasss m_ascii xd lookup rdcs in
         let sd = { syntax = xd;
                    relations = dcs;
		    structure = structure;
                    sources = sources} in
         sd
       with
       | Bounds.Bounds s | Defns.Rule_parse_error s | Grammar_typecheck.Typecheck_error (s,_)->
           Auxl.error ("\nError in processing definitions:\n"^s^"\n")
      )
    else
      (print_endline "********** NOT PROCESSING DEFINITIONS *************\n"; flush stdout;
       let sd = { syntax = xd;
                  relations = [];
		  structure = structure;
                  sources = sources} in
       sd) in
  sd,lookup

let read_systemdefn read_systemdefn_filename =
  let fd = open_in_bin read_systemdefn_filename in
  let sd,lookup = 
    try Marshal.from_channel fd 
    with Failure s -> Auxl.error ("Cannot read dumped systemdefn\n   " ^ s ^"\n")
  in
  close_in fd;
  sd,lookup
  
let output_stage (sd,lookup) = 
  
  (** output of systemdefn *)
  ( match !write_systemdefn_filename_opt with
  | None -> ()
  | Some s ->
      let fd = open_out_bin s in
      Marshal.to_channel fd (sd,lookup) [Marshal.Closures];
      close_out fd;
      print_string ("system definition in file: " ^ s ^ "\n") );
  
  (** dot output of dependencies *)
  ( match !dot_filename_opt with
  | None -> ()
  | Some s ->
      let fd = open_out s in
      output_string fd
        (Grammar_pp.pp_dot_dep_graph pp_ascii_opts_default sd.syntax);
      close_out fd;
      print_string ("dot version in file: " ^ s ^ "\n") );

  (* for each target, compute the o/is informations *)
  let output_details =
    (* for each -o target *)
    (* collect the output file names, and for each output file name, collect the -i it depends on *)
    let sources_per_target =
      List.map
        (fun t ->
          (t, 
           Auxl.option_map 
             (fun (d,ft,fn) -> match d with 
             | In -> Some (d,ft,fn) 
             | Out -> if String.compare ft t = 0 then Some (d,ft,fn) else None)
             all_file_arguments))
        targets in
    
    let rec compute_output ib a =
      match a with
      | [] -> []
      | (In,ft,fn)::xs -> compute_output (fn::ib) xs
      | (Out,ft,fn)::xs -> (
          if ib = [] then Auxl.warning ("warning: no input files for the output file: "^fn^".\n");
          (fn,ib)::(compute_output [] xs))
    in
    List.map (fun (t,fs) -> t, compute_output [] fs) sources_per_target 
  in

  (** target outputs *)
  List.iter 
    (fun (t,fi) -> 
      
      match t with
      | "tex" -> 
          System_pp.pp_systemdefn_core_tex m_tex sd lookup fi
      | "coq" -> 
          let sd = 
            ( match !coq_avoid with
            | 0 -> sd
            | 1 -> Auxl.avoid_primaries_systemdefn false sd
            | 2 -> Auxl.avoid_primaries_systemdefn true sd
            | _ -> Auxl.error "coq type-name avoidance must be in {0,1,2}" ) in
          System_pp.pp_systemdefn_core_io m_coq sd lookup fi !merge_fragments
      | "isa" ->
          System_pp.pp_systemdefn_core_io m_isa sd lookup fi !merge_fragments
      | "hol" ->
          System_pp.pp_systemdefn_core_io m_hol sd lookup fi !merge_fragments
      | "lem" ->
          System_pp.pp_systemdefn_core_io m_lem sd lookup fi !merge_fragments
      | "twf" -> 
          System_pp.pp_systemdefn_core_io m_twf sd lookup fi !merge_fragments
      | "ocaml" -> 
          System_pp.pp_systemdefn_core_io m_caml (Auxl.caml_rename sd) lookup fi !merge_fragments
      | "lex" -> 
          Lexyac_pp.pp_lex_systemdefn m_lex (Auxl.caml_rename sd) fi
      | "yacc" -> 
          Lexyac_pp.pp_yacc_systemdefn m_yacc (Auxl.caml_rename sd) fi
      | _ -> Auxl.int_error("unknown target "^t))


    output_details;

  (** command-line test parse *)
  (match !test_parse_list with [] -> ()|_ -> print_string "\n");
  (List.iter (function s ->
    print_string ("test parse: string \""^s^"\"\n");
    let r = Str.regexp (Str.quote ":" ^ "\\(" ^ Term_parser.ident_string ^"\\)"^ Str.quote ":" ^ "\\(.*\\)") in
    if (Str.string_match r s 0  &&
        Str.match_end () = String.length s) then
      let ntr = Str.matched_group 1 s in
      let term = Str.matched_group 4 s in
      let (ntr, concrete) = 
        if Str.string_match (Str.regexp "concrete_") ntr 0 then
          (Str.string_after ntr 9, true)
        else
          (ntr, false)
      in
      print_string ("test parse:         "^ntr^" \""^term^"\"\n");
      Term_parser.test_parse m_ascii sd.syntax ntr concrete term;
      print_string "\n"
    else
      print_string ("test parse: string "^s
                    ^" not of the required :ntr:term form\n"))
     !test_parse_list);

  (** filtering other files *)
  let filter m (src_filename,dst_filename) = 
    let fd_src = open_in src_filename in
    let fd_dst = open_out dst_filename in
    let lexbuf = Lexing.from_channel fd_src in
    lexbuf.Lexing.lex_curr_p <- 
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = src_filename};
    let unfiltered_document = try
      Grammar_parser.unfiltered_spec_el_list (Grammar_lexer.my_lexer true Grammar_lexer.filter) lexbuf
    with 
    | Parsing.Parse_error ->
        Auxl.error ("unfiltered document "^src_filename^" cannot be parsed\n") 
    | My_parse_error s -> Auxl.error s
    in
    Embed_pp.pp_embed_spec fd_dst m sd.syntax lookup (Auxl.collapse_embed_spec_el_list unfiltered_document);
    let _ = close_in fd_src in
    let _ = close_out fd_dst in
    ()
  in

  (List.iter (filter m_tex) (!tex_filter_filenames));
  (List.iter (filter m_coq) (!coq_filter_filenames));
  (List.iter (filter m_isa) (!isa_filter_filenames));
  (List.iter (filter m_hol) (!hol_filter_filenames));
  (List.iter (filter m_lem) (!lem_filter_filenames));
  (List.iter (filter m_twf) (!twf_filter_filenames));
  (List.iter (filter m_caml) (!caml_filter_filenames));
   
(*  let xd,rdcs = Grammar_typecheck.check_and_disambiguate targets document in  *)

  if !process_defns then begin
    let bad, msg = Defns.pp_counts sd in
    print_string msg;
    if bad && !signal_parse_errors then exit 1
  end;
  ()

(* set GC parameters to reasonable values *)
let _ =
  Gc.set { (Gc.get()) with
           Gc.minor_heap_size = 2*1024*1024      (*  8/16 MB in 32/64bit machines *); 
           Gc.major_heap_increment = 5*1024*1024 (* 40/80 MB in 32/64bit machines *)};;

let _ = match source_filenames, !read_systemdefn_filename_opt with
| (_::_),None -> 
    let (sd,lookup) = process source_filenames in
    output_stage (sd,lookup)
| [], Some s ->
    let (sd,lookup) = read_systemdefn s in
    output_stage (sd,lookup)
| [],None -> 
    Arg.usage options usage_msg;
    Auxl.error "\nError: must specify either some source filenames or a readsys option\n"
| (_::_),Some _ -> Auxl.error "\nError: must not specify both source filenames and a readsys option\n"
