/**************************************************************************/
/*                                   Ott                                  */
/*                                                                        */
/*        Peter Sewell, Computer Laboratory, University of Cambridge      */
/*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     */
/*                                                                        */
/*  Copyright 2005-2010                                                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*  notice, this list of conditions and the following disclaimer.         */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*  notice, this list of conditions and the following disclaimer in the   */
/*  documentation and/or other materials provided with the distribution.  */
/*  3. The names of the authors may not be used to endorse or promote     */
/*  products derived from this software without specific prior written    */
/*  permission.                                                           */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    */
/*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     */
/*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    */
/*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       */
/*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    */
/*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     */
/*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         */
/*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  */
/*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       */
/*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   */
/*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         */
/**************************************************************************/

/* parser for raw grammars */

%{
open Location
open Types
open Auxl

let mkl () = 
   [ { Location.loc_start = symbol_start_pos ();  
       Location.loc_end = symbol_end_pos () } ]

let mkp () = 
   symbol_start_pos ()

(* let mkl x =  *)
(*   let l = {Location.loc_start=symbol_start_pos ();  *)
(* 	   Location.loc_end=symbol_end_pos ()} in *)
(*   (\* print_string (Location.pp_t l) ; flush stdout; *\)  *)
(*   {desc=x; loc=l} *)
    
let parse_error s = 
  raise (My_parse_error ("Parse error: " ^ s ^ " " 
	   ^ Location.pp_position2 (Parsing.symbol_end_pos () )))

(* %token EQUAL             *)
%}

%token <string*string> STRING 
%token <string> BLANKS
%token <string*string> LINE
%token <string*string*string> LINELINE
%token <string> BLANKLINE
%token <string> COMMENTLINE
%token <string> INTERSTITIAL
%token EOF


%token COMMA
%token CCE              
%token BAR              

%token DOUBLELEFTBRACKET 
%token DOUBLERIGHTBRACKET
%token DOUBLELEFTBRACE
%token DOUBLERIGHTBRACE
%token COLONCOLON         
%token LTCOLONCOLON         
%token UNDERSCORECOLONCOLON
%token DOTDOT
%token DOTDOTDOT
%token DOTDOTDOTDOT
%token EMBED
%token METAVAR INDEXVAR
%token RULES
%token SUBRULES
%token CONTEXTRULES
%token SUBSTITUTIONS
%token FREEVARS
%token DEFNCLASS
%token DEFN
%token FUNDEFNCLASS
%token FUNDEFN
%token DEFNCOM
%token BY
%token SINGLE MULTIPLE
%token HOMS
%token PARSING
%token LTEQ
%token LEFT
%token RIGHT
%token NON

%token BIND_LEFT_DELIM BIND_RIGHT_DELIM
%token BIND IN EQ HASH NAMES DISTINCTNAMES
%token LPAREN RPAREN
%token UNION  EMPTY

%token COQSECTIONBEGIN COQSECTIONEND COQVARIABLE

%token COMP_LEFT COMP_MIDDLE COMP_RIGHT COMP_IN

%right UNION

%nonassoc DUMMY_ABOVE_EMBED
%nonassoc EMBED

%start main             /* the entry point */
%start drule_line_annot 
%start unfiltered_spec_el_list
%start embed_spec_el_list

%type <Types.raw_drule_line_annot> drule_line_annot 

%type <Types.raw_item list> main

%type <Types.embed_spec_el list> unfiltered_spec_el_list

%type <Types.embed_spec_el list> embed_spec_el_list

%%

main:
   items    { $1 } 

items: 
   item items                     { $1 :: $2 }
 | EOF                            { [] }

item: 
   metavardefn                    { $1 }
 | RULES rules                    { $2 } 
 | DEFNCLASS defnclass            { $2 }  
 | FUNDEFNCLASS fundefnclass      { $2 }  
 | SUBRULES subrules              { $2 }  
 | CONTEXTRULES contextrules      { $2 }
 | SUBSTITUTIONS substitutions    { $2 }  
 | FREEVARS freevars              { $2 }  
 | EMBED embed                    { $2 }	
 | PARSING parsing_annotations    { $2 }	
 | HOMS hom_section               { $2 }
 | COQSECTIONBEGIN coq_section_begin { $2 }
 | COQSECTIONEND coq_section_end     { $2 }
 | COQVARIABLE coq_variable          { $2 }

metavardefn:
   metavardefn_int   
     { Raw_item_md $1 }
 | indexvardefn_int   
     { Raw_item_md $1 }

metavardefn_int:
   METAVAR ne_ident_hom_desc_list CCE metavarrep
     { { raw_mvd_name = fst(List.hd($2));
         raw_mvd_names = $2;
	 raw_mvd_rep = $4; 
         raw_mvd_indexvar = false;
         raw_mvd_loc = mkl() } }

indexvardefn_int:
   INDEXVAR ne_ident_hom_desc_list CCE metavarrep
     { { raw_mvd_name = fst(List.hd($2));
         raw_mvd_names = $2;
	 raw_mvd_rep = $4;
         raw_mvd_indexvar = true;
         raw_mvd_loc = mkl() } }

metavarrep:
   homomorphism_list              { $1 }

homomorphism_list:
   /* empty */                    { [] }
 | homomorphism homomorphism_list { $1::$2 }

homomorphism:
   DOUBLELEFTBRACE hom_name hom_spec_el_list DOUBLERIGHTBRACE
     { ($2, $3, mkl()) }

hom_name:
   STRING BLANKS		  { fst $1 }
 | BLANKS STRING BLANKS		  { fst $2 }

hom_spec_el_list:
   /* empty */                    { [] }
 | hom_spec_el hom_spec_el_list   { $1::$2 }

hom_spec_el:
   DOUBLELEFTBRACKET hom_inner DOUBLERIGHTBRACKET { $2 }
 | STRING 			  { Raw_hom_string (fst $1) }
 | BLANKS 			  { Raw_hom_blanks $1 }
 | DOTDOT                         { Raw_hom_string ".." }
 | DOTDOTDOT                      { Raw_hom_string "..." }
 | DOTDOTDOTDOT                   { Raw_hom_string "...." }

hom_inner:
   ident_and_blanks_list          { Raw_hom_ident $1 }
 | ident_and_blanks_list dots ident_and_blanks_list   
                                  { Raw_hom_ident_dots (mkl(),$1,$2,$3) } 
 | COMP_LEFT  ident_and_blanks_list COMP_MIDDLE comp_bound COMP_RIGHT blanks_list 
                                  { Raw_hom_ident_comp (mkl(),$2,$4) }

embedmorphism_list:
   /* empty */                    { [] }
 | embedmorphism embedmorphism_list { $1::$2 }

embedmorphism:
   DOUBLELEFTBRACE hom_name embed_spec_el_list DOUBLERIGHTBRACE
     { (mkl(), $2, $3) }

embed_spec_el_list:
   /* empty */                    { [] }
 | embed_spec_el embed_spec_el_list   { $1::$2 }

embed_spec_el:
   DOUBLELEFTBRACKET embed_inner DOUBLERIGHTBRACKET
				  { Embed_inner (mkl(),$2) }
 | STRING 			  { Embed_string (mkl(),fst $1) }
 | BLANKS 			  { Embed_string (mkl(),$1) }
 | DOTDOT                         { Embed_string (mkl(),"..") }
 | DOTDOTDOT                      { Embed_string (mkl(),"...") }
 | DOTDOTDOTDOT                   { Embed_string (mkl(),"....") }

embed_inner:
   /* empty */                    { "" }
 | STRING embed_inner             { (fst $1) ^ $2 }
 | BLANKS embed_inner             { $1 ^ $2 }


bindspec:
   BIND mse IN ident              { Raw_Bind (mkl(), $2 ,$4) }
 | ident EQ mse                   { Raw_AuxFnDef (mkl(), $1, $3) }
 | NAMES LPAREN mse RPAREN EQ NAMES LPAREN mse RPAREN    
                                  { Raw_NamesEqual (mkl(), $3, $8) }
 | NAMES LPAREN mse RPAREN HASH NAMES LPAREN mse RPAREN  
                                  { Raw_NamesDistinct (mkl(), $3, $8) }
 | DISTINCTNAMES LPAREN mse RPAREN    
                                  { Raw_AllNamesDistinct (mkl(), $3) }

bindspeclist:
   /*empty*/                      { [] }
 | bindspec bindspeclist          { $1 :: $2 }

mse:
   ident                          { Raw_MVorNTExp (mkl(), $1) }
 | ident dots ident               { Raw_MVorNTListExp_dotform (mkl(), $1, $2, $3) }
 | COMP_LEFT ident COMP_MIDDLE comp_bound COMP_RIGHT  { Raw_MVorNTListExp_comp (mkl(), $2, $4) }
 | ident LPAREN ident RPAREN      { Raw_Aux (mkl(), $1, $3) }
 | ident LPAREN ident dots ident RPAREN  { Raw_AuxList_dotform (mkl(), $1, $3, $4, $5) }
 | ident LPAREN COMP_LEFT ident COMP_MIDDLE comp_bound COMP_RIGHT RPAREN  { Raw_AuxList_comp (mkl(), $1, $4, $6) }
 | ident COMP_LEFT ident COMP_MIDDLE comp_bound COMP_RIGHT { Raw_AuxList_comp (mkl(), $1, $3, $5) }
 | mse UNION mse                  { Raw_Union (mkl(), $1, $3) }
 | EMPTY                          { Raw_Empty (mkl()) }

bindspeclistlist:
     /*empty*/                    { [] }
 | BIND_LEFT_DELIM bindspeclist BIND_RIGHT_DELIM bindspeclistlist  {$2 :: $4 }

bindspecall:
   bindspeclistlist              { List.flatten $1 }

dots:
 | DOTDOT                         { 0 }
 | DOTDOTDOT                      { 1 }
 | DOTDOTDOTDOT                   { 2 }

element:
   ident                          { Raw_ident (mkl(), $1) }
/*  | LEFTBRACKET element_list RIGHTBRACKET               */
/*                                   { Raw_option (mkl(), $2) } */
/*  | LEFTBRACE element_list RIGHTBRACE                  */
/*                                   { Raw_list (mkl(), $2) } */
/*  | LEFTBRACE element_list RIGHTBRACEPLUS              */
/*                                   { Raw_nelist (mkl(), $2) } */
/*  | DOUBLELEFTBRACKET element DOUBLERIGHTBRACKET  */
/*                                   { Raw_sugaroption (mkl(), $2) } */
 | dots                           { Raw_dots (mkl(),$1) }
 | COMP_LEFT element_list COMP_MIDDLE comp_bound COMP_RIGHT {Raw_comp(mkl(),$2,$4,None)}
 | COMP_LEFT element_list COMP_MIDDLE ident COMP_MIDDLE comp_bound COMP_RIGHT {Raw_comp(mkl(),$2,$6,Some $4)}

comp_bound:
     ident                          {Raw_bound_comp(mkl(),$1) }
 |   ident COMP_IN ident            {Raw_bound_comp_u(mkl(),$1,$3)}
 |   ident COMP_IN ident dots ident {Raw_bound_comp_lu(mkl(),$1,$3,$4,$5)}

element_list:
   /* empty */                    { [] }
 | element element_list           { $1 :: $2 }

rules:
   rule_list
     { Raw_item_rs $1 }

rule_list:
   /* empty */                    { [] }
 | rule rule_list                 { $1 :: $2 }

rule: 
   ne_ident_hom_desc_list COLONCOLON STRING CCE homomorphism_list prodlist 
     { { raw_rule_ntr_name  = fst (List.hd($1));
         raw_rule_ntr_names = $1;
         raw_rule_pn_wrapper = (fst $3);
         raw_rule_ps = $6;
	 raw_rule_homs = $5;
         raw_rule_categories = ["user"];
         raw_rule_loc = mkl() } }

prod:
   flavour element_list COLONCOLON ident_list COLONCOLON STRING bindspecall homomorphism_list
     { { raw_prod_name = (fst $6);
         raw_prod_flavour = $1;
         raw_prod_categories = $4;
         raw_prod_es = $2;
	 raw_prod_homs = $8;
         raw_prod_bs = $7;
	 raw_prod_loc = mkl() } }

prodlist:
   /* empty */                    { [] }
 | prod prodlist                  { $1 :: $2 }

flavour:
   BAR                            { Bar }

ident_desc:
   STRING                         {  (fst $1) }

ne_ident_hom_desc_list:
   ident_desc homomorphism_list   { [($1,$2)] }
 | ident_desc homomorphism_list COMMA ne_ident_hom_desc_list  { ($1,$2) :: $4 }

ident_desc_list:
   /* empty */                    { [] }
 | ident_desc COMMA ident_desc_list     { $1 :: $3 }

ident:
   STRING                         { (mkl(),  (fst $1)) }

blanks:
   BLANKS                         { (mkl(),  ($1)) }

ident_list:
   /* empty */                    { [] }
 | ident ident_list               { $1 :: $2 }
 | BLANKS ident_list              { $2 }

ident_and_blanks_list:
   /* empty */                    { [] }
 | ident  ident_and_blanks_list   { $1 :: $2 }
 | blanks ident_and_blanks_list  { $1 :: $2 }

blanks_list:
   /* empty */                    { () }
 | BLANKS blanks_list              { () }

defnclass: 
   STRING COLONCOLON STRING CCE homomorphism_list defn_list 
     { let rdc = { raw_dc_name = (fst $1);
                   raw_dc_homs = $5;
                   raw_dc_wrapper = (fst $3);
                   raw_dc_defns = $6;
		   raw_dc_loc = mkl() } in
       Raw_item_dcs (Raw_RDC rdc) }

defn_list:
   /* empty */                   { [] }
 | defn defn_list                { $1 :: $2 }

defn: 
   DEFN element_list COLONCOLON ident_list COLONCOLON STRING COLONCOLON STRING homomorphism_list  BY semiraw_rule_list /*linelist */
     { { raw_d_name = (fst $6);
         raw_d_es = $2;
         raw_d_categories = $4;
         raw_d_wrapper = (fst $8);
         raw_d_body = $11;
         raw_d_homs = $9;
         raw_d_loc = mkl() } }

drule_line_annot: 
   ident_list COLONCOLON STRING homomorphism_list EOF 
     { { dla_name = (fst $3); 
	 dla_categories = $1;
         dla_homs = $4 } }

fundefnclass: 
   STRING CCE homomorphism_list fundefn_list 
     { let frdc = { raw_fdc_name = (fst $1);
                    raw_fdc_homs = $3;
                    raw_fdc_fundefns = $4;
		    raw_fdc_loc = mkl() } in
       Raw_item_dcs (Raw_FDC frdc) }

fundefn_list:
   /* empty */                   { [] }
 | fundefn fundefn_list                { $1 :: $2 }

fundefn: 
   FUNDEFN element_list COLONCOLON ident COLONCOLON STRING homomorphism_list  BY BLANKLINE anylinelist 
     { { raw_fd_name = (fst $6);
         raw_fd_es = $2;
         raw_fd_result = $4;
         raw_fd_result_type = "dummy, to be replaced by grammar_typecheck";
         raw_fd_pn_wrapper = "dummy, to be replaced by grammar_typecheck";
         raw_fd_clauses = $10;
         raw_fd_homs = $7;
         raw_fd_loc = mkl() } }


anylinelist:
   /* empty */               { [] }
 | line anylinelist            { $1 :: $2 }
 | COMMENTLINE anylinelist     { (* Raw_commentline (mkl(), $1) ::*) $2 }
 | BLANKLINE anylinelist      { (* Raw_blankline (mkl(), $1) :: *) $2 }




line:
   LINE                      { (mkl(),fst $1) }

lineline:
   LINELINE                  { let (a,b,_) = $1 in (mkl(), b) }
     
linelist:
   /* empty */               { [] }
 | line linelist            { $1 :: $2 }
 | COMMENTLINE linelist     { (* Raw_commentline (mkl(), $1) ::*) $2 }

nelinelist:
 | line linelist                { $1 :: $2 }
 | COMMENTLINE linelist         { (* Raw_commentline (mkl(), $1) ::*) (* (mkl(),$1) ::*) $2 }

semiraw_rule:
     linelist lineline linelist { Lined_rule (mkl(),$1,$2,$3) }
 |   nelinelist                 { Lineless_rule (mkl(),$1) }

blanklinelist:
   /* empty */                  { () }
 | BLANKLINE blanklinelist      { (* Raw_blankline (mkl(), $1) :: *) () }

neblanklinelist:
   BLANKLINE                    { () }
 | BLANKLINE neblanklinelist    { (* Raw_blankline (mkl(), $1) :: *) () }


defncom:
   DEFNCOM embed_spec_el_list DOUBLERIGHTBRACE { Defncom(mkl(),$2) }

semiraw_rule_list:
   blanklinelist                { [] }
 | neblanklinelist semiraw_rule semiraw_rule_list { $2 :: $3 } 
 | neblanklinelist defncom semiraw_rule_list { $2 :: $3 } 


subrules:
   subrules_body
     { Raw_item_srs $1 }

subrules_body:
   /* empty */               { [] }
 | subrule subrules_body     { $1 :: $2 }

subrule: 
   ident_desc LTCOLONCOLON ident_desc homomorphism_list  
      { { raw_sr_lower = $1;
          raw_sr_upper = $3;
	  raw_sr_homs =  $4  ;
	  raw_sr_loc = mkl() } }

contextrules:
   contextrules_body
     { Raw_item_crs $1 }

contextrules_body:
   /* empty */                       { [] }
 | contextrule contextrules_body     { $1 :: $2 }

contextrule:
   ident_desc UNDERSCORECOLONCOLON ident_desc COLONCOLON ident_desc 
      { { raw_cr_ntr = $1;
          raw_cr_target = $3;
          raw_cr_hole = $5;
	  raw_cr_homs = [];
	  raw_cr_loc = mkl() } }

substitutions:
   substitutions_body        
     { Raw_item_sbs $1 }

substitutions_body:
   /* empty */                          { [] }
 | substitution substitutions_body      { $1 :: $2 }

substitution: 
   substitution_kind ident_desc ident_desc COLONCOLON ident_desc homomorphism_list
     { { raw_sb_name = $5;
         raw_sb_this = $2;
         raw_sb_that = $3;
         raw_sb_multiple = $1;
	 raw_sb_homs =  $6  ;
         raw_sb_loc = mkl() } }
 
substitution_kind:
   SINGLE  { false }
 | MULTIPLE { true }

freevars:
   freevars_body        
     { Raw_item_fvs $1 }

freevars_body:
   /* empty */                          { [] }
 | freevar freevars_body      { $1 :: $2 }

freevar:                                      
   ident_desc ident_desc COLONCOLON ident_desc homomorphism_list
     { { raw_fv_name = $4;
         raw_fv_this = $1;
         raw_fv_that = $2;
	 raw_fv_homs = $5  ;
         raw_fv_loc = mkl() } }

embed:
   embedmorphism_list
     { Raw_item_embed $1 }

parsing_annotation_type:
    LTEQ  { LTEQ }
  | LEFT  { Left }
  | RIGHT { Right }
  | NON   { Non}

parsing_annotations:
   parsing_annotations_body
      { Raw_item_pas 
          [ { raw_pa_data = $1 ; 
	    raw_pa_loc = mkl() } ] 
           } 

parsing_annotations_body:
      /* empty */               { [] }
  | parsing_annotation parsing_annotations_body     { $1 :: $2 }

parsing_annotation: 
     ident_desc parsing_annotation_type ident_desc   {  ($1,$2,$3) }


hom_section_item: 
      COLONCOLON STRING bindspecall homomorphism_list 
        { {raw_hsi_name=fst $2; raw_hsi_bs=$3; raw_hsi_homs=$4; raw_hsi_loc=mkl() } }

hom_section_item_list: 
   /* empty */                                { [] }
 | hom_section_item hom_section_item_list     { $1 :: $2 }

hom_section:
  STRING hom_section_item_list 
     { let raw_hs = { raw_hs_wrapper=(fst $1); raw_hs_hsis=$2; raw_hs_loc=mkl() } in
       Raw_item_hs raw_hs }

coq_section_begin:
  STRING 
     { let raw_rqs = { raw_rqs_name=(fst $1); raw_rqs_begin=true; raw_rqs_loc=mkl() } in
       Raw_item_coq_section raw_rqs }

coq_section_end:
  STRING 
     { let raw_rqs = { raw_rqs_name=(fst $1); raw_rqs_begin=false; raw_rqs_loc=mkl() } in
       Raw_item_coq_section raw_rqs }

coq_variable:
  STRING 
     { let raw_rqv = { raw_rqv_name=(fst $1); raw_rqv_loc=mkl() } in
       Raw_item_coq_variable raw_rqv }

 

unfiltered_spec_el_list:
   /* empty */                    { [] }
 | unfiltered_spec_el unfiltered_spec_el_list   { $1::$2 }

unfiltered_spec_el:
   DOUBLELEFTBRACKET unfiltered_inner DOUBLERIGHTBRACKET
				  { Embed_inner (mkl(),$2) }
 | STRING 			  { Embed_string (mkl(),fst $1) }
 | BLANKS 			  { Embed_string (mkl(),$1) }

unfiltered_inner:
   /* empty */                         { "" }
 | STRING unfiltered_inner             { (fst $1) ^ $2 }
 | BLANKS unfiltered_inner             { $1 ^ $2 }


