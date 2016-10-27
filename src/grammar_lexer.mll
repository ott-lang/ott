(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2008                                                   *)
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

(* lexer for raw grammars *)

(* the concrete metasyntax here involves hackery to lex the contents of *)
(* bindspecs and homs rather differently to the production body, and to lex *)
(* definitions on a line-by-line basis.  It should be rewritten. *)



{
open Location
open Auxl
open Grammar_parser       

exception Eof
exception CannotHappen

let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- 
    { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum }

type lexer = Lexing.lexbuf -> Grammar_parser.token

type token_type = Tok_kw of string | Tok_sym of string*string | Tok_sym_direct of string*string | Tok_user of string 

let hom_strings = ["TEX_NAME_PREFIX";"formula";"terminals";"M";"S";"tex";"com";"coq";"hol";"lem";"isa";"ocaml";"icho";"ichlo";"ich";"ichl";"coq-equality";"isasyn";"isaprec";"lex";"texvar";"isavar";"holvar";"lemvar";"ocamlvar";"repr-locally-nameless";"phantom";"coq-struct";"isa-proof";"isa-auxfn-proof";"isa-subrule-proof";"coq-lib"]


let de_lex t = match t with
| EOF                  -> failwith "unexpected EOF in de_lex"
| INTERSTITIAL(s)      -> Tok_user s
| STRING (s1,s2)       -> Tok_sym_direct (s2, if List.mem s2 hom_strings then "\\mykw{"^s2^"}" else Auxl.pp_tex_escape_alltt s2)
| COMMENTLINE s        -> Tok_user s
| BLANKLINE s          -> Tok_user s
| LINELINE(s1,s2,s3)   -> Tok_sym_direct (s1^s2^s3, "\\mysym{"^s1^"}"^Auxl.pp_tex_escape_alltt (s2^s3))
| LINE (s1,s2)         -> Tok_user (s1^s2)
| BLANKS s             -> Tok_user s
| EMBED                -> Tok_kw "embed"                        
| HOMS                 -> Tok_kw "homs"                         
| METAVAR              -> Tok_kw "metavar"                      
| INDEXVAR             -> Tok_kw "indexvar"                     
| RULES                -> Tok_kw "grammar"                      
| SUBRULES             -> Tok_kw "subrules"                     
| CONTEXTRULES         -> Tok_kw "contextrules"                     
| SUBSTITUTIONS        -> Tok_kw "substitutions"                
| SINGLE               -> Tok_kw "single"                       
| MULTIPLE             -> Tok_kw "multiple"                     
| FREEVARS             -> Tok_kw "freevars"                     
| DEFNCLASS            -> Tok_kw "defns"                        
| DEFN                 -> Tok_kw "defn"                         
| FUNDEFNCLASS         -> Tok_kw "funs"                        
| FUNDEFN              -> Tok_kw "fun"                         
| BY                   -> Tok_kw "by"                           
| BIND                 -> Tok_kw "bind"          
| IN                   -> Tok_kw "in"            
| NAMES                -> Tok_kw "names"         
| DISTINCTNAMES        -> Tok_kw "distinctnames" 
| UNION                -> Tok_kw "union"         
| COMP_IN              -> Tok_kw "IN"            
| PARSING              -> Tok_kw "parsing"
| LEFT                 -> Tok_kw "left"
| RIGHT                -> Tok_kw "right"
| NON                  -> Tok_kw "non"
| COQSECTIONBEGIN      -> Tok_kw "begincoqsection"
| COQSECTIONEND        -> Tok_kw "endcoqsection"
| COQVARIABLE          -> Tok_kw "coqvariable"
| LTEQ                 -> Tok_sym ("<="   ,"<=")
| BIND_LEFT_DELIM      -> Tok_sym ("(+"   , "(+")
| DOTDOT               -> Tok_sym (".."   , "..")          
| DOTDOTDOT            -> Tok_sym ("..."  , "...")          
| DOTDOTDOTDOT         -> Tok_sym ("...." , "....")          
| COMP_LEFT            -> Tok_sym ("</"   , "</")          
| COMP_MIDDLE          -> Tok_sym ("//"   , "//")          
| COMP_RIGHT           -> Tok_sym ("/>"   , "/>")          
| DOUBLELEFTBRACKET    -> Tok_sym ("[["   , "[[")
| DOUBLERIGHTBRACKET   -> Tok_sym ("]]"   , "]]")     
| COMMA                -> Tok_sym (","    , ",")
| CCE                  -> Tok_sym ("::="  , "::=")
| BAR                  -> Tok_sym ("|"    , "|")
| DOUBLELEFTBRACE      -> Tok_sym ("{{"   , "\\mylb\\mylb{}")                          
| DOUBLERIGHTBRACE     -> Tok_sym ("}}"   , "\\myrb\\myrb{}")                          
| COLONCOLON           -> Tok_sym ("::"   , "::")                          
| LTCOLONCOLON         -> Tok_sym ("<::"  , "<::")                          
| UNDERSCORECOLONCOLON -> Tok_sym ("_::"  , "_::")                          
| BIND_RIGHT_DELIM     -> Tok_sym ("+)"   , "+)")
| DEFNCOM              -> Tok_sym ("{{com", "\\mylb\\mylb\\mybf{com}")
| EQ                   -> Tok_sym ("="    , "=")         
| HASH                 -> Tok_sym ("#"    , "#")         
| LPAREN               -> Tok_sym ("("    , "(")         
| RPAREN               -> Tok_sym (")"    , ")")         
| EMPTY                -> Tok_sym ("{}"   , "\\mylb\\myrb{}")         


let de_lex_ascii t = match de_lex t with
| Tok_user s -> s
| Tok_kw s -> s
| Tok_sym (s1,s2) -> s1
| Tok_sym_direct (s1,s2) -> s1

let de_lex_tex t = match de_lex t with
| Tok_user s -> Auxl.pp_tex_escape_alltt s
| Tok_kw s -> "\\mykw{"^s^"}"
| Tok_sym (s1,s2) -> "\\mysym{"^s2^"}"
| Tok_sym_direct (s1,s2) -> s2


exception No_Lexer_Here
let my_lexer_state = ref ((function _ -> raise No_Lexer_Here) : lexer)

let my_lexer : bool -> lexer -> lexer =
  fun strip_interstitials -> 
    fun initial_lexer -> 
      my_lexer_state := initial_lexer;
      fun lexbuf ->
        let next_token () =
          !my_lexer_state lexbuf in
        let rec next_non_interstitial_token () = 
          let t = 
            next_token () in
          match t with
          | INTERSTITIAL s -> next_non_interstitial_token ()
          | _ -> t in
        try 
          if strip_interstitials then 
            next_non_interstitial_token ()
          else
            next_token ()
        with
          ex -> 
            (print_string ("Lexing error at "^pp_position2 lexbuf.Lexing.lex_curr_p^"\n");
             flush stdout;
             raise ex)
          
let trim : string -> string =
  fun s ->
    String.sub s 0 (String.length s -1)

let dequote s = 
  let l = String.length s in 
  if l <=1 then s else 
  if String.get s 0 = '\'' && String.get s (l-1) = '\'' 
  then String.sub s 1 (l-2)
  else s
      
let get_first_word_and_rest =
  let whitespace = [' '; '\t';'\010'; '\012'; '\013' ] in
  let rec skip_whitespace s l n =
    if n <= l && List.mem (String.get s n) whitespace then
      skip_whitespace s l (n + 1) else n in
  let rec skip_until_whitespace s l n =
    if n <= l && not (List.mem (String.get s n) whitespace) then 
      skip_until_whitespace s l (n + 1) else n in
  fun s ->
    let l = String.length s in
    let n1 = skip_whitespace s l 0 in
    let n2 = skip_until_whitespace s l n1 in
    (String.sub s n1 (n2 - n1), l - n2)

(** hack to move the lexer [n] characters back. *)
let go_back n f lexbuf =
  lexbuf.Lexing.lex_curr_pos <- lexbuf.Lexing.lex_curr_pos - n;
  my_lexer_state := f

} 

let whitespace = (' ' | '\t' | '\010' | '\012' | '\013')
let newline = ('\010' | '\013' | "\013\010")
let non_newline = [^ '\010' '\013']
let non_newline_whitespace = (' ' | '\t' |'\012')
(* let pre_ident = (['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | "_" | "'")(['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | "_" | "-" | "'")* *)
let pre_ident = (['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | "_" | "'")(['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | "_" | "'")*
let maybe_quoted_ident = pre_ident | ("'" pre_ident "'" ) | "''"
(*
let pre_ident_allow_minus = (['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | "_" | "'")(['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | "_" | "-" | "'")*
let maybe_quoted_ident_allow_minus = pre_ident_allow_minus | ("'" pre_ident_allow_minus "'" ) | "''"
*)
let string = [^ ' '  '\t'  '\010'  '\012'  '\013']+


(* We use context-dependent lexing, lexing (eg) the elements of a *)
(* production w.r.t. a small language so that the user rarely has to *)
(* quote tokens. *)


(* lexing for the top-level ott source file *)
(* - whitespace is discarded *)
(* - only maybe_quoted_idents are allowed, not arbitary strings, *)
(*    as they are all nonterminals or metavars.  This lets us have *)
(*    non-space-separated comma-separated lists*)
(* - these maybe_quoted_idents are dequoted, so the user can avoid *)
(*    clashes with the keywords below *)
(* - comments are allowed *)
(* NB: take care that all the tokens below are listed in quoted_token in grammar_pp.ml *)
(* so that they are ASCII pretty printed appropriately *)
rule metalang = parse
    non_newline_whitespace+ as lxm { INTERSTITIAL(lxm) }     
  | newline as lxm                 { incr_linenum lexbuf; INTERSTITIAL(lxm) } 
  | ">>"                           { comments metalang [ lexbuf.Lexing.lex_curr_p ] lexbuf }
  | ("%"[^'\010' '\013']* newline) as lxm    { incr_linenum lexbuf; INTERSTITIAL(lxm) }  
  | ","                            { COMMA }
  | "::="                          { CCE                  }
  | "|"                            { my_lexer_state := elements; BAR }
  | "{{"                           { my_lexer_state := hom metalang; DOUBLELEFTBRACE      }
  | "}}"                           { DOUBLERIGHTBRACE     }
  | "::"                           { COLONCOLON           }
  | "<::"                          { LTCOLONCOLON         }
  | "_::"                          { UNDERSCORECOLONCOLON }
  | "embed"                        { EMBED                }
  | "homs"                         { HOMS                 }
  | "metavar"                      { METAVAR              }
  | "indexvar"                     { INDEXVAR             }
  | "grammar"                      { RULES                }
  | "subrules"                     { SUBRULES             }
  | "contextrules"                 { CONTEXTRULES         }
  | "substitutions"                { SUBSTITUTIONS        }
  | "single"                       { SINGLE               }
  | "multiple"                     { MULTIPLE             }
  | "freevars"                     { FREEVARS             }
  | "parsing"                      { PARSING              }
  | "begincoqsection"              { COQSECTIONBEGIN      }
  | "endcoqsection"                { COQSECTIONEND        }
  | "coqvariable"                  { COQVARIABLE          }
  | "<="                           { LTEQ                 }
  | "left"                         { LEFT                 }
  | "right"                        { RIGHT                }
  | "non"                          { NON                  }
  | "defns"                        { DEFNCLASS            }
  | "funs"                         { FUNDEFNCLASS         }
  | "defn"                         { my_lexer_state := elements; DEFN            }
  | "fun"                          { my_lexer_state := elements; FUNDEFN         }
  | "by"                           { my_lexer_state := defnlang; BY              }
  | "(+"                           { my_lexer_state := bindspec; BIND_LEFT_DELIM }
  | "{{*"                          { my_lexer_state := hom_star metalang; DOUBLELEFTBRACE      }
  | "*}}"                          { DOUBLERIGHTBRACE     }
  | maybe_quoted_ident as lxm      { STRING(dequote(lxm),lxm) } 
  | eof                            { EOF                  }

(* lexing for the elements of a production. *)
(* - tokens must be whitespace-separated, *)
(* - whitespace is discarded *)
(* - arbitrary strings are allowed, and are dequoted *)
(* - comments are not allowed *)
and elements = parse
    non_newline_whitespace+ as lxm { INTERSTITIAL(lxm) }     
  | newline as lxm                 { incr_linenum lexbuf; INTERSTITIAL(lxm) } 
  | "::"                           { my_lexer_state := metalang; COLONCOLON }
  | ".."                           { DOTDOT               }
  | "..."                          { DOTDOTDOT            }
  | "...."                         { DOTDOTDOTDOT         }
  | "</"                           { COMP_LEFT            }
  | "//"                           { COMP_MIDDLE          }
  | "/>"                           { COMP_RIGHT           }
  | "IN"                           { COMP_IN              }
  | string as lxm                  { STRING(dequote(lxm),lxm) } 
  | eof                            { EOF                  }
(* for BNF options and lists *)
(*| "{"                            { LEFTBRACE            } *)
(*| "}"                            { RIGHTBRACE           } *)
(*| "}+"                           { RIGHTBRACEPLUS       } *)
(*| "["                            { LEFTBRACKET          } *)
(*| "]"                            { RIGHTBRACKET         } *)
(*| "[["                           { DOUBLELEFTBRACKET    } *)
(*| "]]"                           { DOUBLERIGHTBRACKET   } *)


(* lexing for a homomorphism, including any [[inner]] parts *)
(* - this is used both for normal homomorphisms and embedmorphisms *)
(* - the non-inner parts of both, and the inner parts of the latter, *)
(*    have to have their whitespace preserved, as the first is passed *)
(*    through to the proof assistant and the second is processed as a *)
(*    symterm by ott.  We therefore produce both BLANKS and STRING *)
(* - apart from [[ ]] {{ }} .. ... ...., arbitrary strings are allowed *)
(* - to allow non-spaced inner parts, eg [[x]], as the lexer does longest-match, *)
(*    we treat [ ] { } . specially.  The original string is then agglomerated back *)
(*    in grammar_typecheck. *)
(* - we used to have a mechanism to let the user write (eg) [[[ in order to *)
(*    pass through literal [[ to the proof assistant.  But they should all *)
(*    be insensitive to intermediate whitespace between the [, so for simplicity *)
(*    it's now removed *)
(* - comments are not allowed *)
and hom returnstate = parse
    non_newline_whitespace+ as lxm { BLANKS(lxm) }     
  | newline as lxm                 { incr_linenum lexbuf; BLANKS(lxm) } 
(*| "[[" "["+ as lxm               { STRING( trim lxm )   } *)
(*| "]]" "]"+ as lxm               { STRING( trim lxm )   } *)
(*| "{{" "{"+ as lxm               { STRING( trim lxm )   } *)
(*| "}}" "}"+ as lxm               { STRING( trim lxm )   } *)
  | "[["                           { DOUBLELEFTBRACKET    }
  | "]]"                           { DOUBLERIGHTBRACKET   } 
  | "{{"                           { DOUBLELEFTBRACE      }
  | "}}"                           { my_lexer_state := returnstate; DOUBLERIGHTBRACE     }
  | "["  as lxm                    { STRING( "[",String.make 1 lxm )        }    
  | "]"  as lxm                    { STRING( "]",String.make 1 lxm )        }
  | "{"  as lxm                    { STRING( "{",String.make 1 lxm )        }
  | "}"  as lxm                    { STRING( "}",String.make 1 lxm )        }
  | ".."                           { DOTDOT               }
  | "..."                          { DOTDOTDOT            }
  | "...."                         { DOTDOTDOTDOT         }
  | " "*"</"                       { my_lexer_state := comp_bound (hom returnstate); COMP_LEFT            }
  | "." as lxm                     { STRING( ".",String.make 1 lxm)         }
  | [^ ' ' '\t' '\010' '\013' '\012' '[' ']' '{' '}' '.']+ as lxm  { STRING(lxm,lxm) } 
  | eof                            { EOF                  }

(* same as hom, but ends with "*}}" *)
and hom_star returnstate = parse
    non_newline_whitespace+ as lxm { BLANKS(lxm) }     
  | newline as lxm                 { incr_linenum lexbuf; BLANKS(lxm) } 
  | "[["                           { DOUBLELEFTBRACKET    }
  | "]]"                           { DOUBLERIGHTBRACKET   } 
  | "*}}"                          { my_lexer_state := returnstate; DOUBLERIGHTBRACE     }
  | ".."                           { DOTDOT               }
  | "..."                          { DOTDOTDOT            }
  | "...."                         { DOTDOTDOTDOT         }
  | " "*"</"                       { my_lexer_state := comp_bound (hom_star returnstate); COMP_LEFT            }
  | "[" as lxm                     { STRING("[",String.make 1 lxm)        }    
  | "]" as lxm                     { STRING("]",String.make 1 lxm)        }
  | "." as lxm                     { STRING(".",String.make 1 lxm)        }
  | "*" as lxm                     { STRING("*",String.make 1 lxm)        }
  | [^ ' ' '\t' '\010' '\013' '\012' '[' ']' '*' '.']+ as lxm  { STRING(lxm,lxm) } 
  | eof                            { EOF                  }

and comp_bound returnstate = parse
    non_newline_whitespace+ as lxm { INTERSTITIAL(lxm)  }     
  | newline as lxm                 { incr_linenum lexbuf; INTERSTITIAL(lxm) } 
  | ".."                           { DOTDOT               }
  | "..."                          { DOTDOTDOT            }
  | "...."                         { DOTDOTDOTDOT         }
  | "</"                           { COMP_LEFT            }
  | "//"                           { COMP_MIDDLE          }
  | "/>"                           { my_lexer_state := returnstate; COMP_RIGHT           }
  | "IN"                           { COMP_IN              }
  | [^ ' ' '\t' '\010' '\013' '\012' ]+ as lxm  { STRING(lxm,lxm) } 
  | eof                            { EOF                  }

(* lexing for a bindspec, including any x1..xn parts *)
(* - whitespace is discarded *)
(* - only maybe_quoted_idents are allowed; they are dequoted *)
(* - comments are allowed *)
and bindspec = parse
    non_newline_whitespace+ as lxm { INTERSTITIAL(lxm) }     
  | newline as lxm                 { incr_linenum lexbuf; INTERSTITIAL(lxm) } 
  | "%" non_newline* as lxm        { my_lexer_state := linecomment bindspec; INTERSTITIAL(lxm) } 
  | ">>"                           { comments bindspec [ lexbuf.Lexing.lex_curr_p ] lexbuf }
  | "+)"                           { my_lexer_state := metalang; BIND_RIGHT_DELIM }
  | "bind"                         { BIND                }
  | "in"                           { IN                  }
  | "names"                        { NAMES               }
  | "distinctnames"                { DISTINCTNAMES       }
  | "union"                        { UNION               }
  | "="                            { EQ                  }
  | "#"                            { HASH                }
  | "("                            { LPAREN              }
  | ")"                            { RPAREN              }
  | "{}"                           { EMPTY               }
  | ".."                           { DOTDOT              }
  | "..."                          { DOTDOTDOT           }
  | "...."                         { DOTDOTDOTDOT        }
  | "</"                           { COMP_LEFT           }
  | "//"                           { COMP_MIDDLE         }
  | "/>"                           { COMP_RIGHT          }
  | "IN"                           { COMP_IN             }
  | maybe_quoted_ident as lxm      { STRING(dequote(lxm),lxm)} 
  | eof                            { EOF                 }

(* lexing for a definitions *)
(* - here lexing is on a line-by-line basis. *)
(* - comments are allowed *)
and defnlang = parse
  | (non_newline_whitespace* newline) as lxm
      { incr_linenum lexbuf; BLANKLINE(lxm) }  (* blank line *)
  | (non_newline_whitespace* "%"[^'\n']* newline) as lxm
      { incr_linenum lexbuf; COMMENTLINE(lxm) } (* line comment*)
  | (non_newline_whitespace* "%"[^'\n']* eof) 
      { EOF } (* line comment terminated with EOF *)
  | non_newline_whitespace*">>" [' ' '\t' '\012']* newline               
      { incr_linenum lexbuf;                    (* skip some kind of comment *)
        comments defnlang [ lexbuf.Lexing.lex_curr_p ] lexbuf } 
  | (non_newline_whitespace* "----" "-"* as lxm1) (non_newline+ as lxm2) ((newline|eof) as lxm3)
      {incr_linenum lexbuf; LINELINE(lxm1,lxm2,lxm3)} (* line of ---- *)
  | (non_newline+ as lxm1) ((newline|eof) as lxm2)  as lxm
      { (* todo: this is horrible... *)
        let (s, back) = get_first_word_and_rest lxm in
        match s with
        | "grammar"        -> go_back back metalang lexbuf;RULES
	| "embed"	   -> go_back back metalang lexbuf;EMBED	
	| "homs"	   -> go_back back metalang lexbuf;HOMS	       
	| "metavar"	   -> go_back back metalang lexbuf;METAVAR	  
	| "indexvar"	   -> go_back back metalang lexbuf;INDEXVAR
	| "subrules"	   -> go_back back metalang lexbuf;SUBRULES
	| "contextrules"   -> go_back back metalang lexbuf;CONTEXTRULES
	| "substitutions"  -> go_back back metalang lexbuf;SUBSTITUTIONS	
	| "freevars"	   -> go_back back metalang lexbuf;FREEVARS	   
	| "parsing"	   -> go_back back metalang lexbuf;PARSING	  
	| "defns"	   -> go_back back metalang lexbuf;DEFNCLASS
	| "begincoqsection"-> go_back back metalang lexbuf;COQSECTIONBEGIN
	| "endcoqsection"  -> go_back back metalang lexbuf;COQSECTIONEND
	| "coqvariable"	   -> go_back back metalang lexbuf;COQVARIABLE
	| "defn"	   -> go_back back elements lexbuf;DEFN
	| "funs"	   -> go_back back metalang lexbuf;FUNDEFNCLASS
	| "fun"		   -> go_back back elements lexbuf;FUNDEFN
	| "{{com"	   -> go_back back (hom defnlang) lexbuf;DEFNCOM
	| "{{"             -> 
	    begin 
	      let (s, back) = get_first_word_and_rest (String.sub lxm (String.length lxm - back) back) in
	      match s with 
	      | "com"	   -> go_back back (hom defnlang) lexbuf;DEFNCOM
	      | _          -> incr_linenum lexbuf; LINE(lxm1,lxm2) 
            end
        | _ -> incr_linenum lexbuf; LINE(lxm1,lxm2) } (* other newline- or eof-terminated string *)
  | eof                { EOF }




(* lexing for comments *)
and comments surrounding_lexer level = parse
  | "%" non_newline*             
      { comments surrounding_lexer level lexbuf } 
  | "<<"    
      { match level with 
      | [p] -> surrounding_lexer lexbuf 
      | p::ps ->  comments surrounding_lexer ps lexbuf 
      | [] -> raise CannotHappen }
  | ">>"    
      { comments surrounding_lexer (lexbuf.Lexing.lex_curr_p :: level) lexbuf }
  | newline                          
      { incr_linenum lexbuf; comments surrounding_lexer level lexbuf } 
  | _     
      { comments surrounding_lexer level lexbuf }
  | eof     
      { warning ("open comment at "
		 ^ pp_position2 
		     (match level with p::ps->p | []->raise CannotHappen)
		 ^ " is not closed");
	raise End_of_file }

and linecomment surrounding_lexer = parse
  | newline { incr_linenum lexbuf; surrounding_lexer lexbuf } 
  | _       { linecomment surrounding_lexer lexbuf          }
  | eof     { EOF                                           }



    
(* lexing for mng files to be filtered *)
and filter = parse
    non_newline_whitespace+ as lxm { BLANKS(lxm) }     
  | newline as lxm    { incr_linenum lexbuf; BLANKS(lxm) } (* skip nl *)
 (*  | ( non_newline_whitespace+ "%" non_newline+ ) as lxm  { STRING(lxm) }  (* tex comment *) *)
  | [^ ' ' '\t' '\010' '\013' '\012' '[' ']' ]+ as lxm  { STRING(lxm,lxm) } 
  | "[[" "["+ as lxm  { STRING( trim lxm, lxm )   }
  | "]]" "]"+ as lxm  { STRING( trim lxm,lxm )   }
  | "[["              { DOUBLELEFTBRACKET    }
  | "]]"              { DOUBLERIGHTBRACKET   }
  | "["  as lxm       { STRING( "[", String.make 1 lxm )        }    
  | "]"  as lxm       { STRING( "]", String.make 1 lxm )        }
  | eof               { EOF                  }




