Wed Oct  3 16:27:40 BST 2007

The basic structure of a simple Ott execution is to read in a .ott
file, convert it to an internal representation (a value of type
systemdefn) and then pretty print it into the various targets that
were requested on the command line.  The pretty printing functions 
are each parameterised by (and often do a case split on) a pp_mode
telling them which target is being generated.

location.ml            locations in ott source files

types.ml               type definitions, especially of syntaxdefn,
                        relationsdefn, and (roughly their combination) systemdefn

auxl.ml                many assorted auxiliary functions

merge.ml               merging of symbolic terms, eg to take the two
                        endpoints of a putative ... form and form a
                        list, and code to abstract an indexvar from an entity
                       
grammar_lexer.mll      the lexer for .ott source files

grammar_parser.mly     the parser for .ott source files
                       
grammar_pp.ml          pretty printing of the syntaxdefn types, for
                        ascii, latex, coq, hol, isabelle, and ocaml
                       
term_parser.ml         the current(old) parser for user-language concrete and
                        symbolic terms, implemented with memoized
                        parser combinators

glr.ml                 a general glr parser

new_term_parser.ml     a putative replacement parser for the user languages,
                        using glr.ml
                       
dependency.ml          computing the dependencies of a syntaxdefn 

grammar_typecheck.ml   the check_and_disambiguate function, taking a
                        raw syntaxdefn and producing a syntaxdefn (together with a
                        raw_defnclass list)

transform.ml           takes a grammar and returns a grammar in which
                        the dot forms have been expanded using
                        auxiliary list-like constructors  (for Coq)

bounds.ml              bounds extraction - calculuting a dot
                        environment from a set of symbolic terms, identifying which are
                        indexed with the same bounds

substs_pp.ml           pretty print substitution and free variable
                        proof assistant functions

subrules_pp.ml         pretty print is_value predicates for subrules

embed_pp.ml	       pretty print of an embedded part of an .ott file

defns.ml               process inductive definitions, parsing the
                        rules using term_parser, doing bounds
                        analysis, and pretty-printing the rules

coq_induct.ml	       generates induction principles for Coq native lists

system_pp.ml           pretty prints an entire systemdefn, in any of
                        the targets

align.ml               a long identity function

main.ml                the driver, reading .ott files (and files to be filtered),
                        parsing them with grammar_parser, converting
                        them to syntaxdefns with grammar_typecheck,
                        processing their defns with defns, and pretty
                        printing the resulting systemdefns with
                        system_pp



