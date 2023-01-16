#########################################################################
#                                   Ott                                  #
#                                                                        #
#        Peter Sewell, Computer Laboratory, University of Cambridge      #
#      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     #
#                                                                        #
#  Copyright 2005-2017                                                   #
#                                                                        #
#  Redistribution and use in source and binary forms, with or without    #
#  modification, are permitted provided that the following conditions    #
#  are met:                                                              #
#  1. Redistributions of source code must retain the above copyright     #
#  notice, this list of conditions and the following disclaimer.         #
#  2. Redistributions in binary form must reproduce the above copyright  #
#  notice, this list of conditions and the following disclaimer in the   #
#  documentation and/or other materials provided with the distribution.  #
#  3. The names of the authors may not be used to endorse or promote     #
#  products derived from this software without specific prior written    #
#  permission.                                                           #
#                                                                        #
#  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    #
#  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     #
#  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    #
#  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       #
#  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    #
#  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     #
#  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         #
#  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  #
#  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       #
#  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   #
#  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         #
##########################################################################

topdir = ..

OTTVER=0.33

OCAMLFIND=ocamlfind
OCAMLARGS=-package str -package ocamlgraph -linkpkg

# for us
OCAMLC	 	= $(OCAMLFIND) ocamlc $(OCAMLARGS) -g -dtypes  # -w p disables partial match warnings
OCAMLOPT	= $(OCAMLFIND) ocamlopt $(OCAMLARGS) -w y -g -dtypes -unsafe -inline 9

# for releases
#OCAMLC	 	= $(OCAMLFIND) ocamlc $(OCAMLARGS) -g -w p -w y
#OCAMLOPT	= $(OCAMLFIND) ocamlopt $(OCAMLARGS) -w p -w y -unsafe -inline 9

OCAMLDEP 	= ocamldep
OCAMLLEX        = ocamllex
OCAMLYACC       = ocamlyacc

LATEX		= latex
DVIPS		= dvips
DVIPDFM		= dvipdfm

COQC            = coqc
COQ_INCLUDE     = -I $(topdir)/coq
COQ_FLAGS       =

# DO NOT EDIT BELOW THIS LINE ###########################################

SOURCES_LEXER_PARSER = grammar_lexer.mll grammar_parser.mly

SOURCES_NON_LEXER_PARSER1 = location.ml types.ml auxl.ml merge.ml global_option.ml

SOURCES_NON_LEXER_PARSER2 = grammar_pp.ml parse_table.ml glr.ml new_term_parser.ml term_parser.ml \
			    dependency.ml bounds.ml context_pp.ml \
	                    quotient_rules.ml grammar_typecheck.ml 		  \
			    transform.ml substs_pp.ml subrules_pp.ml				  \
			    embed_pp.ml defns.ml ln_transform.ml coq_induct.ml	  		  \
                            system_pp.ml lex_menhir_pp.ml align.ml main.ml




SOURCES_MLI =           \
  align.mli             \
  bounds.mli            \
  coq_induct.mli        \
  defns.mli             \
  dependency.mli        \
  embed_pp.mli          \
  grammar_typecheck.mli \
  merge.mli             \
  subrules_pp.mli       \
  substs_pp.mli         \
  system_pp.mli         \
  lex_menhir_pp.mli         \
  transform.mli		\
  term_parser.mli

SOURCES= $(SOURCES_NON_LEXER_PARSER1) 					\
         grammar_lexer.ml grammar_parser.mli grammar_parser.ml 		\
	 version.ml 							\
         $(SOURCES_NON_LEXER_PARSER2)

MLI 	= $(filter %.mli, $(SOURCES))
ML	= $(filter %.ml, $(SOURCES))

CMO 	= $(patsubst %.ml, %.cmo, $(ML))
CMX 	= $(patsubst %.cmo, %.cmx, $(CMO))

CMI_FROM_MLI = $(patsubst %.mli, %.cmi, $(SOURCES_MLI))


#default: ott.opt
default: ott.byt

all: default
ott: default


# compile and link Ott

byt: ott.byt

ott.byt: Makefile $(CMO) $(CMI_FROM_MLI) version.tex
	echo $^
	$(OCAMLC) -v
	$(OCAMLC) -o ott.byt $(CMO)
	ln -s -f $@ ott

.FORCE: opt
opt: ott.opt

ott.opt: Makefile $(CMX) $(CMI_FROM_MLI) version.tex
	echo $^
	$(OCAMLOPT) -v
	$(OCAMLOPT) -o ott.opt $(CMX)
	ln -s -f $@ ott

interfaces: $(ML:.ml=.interface)

mlis: $(ML:.ml=.mli)

# files that require a special treatment

grammar_lexer.ml: grammar_lexer.mll
	$(OCAMLLEX) grammar_lexer.mll

grammar_parser.ml grammar_parser.mli: grammar_parser.mly
	$(OCAMLYACC) -v grammar_parser.mly

grammar_typecheck.cmo: grammar_typecheck.ml
	$(OCAMLC) -c grammar_typecheck.ml

grammar_typecheck.cmx: grammar_typecheck.ml
	$(OCAMLOPT) -c grammar_typecheck.ml

glr.cmo: glr.ml
	$(OCAMLC) -c glr.ml

glr.cmx: glr.ml
	$(OCAMLOPT) -c glr.ml

parse_table.cmo: parse_table.ml
	$(OCAMLC) -c parse_table.ml

parse_table.cmx: parse_table.ml
	$(OCAMLOPT) -c parse_table.ml

new_term_parser.cmo: new_term_parser.ml
	$(OCAMLC) -c new_term_parser.ml

new_term_parser.cmx: new_term_parser.ml
	$(OCAMLOPT) -c new_term_parser.ml

dependency.cmo: dependency.ml
	$(OCAMLC) -c dependency.ml

dependency.cmx: dependency.ml
	$(OCAMLOPT) -c dependency.ml

#version.ml: Makefile tmp_date.txt
#	echo let n=\"$(OTTVER)\" > tmp_version1.ml
#	echo -n let d=\" > tmp_version2.ml
#	echo \" > tmp_version3.ml
#	cat tmp_version1.ml tmp_version2.ml tmp_date.txt tmp_version3.ml > version.ml
#	rm tmp_version1.ml tmp_version2.ml tmp_version3.ml

version.ml: tmp_date.txt Makefile #Makefile-core
	echo 'let n="$(OTTVER)"' >version.ml
	echo let d=\"$$(cat tmp_date.txt)\" >>version.ml

version.tex: tmp_date.txt version_src.tex Makefile
	sed -e 's/__VERSION__/$(OTTVER)/' \
	    -e '/__DATE__/r tmp_date.txt' \
	    -e '/__DATE__/d' <version_src.tex >version.tex
#	sed -e 's/__VERSION__/$(OTTVER)/' \
#	    -e "s/__DATE__/$$(cat tmp_date.txt)/" <version_src.tex >version.tex

# common rules

%.cmi: %.mli
	$(OCAMLC) -c $<

%.interface: %.ml
	$(OCAMLC) -i $< >$@

#%.mli: %.ml
#	$(OCAMLC) -i $< >$@

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

%.ps : %.dot
	dot -Tps $< > $@

%.png : %.dot
	dot -Tpng -Gsize="2,2" $< > $@

%.vo: %.v
	$(COQC) $(COQ_INCLUDE) $(COQ_FLAGS) $<

# INSTALL  ##############################################################

$(topdir)/bin:
	mkdir $(topdir)/bin

install.byt: $(topdir)/bin
	$(MAKE) byt
	cp ./ott $(topdir)/bin/ott

install: $(topdir)/bin
	$(MAKE) opt
	cp ./ott $(topdir)/bin/ott



# LIBRARY ##############################################################

coq-lib:
	cd $(topdir)/coq && $(MAKE) all


# GRAMMAR DOCS ##########################################################

# magic to tex-ify our yacc parser

Y2L=../aux/y2l/y2l  

%.mly-y2l : %.mly
	cat $< | tr -d \' | grep -v '%start' | grep -v '%type' | sed -e 's/%prec [^ ]*//' > $@

grammar_parser.tex : grammar_parser.mly-y2l  $(Y2L)
	$(Y2L) $< -O2  > $@
#
# not sure if the parser-tokens.y2l can be autogenerated or if we 
# have to write it by hand (hacking grammar_parser.mli
# (cf ../../Impl/acute/parser-tokens.y2l).  If omitting it, use
# the grammar_parser.tex rule above instead of this below
#
#%.tex : %.mly-y2l parser-tokens.y2l $(Y2L)
#	$(Y2L) $< -O2 -tparser-tokens.y2l > $@

grammar.ps : grammar.tex grammar_parser.tex
	$(LATEX) grammar.tex
	$(DVIPS) $(DVIPSOPTS) grammar.dvi


# EXAMPLES USED IN MANUAL ##############################################

tmp_test7_clean.ott: ../tests/test7.ott
	rm -f tmp_test7_clean.ott
	(grep -v ^a | sed -e 's/^r//g' | grep -v ^% ) < ../tests/test7.ott > tmp_test7_clean.ott
	chmod ugo-w tmp_test7_clean.ott


# DOT IMAGES FOR WEB PAGE  ###############################################

tmp_test7.ott: ../tests/test7.ott
	rm -f tmp_test7.ott
	(sed -e 's/^r//g') < ../tests/test7.ott > tmp_test7.ott
	chmod ugo-w tmp_test7.ott


test7: ott  tmp_test7.ott
	./ott  -o out.tex 						\
	       -dot tmp_test7_dot.dot 					\
	       -o out.thy -o outScript.sml -o out.v		\
	        -parse ":user_syntax: \x1':X.x1'"  			\
	        -parse ":user_syntax: :user_syntax__t: \x1':X.x1'"  	\
	        -parse ":user_syntax: :user_syntax__t: :concrete: \x1':X.x1'"  \
	        -parse ":user_syntax: :concrete: \x1':X.x1'"  		\
	        -parse ":concrete_t:\x1':X.x1'"                      	\
	        -parse ":Jop: match({l1=p1,..,lm=pm},{k1=v1,..,kn=vn}) = s1,..,sm" \
               tmp_test7.ott 						\
        && ($(LATEX) out; $(DVIPS) out -o; $(DVIPDFM) out)


%.ps : %.dot
	dot -Tps $< > $@

%.png : %.dot
	dot -Tpng -Gsize="2,2" $< > $@



#%.gif : %.dot
#	dot -Tgif -Gsize="2,2" $< > $@


# WEB PAGE INSTALL ###################################################


tmp_index.html: ../doc/index.html.p 
	cat ../doc/index.html.p | \
	sed -e "s/OTTVERSION/$(OTTVER)/g" > tmp_index.html

install-www-index: tmp_index.html 
	$(MAKE) test7
	$(MAKE) tmp_test7_dot.ps
	$(MAKE) tmp_test7_dot.png
	cp -f tmp_index.html ~/public_html/ott/index.html
	cp -f ../doc/style.css ~/public_html/ott
	cp -f ../doc/favicon.ico ~/public_html/ott
	cp -f ../revision_history.txt ~/public_html/ott
	cp -f ../README.md ~/public_html/ott/README.txt
	cp -f tmp_test7_dot.ps ~/public_html/ott/test7.dot.ps
	cp -f tmp_test7_dot.png ~/public_html/ott/test7.dot.png
	chmod ugo-w ~/public_html/ott/index.html
	chmod ugo-w ~/public_html/ott/style.css
	chmod ugo-w ~/public_html/ott/revision_history.txt



# CLEANUP ##############################################################

clean:
	rm -f *~ *.cmi *.cmo *.cmx *.o
	rm -f grammar_lexer.ml grammar_parser.ml 			\
              grammar_parser.mli grammar_parser.output
	rm -f version.ml
	rm -rf ott ott.byt ott.opt $(topdir)/bin/ott
	rm -f grammar_parser.tex *.mly-y2l
	rm -f *.aux *.log *.dvi *.ps *.pdf *.annot
	rm -f out.thy out.v outScript.sml outTheory.uo outTheory.ui outTheory.sig outTheory.sml out.tex out.sty 
	rm -f tmp_*.dot tmp.dot
	rm -f tmp_*.ott
	rm -f testRegr*
	rm -f *Theory.* *.ui *.uo

realclean:
	rm -f .depend
	cd $(topdir)/coq && $(MAKE) clean


# DEPENDENCIES ########################################################

foob:
	echo $(SOURCES)

depend:
	$(OCAMLDEP) $(SOURCES) $(SOURCES_MLI) > .depend
.depend: Makefile $(SOURCES) $(SOURCES_MLI)
	$(OCAMLDEP) $(SOURCES) $(SOURCES_MLI) > .depend

include .depend
