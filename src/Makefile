#########################################################################
#                                   Ott                                  #
#                                                                        #
#        Peter Sewell, Computer Laboratory, University of Cambridge      #
#      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     #
#                                                                        #
#  Copyright 2005-2011                                                   #
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

OTTVER=0.25

# for us
#OCAMLC	 	= ocamlc.opt -g -dtypes  # -w p disables partial match warnings
#OCAMLOPT	= ocamlopt.opt -w y -g -dtypes -unsafe -inline 9

# for releases
OCAMLC	 	= ocamlc -g -w p -w y 
OCAMLOPT	= ocamlopt -w p -w y -unsafe -inline 9

OCAMLDEP 	= ocamldep
OCAMLLEX        = ocamllex
OCAMLYACC       = ocamlyacc

LATEX		= latex
DVIPS		= dvips
DVIPDFM		= dvipdfm

COQC            = coqc
COQ_INCLUDE     = -I $(topdir)/coq
COQ_FLAGS       =
OCAMLGRAPHDIRBODY = ocamlgraph-1.7
OCAMLGRAPHDIR = ../$(OCAMLGRAPHDIRBODY)
OCAMLGRAPHTARGZ	= ocamlgraph-1.7.tar.gz
LIBRARIES	= str $(OCAMLGRAPHDIR)/graph

# DO NOT EDIT BELOW THIS LINE ###########################################

SOURCES_LEXER_PARSER = grammar_lexer.mll grammar_parser.mly

SOURCES_NON_LEXER_PARSER1 = location.ml types.ml auxl.ml merge.ml global_option.ml 

SOURCES_NON_LEXER_PARSER2 = grammar_pp.ml parse_table.ml glr.ml new_term_parser.ml term_parser.ml \
			    dependency.ml bounds.ml context_pp.ml grammar_typecheck.ml 		  \
			    transform.ml substs_pp.ml subrules_pp.ml				  \
			    embed_pp.ml defns.ml ln_transform.ml coq_induct.ml	  		  \
                            system_pp.ml lexyac_pp.ml align.ml main.ml 

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
  lexyac_pp.mli         \
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


default: ott.opt
#default: ott.byt

all: default
ott: default


# compile and link Ott

byt: ott.byt

ott.byt: Makefile $(CMO) $(CMI_FROM_MLI) version.tex
	echo $^
	$(OCAMLC) -v
	$(OCAMLC) -o ott.byt $(addsuffix .cma, $(LIBRARIES)) $(CMO)
	ln -s -f $@ ott

.FORCE: opt
opt: ott.opt

ott.opt: Makefile $(CMX) $(CMI_FROM_MLI) version.tex
	echo $^
	$(OCAMLOPT) -v
	$(OCAMLOPT) -o ott.opt $(addsuffix .cmxa, $(LIBRARIES)) $(CMX) 
	ln -s -f $@ ott

interfaces: $(ML:.ml=.interface)

mlis: $(ML:.ml=.mli)

# files that require a special treatment

grammar_lexer.ml: grammar_lexer.mll 
	$(OCAMLLEX) grammar_lexer.mll

grammar_parser.ml grammar_parser.mli: grammar_parser.mly
	$(OCAMLYACC) -v grammar_parser.mly  

grammar_typecheck.cmo: grammar_typecheck.ml
	$(OCAMLC) -c -I $(OCAMLGRAPHDIR) grammar_typecheck.ml

grammar_typecheck.cmx: grammar_typecheck.ml
	$(OCAMLOPT) -c -I $(OCAMLGRAPHDIR) grammar_typecheck.ml

glr.cmo: glr.ml
	$(OCAMLC) -c -I $(OCAMLGRAPHDIR) glr.ml

glr.cmx: glr.ml
	$(OCAMLOPT) -c -I $(OCAMLGRAPHDIR) glr.ml

parse_table.cmo: parse_table.ml
	$(OCAMLC) -c -I $(OCAMLGRAPHDIR) parse_table.ml

parse_table.cmx: parse_table.ml
	$(OCAMLOPT) -c -I $(OCAMLGRAPHDIR) parse_table.ml

new_term_parser.cmo: new_term_parser.ml
	$(OCAMLC) -c -I $(OCAMLGRAPHDIR) new_term_parser.ml

new_term_parser.cmx: new_term_parser.ml
	$(OCAMLOPT) -c -I $(OCAMLGRAPHDIR) new_term_parser.ml

dependency.cmo: dependency.ml
	$(OCAMLC) -c -I $(OCAMLGRAPHDIR) dependency.ml

dependency.cmx: dependency.ml
	$(OCAMLOPT) -c -I $(OCAMLGRAPHDIR) dependency.ml

#version.ml: Makefile tmp_date.txt
#	echo let n=\"$(OTTVER)\" > tmp_version1.ml
#	echo -n let d=\" > tmp_version2.ml
#	echo \" > tmp_version3.ml
#	cat tmp_version1.ml tmp_version2.ml tmp_date.txt tmp_version3.ml > version.ml
#	rm tmp_version1.ml tmp_version2.ml tmp_version3.ml

version.ml: tmp_date.txt #Makefile-core 
	echo 'let n="$(OTTVER)"' >version.ml
	echo let d=\"$$(cat tmp_date.txt)\" >>version.ml

version.tex: tmp_date.txt version_src.tex
	sed -e 's/__VERSION__/$(OTTVER)/' \
	    -e '/__DATE__/r tmp_date.txt' \
	    -e '/__DATE__/d' <version_src.tex >version.tex
#	sed -e 's/__VERSION__/$(OTTVER)/' \
#	    -e "s/__DATE__/$$(cat tmp_date.txt)/" <version_src.tex >version.tex

# common rules

%.cmi: %.mli
	$(OCAMLC) -I $(OCAMLGRAPHDIR) -c $<

%.interface: %.ml
	$(OCAMLC) -I $(OCAMLGRAPHDIR) -i $< >$@

#%.mli: %.ml
#	$(OCAMLC) -I $(OCAMLGRAPHDIR) -i $< >$@

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -I $(OCAMLGRAPHDIR) -c $<

%.ps : %.dot
	dot -Tps $< > $@

%.png : %.dot
	dot -Tpng -Gsize="2,2" $< > $@

%.vo: %.v
	$(COQC) $(COQ_INCLUDE) $(COQ_FLAGS) $<

# INSTALL  ##############################################################

## Rules to unpack and build our copy of ocamlgraph.
$(OCAMLGRAPHDIR)/Makefile:
	cd .. && tar -zxvf $(OCAMLGRAPHTARGZ)
	cd $(OCAMLGRAPHDIR) && ./configure
$(OCAMLGRAPHDIR)/graph.cma: $(OCAMLGRAPHDIR)/Makefile
	cd $(OCAMLGRAPHDIR) && $(MAKE) graph.cma
$(OCAMLGRAPHDIR)/graph.cmxa: $(OCAMLGRAPHDIR)/Makefile
	cd $(OCAMLGRAPHDIR) && \
	$(MAKE) OCAMLOPT='$(OCAMLOPT) -I src -I lib' graph.cmxa
# The extra `-I' options when building graph.cmxa work around OCaml
# PR#4124 (present in OCaml 3.09.*).
ocamlgraph: $(OCAMLGRAPHDIR)/graph.cma $(OCAMLGRAPHDIR)/graph.cmxa

install.byt: $(OCAMLGRAPHDIR)/graph.cma
	$(MAKE) byt
	cp ./ott ../bin/ott

install: $(OCAMLGRAPHDIR)/graph.cmxa
	$(MAKE) opt
	cp ./ott ../bin/ott



# LIBRARY ##############################################################

coq-lib:
	cd ../coq && $(MAKE) all

# CLEANUP ##############################################################

clean:
	rm -f *~ *.cmi *.cmo *.cmx *.o 
	rm -f grammar_lexer.ml grammar_parser.ml 			\
              grammar_parser.mli grammar_parser.output 
	rm -f version.ml
	rm -rf ott ott.byt ott.opt ../bin/ott
	rm -f grammar_parser.tex *.mly-y2l
	rm -f *.aux *.log *.dvi *.ps *.pdf *.annot
	rm -f out.thy out.v outScript.sml outTheory.uo outTheory.ui outTheory.sig outTheory.sml out.tex out.sty 
	rm -f tmp_*.dot tmp.dot
	rm -f tmp_*.ott
	rm -f testRegr*
	rm -f *Theory.* *.ui *.uo

realclean:
	rm -f .depend
	cd ../coq && $(MAKE) clean


# DEPENDENCIES ########################################################

foob:
	echo $(SOURCES)

depend:
	$(OCAMLDEP) $(SOURCES) $(SOURCES_MLI) > .depend
.depend: Makefile $(SOURCES) $(SOURCES_MLI) 
	$(OCAMLDEP) $(SOURCES) $(SOURCES_MLI) > .depend

include .depend
