
CAMLC=ocamlc
CAMLOPT=ocamlopt
COMPFLAGS=-warn-error A $(INCLUDES)
LINKFLAGS=

CAMLYACC=ocamlyacc
YACCFLAGS=-v
CAMLLEX=ocamllex
CAMLDEP=ocamldep
DEPFLAGS=$(INCLUDES)
CAMLRUN=ocamlrun
SHELL=/bin/sh
MKDIR=mkdir -p

INCLUDES=-I utils -I parsing 

UTILS=utils/misc.cmx utils/tbl.cmx utils/config.cmx \
  utils/clflags.cmx utils/terminfo.cmx utils/ccomp.cmx utils/warnings.cmx \
  utils/consistbl.cmx

OPTUTILS=$(UTILS)

PARSING=parsing/linenum.cmx parsing/location.cmx parsing/longident.cmx \
  parsing/syntaxerr.cmx parsing/parser.cmx \
  parsing/lexer.cmx parsing/parse.cmx parsing/printast.cmx 

FILES=$(UTILS) $(PARSING) main.cmx

filter: $(FILES) Makefile
	$(CAMLOPT) $(LINKFLAGS) -o filter $(FILES)


parsing/parser.mli parsing/parser.ml: parsing/parser.mly
	$(CAMLYACC) $(YACCFLAGS) parsing/parser.mly


parsing/lexer.ml: parsing/lexer.mll
	$(CAMLLEX) parsing/lexer.mll


parsing/linenum.ml: parsing/linenum.mll
	$(CAMLLEX) parsing/linenum.mll


.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(CAMLC) $(COMPFLAGS) -c $<

.mli.cmi:
	$(CAMLC) $(COMPFLAGS) -c $<

.ml.cmx:
	$(CAMLOPT) $(COMPFLAGS) -c $<

clean::
	rm -f utils/*.cm[iox] utils/*.[so] utils/*~
	rm -f parsing/*.cm[iox] parsing/*.[so] parsing/*~
	rm -f parsing/parser.ml parsing/parser.mli parsing/parser.output
	rm -f parsing/lexer.mli parsing/lexer.ml
	rm -f *.cm[iox] *.[so] *~ filter

depend: 
	(for d in utils parsing .; \
	 do $(CAMLDEP) $(DEPFLAGS) $$d/*.mli $$d/*.ml; \
	 done) > .depend

FORCE:

include .depend
