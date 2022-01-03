#  make -C ../.. && make clean && make

ROOT            := test_if

OTTDIR          := ../../..

OTT             := $(OTTDIR)/bin/ott

MENHIR_EXTRA_LIB:= $(OTTDIR)/menhir/menhir_library_extra.mly

MENHIR          := menhir

MENHIRFLAGS     := --infer --explain --unused-tokens --trace --base $(ROOT)_parser

OCAMLBUILD      := ocamlbuild -use-ocamlfind -use-menhir -menhir "$(MENHIR) $(MENHIRFLAGS) ../$(MENHIR_EXTRA_LIB) " -package pprint

MAIN            := main

all: $(ROOT)_ast.ml $(ROOT)_parser.mly $(ROOT)_parser_pp.ml $(ROOT)_lexer.mll main.ml 
	$(OCAMLBUILD) $(MAIN).byte


pdf: $(ROOT)_quotiented.pdf $(ROOT)_unquotiented.pdf

# generate the ocaml AST type, ocamllex lexer, menhir parser, and ocaml pretty printers for the AST, all from the Ott soruce
$(ROOT)_ast.ml  $(ROOT)_lexer.mll $(ROOT)_parser.mly $(ROOT)_parser_pp.ml $(ROOT)_ast.tex : $(ROOT).ott
	$(OTT) -show_sort true -quotient_rules false -i $(ROOT).ott  -o $(ROOT)_parser.mly -o $(ROOT)_lexer.mll -o $(ROOT)_ast.ml -o $(ROOT).tex


$(ROOT)_quotiented.pdf: $(ROOT).ott Makefile
	$(OTT) -quotient_rules true -i $(ROOT).ott -o $(ROOT)_quotiented.tex
	pdflatex $(ROOT)_quotiented.tex

$(ROOT)_unquotiented.pdf: $(ROOT).ott Makefile
	$(OTT) -quotient_rules false -i $(ROOT).ott -o $(ROOT)_unquotiented.tex
	pdflatex $(ROOT)_unquotiented.tex

clean:
	rm -rf *~
	rm -rf _build
	rm -rf $(ROOT)_ast.ml $(ROOT)_parser.mly $(ROOT)_lexer.mll $(ROOT)_parser_pp.ml
	rm -rf *.aux *.log *.tex
	rm -rf main.native main.byte
	$(OCAMLBUILD) -clean

realclean:
	$(MAKE) clean
	rm -rf *.pdf