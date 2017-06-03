#  make -C ../.. && make clean && make


MENHIR          := menhir

MENHIRFLAGS     := --infer

OCAMLBUILD      := ocamlbuild -use-ocamlfind -use-menhir -menhir "$(MENHIR) $(MENHIRFLAGS)"

MAIN            := main

all: test10menhir_ast.ml test10menhir_parser.mly test10menhir_parser_pp.ml test10menhir_lexer.mll main.ml test10menhir_quotiented.pdf
	$(OCAMLBUILD) $(MAIN).native

# generate the ocaml AST type, ocamllex lexer, menhir parser, and ocaml pretty printers for the AST, all from the Ott soruce
test10menhir_ast.ml  test10menhir_lexer.mll test10menhir_parser.mly test10menhir_parser_pp.ml test10menhir_ast.tex : test10menhir.ott
	../../bin/ott -quotient_rules false -i test10menhir.ott  -o test10menhir_parser.mly -o test10menhir_lexer.mll -o test10menhir_ast.ml -o test10menhir.tex


test10menhir_quotiented.pdf: test10menhir.ott Makefile
	../../bin/ott -quotient_rules true -i test10menhir.ott -o test10menhir_quotiented.tex
	pdflatex test10menhir_quotiented.tex

clean:
	rm -rf *~
	rm -rf _build
	rm -rf test10menhir_ast.ml test10menhir_parser.mly test10menhir_lexer.mll test10menhir_parser_pp.ml
	rm -rf *.aux *.log *.pdf *.tex
	$(OCAMLBUILD) -clean
