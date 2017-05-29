# rm -rf test10menhir_parser.mly && make -C ../.. && make

MENHIR          := menhir

MENHIRFLAGS     := --infer

OCAMLBUILD      := ocamlbuild -use-ocamlfind -use-menhir -menhir "$(MENHIR) $(MENHIRFLAGS)"

MAIN            := main

all: test10menhir_ast.ml test10menhir_parser.mly test10menhir_lexer.mll main.ml
	$(OCAMLBUILD) $(MAIN).native

test10menhir_ast.ml test10menhir_parser.mly test10menhir_lexer.mll: test10menhir.ott
	../../bin/ott -i test10menhir.ott -o test10menhir_ast.ml -o test10menhir_parser.mly -o test10menhir_lexer.mll

clean:
	rm -rf *~
	rm -rf test10menhir_ast.ml test10menhir_parser.mly test10menhir_lexer.mll
	$(OCAMLBUILD) -clean
