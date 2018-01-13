all:
	./process-tests.scm
	hol < make_ml.sml
	cp reduction_funML.BUGFIX.sml reduction_funML.sml
	sml < run_tests.sml

clean:
	rm -f caml_typedefML.sig caml_typedefML.sml defs_red_funML.sig defs_red_funML.sml matching_funML.sig matching_funML.sml ottML.sig ottML.sml reduction_funML.sig reduction_funML.sml testsML.sig testsML.sml tests.sml run_tests.sml
