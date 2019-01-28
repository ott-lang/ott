

aux_test: aux.1.ott
	../bin/ott -generate_aux_rules true -aux_style_rules false -o aux.1.ml -o Aux.thy $<


isa_ind: test19.2.ott
	../bin/ott  -isa_rewrite_defns true -o Test19.thy $<
	../bin/ott -o Test19Plain.thy $<

isa_ind_hand: test19.3.ott
	../bin/ott -o Test19Hand.thy $<

