## Default target: run ott, and typeset the spec.
default: ott ps pdf
## Run ott, and compile the spec in proof assistants (Coq, HOL and Isabelle).
all: default coq-def hol-def isa-def
## Build everything. Requires Coq, Isabelle, and HOL.
## See hol/README for HOL version requirement.
world: all hol-proof


lemtest: 
	make -C ../../src
	make caml_typedef.lem
	~/bitbucket/lem/lem  -wl_unused_vars ign -ocaml caml_typedef.lem



#### Options for ott hackers ####
## Run `make separate_ott_runs=1' to run a separate ott process for
## each output languages (slower, but sometimes useful in case of
## language-specific bugs in ott).
separate_ott_runs =

#### General targets ####
ott: caml_typedef.tex caml_typedef.v caml_typedefScript.sml caml_typedef.thy
ps: caml_typedef.ps
pdf: caml_typedef.pdf
coq-def: caml_typedef.vo
hol-def: caml_typedefTheory.uo hol_caml
isa-def: caml_typedef.isa
coq: coq-def
hol: hol-def
isa: isa-def
hol-proof: hol/definitionsTheory.uo hol/defs_red_funTheory.uo

install_doc: caml_typedef.pdf
	cp caml_typedef.pdf doc/built_doc

#### Directories ####
############ CHANGE topdir TO REFER TO YOUR TOP LEVEL OTT INSTALLATION ########
topdir = ../..
#/home/so294/scratch/ott_distro_0.10.13
ott_coq_lib_dir = $(topdir)/coq
ott_hol_lib_dir = $(topdir)/hol
poly_lib = /Users/so294/polyml.5.1/lib

#### Programs and their arguments ####
COQC = coqc
#COQ_INCLUDE = -I $(ott_coq_lib_dir)
COQ_INCLUDE = -R $(ott_coq_lib_dir) Ott
COQ_FLAGS =
DVIPS = dvips
DVIPSFLAGS = -Ppdf -j0 -G0
HOLMAKE = Holmake
HOLMAKE_INCLUDE = -I $(ott_hol_lib_dir)
HOLMAKE_FLAGS = --qof
ISABELLE = isabelle
ISABELLE_FLAGS = -q
ISABELLE_WRAPPER = use_thy "$*" handle e => (TextIO.output (TextIO.stdErr, "Isabelled failed: " ^ exnMessage e ^ "\n"); OS.Process.exit OS.Process.failure)
LATEX = latex
OTT = $(topdir)/src/ott
#OTT = $(topdir)/bin/ott
OTT_COMMON_FLAGS = -pp_grammar -tex_show_categories true -coq_expand_list_types false -isa_generate_lemmas false
## Run `make OTT_VERBOSITY_FLAGS= target' to cause ott to spew out a
## lot of debugging output.
OTT_VERBOSITY_FLAGS = -show_defns false  -tex_show_categories true
#-show_post_sort false
OTT_FLAGS = -no_rbcatn true $(OTT_COMMON_FLAGS) $(OTT_VERBOSITY_FLAGS)
# -lem_debug true 
PS2PDF = ps2pdf

#### Preprocessing ####
caml_sources = syntax typing reduction
caml_combinations = \
	caml_plain caml_module caml_module_typedef caml_typedef

## Extract the desired language fragment
caml_plain_%.ott: %.ott
	cat $< >$@.tmp
	mv -f $@.tmp $@
caml_module_%.ott: %.ott
	sed -e 's/\(\(%[^%]\)*\)%m/\1/' $< >$@.tmp
	mv -f $@.tmp $@
caml_typedef_%.ott: %.ott
	sed -e 's/\(\(%[^%]\)*\)%d/\1/' $< >$@.tmp
	mv -f $@.tmp $@
caml_module_typedef_%.ott: %.ott
	sed -e 's/\(\(%[^%]\)*\)%d/\1/' -e 's/\(\(%[^%]\)*\)%m/\1/' $< >$@.tmp
	mv -f $@.tmp $@

## Multiple extraction targets
caml_%.ott: caml_%_syntax.ott caml_%_typing.ott caml_%_reduction.ott ;

#### Ott ####
ifeq ($(separate_ott_runs),)
## One ott run to produce everything
caml%.rawtex caml%.v caml%Script.sml caml%.thy caml%.lem: \
  caml%_syntax.ott caml%_typing.ott caml%_reduction.ott $(OTT)
	# Note: no protection against interruptions for hol and isabelle,
	# because ott requires a file name ending in Script.sml.
	$(OTT) $(OTT_FLAGS)  -o caml$*.tmp.tex -o caml$*.tmp.v -o caml$*Script.sml -o caml$*.thy -o caml$*.lem caml$*_syntax.ott caml$*_typing.ott caml$*_reduction.ott
	mv -f caml$*.tmp.tex caml$*.rawtex
	mv -f caml$*.tmp.v caml$*.v
else
## Separate ott runs, one per target
caml%.rawtex: caml%_syntax.ott caml%_typing.ott caml%_reduction.ott $(OTT)
	$(OTT) $(OTT_FLAGS) -o $@ $(@:.tex=)_syntax.ott $(@:.tex=)_typing.ott $(@:.tex=)_reduction.ott
#	mv -f $@.tmp $@
caml%Script.sml: caml%_syntax.ott caml%_typing.ott caml%_reduction.ott $(OTT)
	# Note: no protection against interruptions, because ott requires
	# a file name ending in Script.sml.
	$(OTT) $(OTT_FLAGS) -o $@ $(@:Script.sml=)_syntax.ott $(@:Script.sml=)_typing.ott $(@:Script.sml=)_reduction.ott
caml%.thy: caml%_syntax.ott caml%_typing.ott caml%_reduction.ott $(OTT)
	# Note: no protection against interruptions, because ott requires
	# a file name ending in .thy.
	$(OTT) $(OTT_FLAGS) -o $@ $(@:.thy=)_syntax.ott $(@:.thy=)_typing.ott $(@:.thy=)_reduction.ott
caml%.v: caml%_syntax.ott caml%_typing.ott caml%_reduction.ott $(OTT)
	$(OTT) $(OTT_FLAGS) -coq_expand_list_types false -o $@ $(@:.v=)_syntax.ott $(@:.v=)_typing.ott $(@:.v=)_reduction.ott
#	mv -f $@.tmp $@
caml%.lem: caml%_syntax.ott caml%_typing.ott caml%_reduction.ott $(OTT)
	$(OTT) $(OTT_FLAGS)  -o $@ $(@:.v=)_syntax.ott $(@:.v=)_typing.ott $(@:.v=)_reduction.ott
#	mv -f $@.tmp $@
endif

caml%.grammar: caml%_syntax.ott caml%_typing.ott caml%_reduction.ott $(OTT)
	$(OTT) $(OTT_FLAGS) -writesys $@.tmp $(@:.grammar=)_syntax.ott $(@:.grammar=)_typing.ott $(@:.grammar=)_reduction.ott
	mv -f $@.tmp $@

$(OTT): %:
#	cd $(@D) && $(MAKE) $(@F)

## Generate all combinations
caml_combinationsScript.sml: $(caml_combinations:=Script.sml) ;
caml_combinations.dvi: $(caml_combinations:=.dvi) ;
caml_combinations.pdf: $(caml_combinations:=.pdf) ;
caml_combinations.ps: $(caml_combinations:=.ps) ;
caml_combinations.tex: $(caml_combinations:=.tex) ;
caml_combinations.thy: $(caml_combinations:=.thy) ;
caml_combinations.v: $(caml_combinations:=.v) ;

#### TeX ####
%.tex: %.rawtex ott-preamble.sed
	sed -f ott-preamble.sed <$< >$@.tmp
	mv -f $@.tmp $@

.SUFFIXES: .tex .dvi .ps .pdf
.tex.dvi:
	$(LATEX) $<
	$(LATEX) $<
	$(LATEX) $<
.dvi.ps:
	$(DVIPS) $(DVIPS_FLAGS) -o $@ $<
.ps.pdf:
	$(PS2PDF) $< $@

#### Coq ####
coq_libs = $(ott_coq_lib_dir)/ott_list
coq-libs: $(coq_libs:=.vo)
$(coq_libs:=.vo): %:
	cd $(@D) && $(MAKE) $(@F)
.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $(COQ_INCLUDE) $(COQ_FLAGS) $<

#### Hol ####
dummy:

hol_caml.o: caml_typedefTheory.uo hol_caml.ML
	hol.builder < hol_caml.ML

hol_caml: hol_caml.o
	cc -L$(poly_lib) -o hol_caml -lpolymain -lpolyml hol_caml.o

hol_libs = $(topdir)/hol/ottLib $(topdir)/hol/ottTheory
hol-libs: $(hol_libs:=.ui) $(hol_libs:=.uo)
$(hol_libs:=.ui) $(hol_libs:=.uo): %:
	cd $(@D) && $(MAKE) $(@F)
%Theory.uo: %Script.sml hol-libs
	$(HOLMAKE) $(HOLMAKE_INCLUDE) $(HOLMAKE_FLAGS) $@
hol/Holmakefile: Makefile
	rm -f hol/Holmakefile
	echo INCLUDES = .. ../$(ott_hol_lib_dir) > hol/Holmakefile
hol/testing/Holmakefile: Makefile
	rm -f hol/testing/Holmakefile
	echo INCLUDES = .. ../.. $(ott_hol_lib_dir) > hol/testing/Holmakefile
hol/definitionsTheory.uo: caml_typedefTheory.uo hol/Holmakefile hol/testing/Holmakefile dummy hol-def
	cd $(@D) && $(HOLMAKE) $(HOLMAKE_FLAGS) --poly ../hol_caml $(@F)
hol/defs_red_funTheory.uo: caml_typedefTheory.uo hol/Holmakefile hol/testing/Holmakefile dummy hol-def
	cd $(@D) && $(HOLMAKE) $(HOLMAKE_FLAGS) --poly ../hol_caml $(@F)

hol/ocamlpp/filter:
	cd $(@D) && $(MAKE) $(@F)

#### Isabelle ####
.SUFFIXES: .thy .isa
.thy.isa:
	$(ISABELLE) $(ISABELLE_FLAGS) -e '$(ISABELLE_WRAPPER)'
	touch $@ # TODO: can Isabelle produce a proof trace of some kind?

#### Cleanup ####
clean:
	rm -f *.grammar *.rawtex
	rm -f *.aux *.dvi *.lof *.log *.lot *.ps *.pdf *.toc
	rm -f *.vo *.ui *.uo *.isa
	rm -f $(caml_combinations:=_syntax.ott) $(caml_combinations:=_typing.ott) $(caml_combinations:=_reduction.ott)
	rm -f $(caml_combinations:=.tex) $(caml_combinations:=Script.sml) $(caml_combinations:=.thy) $(caml_combinations:=.v)
	rm -f *Theory.sig *Theory.sml
	rm -f *.tmp tmp.* hol_caml
	rm -rf .HOLMK
	rm -rf *~

#### Dependencies ####
## Ott preprocessed sources
$(caml_combinations:=_syntax.ott):
$(caml_combinations:=_typing.ott):
$(caml_combinations:=_reduction.ott):
## Ott output
$(caml_combinations:=.rawtex): $(OTT)
$(caml_combinations:=.tex): $(OTT)
$(caml_combinations:=.dvi): ott-spec.ltx
$(caml_combinations:=.v): $(OTT)
$(caml_combinations:=Script.sml): $(OTT)
$(caml_combinations:=.thy): $(OTT)
## Coq
$(caml_combinations:=.vo): caml_lib_misc.vo
caml_base.vo: caml_base.v caml_typedef.vo
caml_examples_adhoc_1.vo: caml_examples_adhoc_1.v caml_typedef.vo caml_base.vo

#### The End ####
