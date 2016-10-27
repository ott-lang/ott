LATEX  = latex
BIBTEX = bibtex
DVIPS  = dvips
PS2PDF = ps2pdf
OTT    = ../bin/ott

DVIPSFLAGS = -Ppdf -j0 -G0 
OTT_FLAGS := -tex_wrap false -signal_parse_errors true
OTT_FLAGS += -show_defns false

lj = lj_common.ott lj_base.ott lj.ott

.PHONY: manual clean

manual.pdf manual.ps: manual.tex ottlayout.sty lj_included.tex lj_override.tex
	$(LATEX) $< && $(BIBTEX) manual && $(LATEX) $< && $(LATEX) $<
	$(DVIPS) $(DVIPSFLAGS) manual && $(PS2PDF) manual.ps

lj_included.tex : $(lj)
	$(OTT) $(OTT_FLAGS) -tex_name_prefix lj -o $@ -merge true $(lj)

%_override.tex: override.tex empty.ott
	$(OTT) $(OTT_FLAGS) -tex_name_prefix lj -tex_filter $< $@ empty.ott

clean:
	@rm -f *~ *.{aux,bbl,blg,dvi,log,ps,pdf,sys,thy} \
               *_{included,override}.tex
