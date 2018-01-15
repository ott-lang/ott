DVIPSFLAGS = -Ppdf -j0 -G0 

all:
	latex poster && dvips $(DVIPSFLAGS) poster
	latex caml_typedef.tex && dvips $(DVIPSFLAGS) caml_typedef
