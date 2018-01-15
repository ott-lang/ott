DVIPSFLAGS = -Ppdf -j0 -G0 

all:
	latex poster && dvips $(DVIPSFLAGS) poster && ps2pdf poster.ps
	latex poster_rules.tex && dvips $(DVIPSFLAGS) poster_rules && ps2pdf poster_rules.ps

install_doc:
	cp poster.pdf built_doc
	cp poster_rules.pdf built_doc

clean:
	rm -rf *.aux *.dvi *.log
	rm -rf *~
	rm -rf poster_rules.ps poster_rules.pdf poster.ps poster.pdf
