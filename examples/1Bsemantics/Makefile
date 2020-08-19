
OTT=../../bin/ott

l1: l1.ott
	$(OTT) -pp_grammar -isa_syntax true l1.ott -o l1.tex -o l1.thy -o l1.lem
	$(OTT) -tex_wrap false l1.ott -o l1_nowrap.tex 
	pdflatex l1.tex
	lem l1.lem  -isa

l2: l1.ott l2.ott
	$(OTT) -merge true l1.ott l2.ott -o l2.tex -o l2.thy -o l2.tmp.lem
	pdflatex l2.tex
	(echo 'open import Pervasives' ; cat l2.tmp.lem) > l2.lem
	lem l2.lem -isa


clean:
	rm -rf *~
	rm -rf l1.tex l1.thy l1.lem l1_nowrap.tex L1.thy
	rm -rf l2.tex l2.thy l2.tmp.lem l2.lem l2.thy L2.thy
	rm -rf l1.aux l1.log l1.pdf
	rm -rf l2.aux l2.log l2.pdf
	rm -rf L1Auxiliary.thy L2Auxiliary.thy
