LATEX		= latex
DVIPS		= dvips
DVIPSFLAGS = -Ppdf -j0 -G0 -t a4
#DVIPSFLAGS = -Ppdf -j0 -G0 -t letter


FIGURES=ich_fig0 ich_fig1
#ich_fig_FIG_OPTS=-m 0.55
FIGURE_PSTEX_TS=$(addsuffix .pstex_t, $(FIGURES))


# to make manual for new release:
#     bump new version in ../Makefile
#     date > tmp_date.txt  in ../src/
#     make in .. to rebuild version.tex
#     make install-top2-built
#     make install-web-files



all: top2.html top2.ps top2.pdf

clean::
	rm -f *.aux *.log *.dvi  *.annot top.doc top.tex top.ps top.pdf top2.ps top2.pdf top2.ggl top2.blg top2.html top2.image.tex top2.tex bind-doc.pdf bind-doc.ps bind-wmm-2.bbl bind-wmm-2.blg bind-wmm-2.pdf bind-wmm-2.ps  paper.bbl paper.blg paper.tex s
	rm -f bind-doc-2.ps bind-doc-2.pdf bind-2.tex bind-2.thy
	rm -f binding.1.aux  binding.1.tex  binding.2.aux  binding.2.tex  binding.3.aux  binding.3.tex  binding.4.aux  binding.4.tex  binding.5.aux   binding.5.tex  binding.6.alltt.tex  binding.6b.aux  binding.6b.tex  binding.6bScript.sml
	rm -f test10.0.alltt test10.2.aux test10.4.alltt test10.aux test10.meta.tex test10.tex test10.v test10_homs.alltt test10st.tex test10.2.alltt test10.2.tex test10.7.alltt test10.meta.aux test10.ml test10.thy test10Script.sml test10st.aux test21.1.alltt
	rm -f test11.alltt test12.thy test12.v test13.aux test13.tex test13d.aux test13d.tex test17.10.aux test17.10.tex test7tt.mng.alltt.tex
	rm -f slides-arg.dvi
	rm -f slides-sl.dvi 
	rm -f slides-icfp.dvi
	rm -f slides-parsec.dvi 
	rm -f grammar_parser.tex *.mly-y2l grammar_parser_hevea.tex
	rm -f top2*.gif top2.haux top2.htoc top2.lof 
	rm -f squishtex.hand.alltt.tex
	rm -f options.txt test7.tex test7afilter.out.ps test7tt.tex test8.tex tmp.dot tmp_0.dot tmp_1.dot tmp_2.dot top.toc top2.bbl top2.toc version.tex x.tex
	rm -f bind.tex bind.thy
	rm -f test10_tuple.tex test10_tuple.thy test10_tuple.v test10_tupleScript.sml test10b.tex test10b.thy test10b.v test10bScript.sml test10st_narrow.tex test10st_narrow.thy test10st_narrow.v test10st_narrowScript.sml
	rm -f test10.alltt.tex test10_html.html 
	rm -f README.tex
	rm -f *~

realclean::
	rm -f .depend


test1.tex: ../src/ott  ../tests/test1.ott
	../src/ott  -colour true -showraw true  			\
	       -o test1.tex						\
	       -tex_show_meta true                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testOne					\
                ../tests/non_super_tabular.ott ../tests/test1.ott                                      

test8.tex: ../src/ott  ../tests/test8.ott
	../src/ott  -colour true -showraw true  			\
	       -o test8.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testEight					\
                ../tests/non_super_tabular.ott ../tests/test8.ott                                      


test10.lem test10.tex: ../src/ott  ../tests/test10.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTen					\
	       -o test10.thy 					\
	       -o test10.v 						\
	       -o test10Script.sml                                    \
	       -o test10.lem                                    \
	       -o test10.ml                                         \
                ../tests/non_super_tabular.ott ../tests/test10.ott                                      

test10_poster.tex: ../src/ott  ../tests/test10_poster.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10_poster.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTenPoster					\
	       -o test10_poster.thy 					\
	       -o test10_poster.v 						\
	       -o test10_posterScript.sml                                    \
	       -o test10_poster.ml                                         \
                ../tests/non_super_tabular.ott ../tests/test10_poster.ott                                      
test10.despaced.v: test10.tex
	cat test10.v | sed -e 's/\n\n/\n/g' > test10.despaced.v

test10.2.tex: ../src/ott  ../tests/non_super_tabular.ott ../tests/test10.2.ott 
	../src/ott  -colour true -showraw true    \
	       -o test10.2.tex                  \
	       -tex_show_meta false               \
	       -tex_wrap false                    \
	       -tex_name_prefix	testTenTwo        \
                ../tests/non_super_tabular.ott  ../tests/test10.2.ott                                      

test10.2.ps: ../src/ott  ../tests/test10.2.ott
	../src/ott  -colour true -showraw true    \
	       -o test10.2.tex                  \
	       -tex_show_meta false               \
	       -tex_wrap true                    \
	       -tex_name_prefix	testTenTwo        \
                ../tests/non_super_tabular.ott ../tests/test10.2.ott                                      
	latex test10.2 && dvips test10.2


test10.0.alltt: ../src/ott ../tests/test10.0.ott 
	../src/ott -alltt test10.0.alltt ../tests/test10.0.ott
test10.2.alltt: ../src/ott ../tests/test10.2.ott 
	../src/ott -alltt test10.2.alltt ../tests/test10.2.ott
test10.4.alltt: ../src/ott ../tests/test10.4.ott 
	../src/ott -alltt test10.4.alltt ../tests/test10.4.ott
test10.7.alltt: ../src/ott ../tests/test10.7.ott 
	../src/ott -alltt test10.7.alltt ../tests/test10.7.ott

test10.alltt.tex: ../src/ott ../tests/test10.ott 
	../src/ott -alltt test10.alltt.tex ../tests/test10.ott

test22.1.alltt.tex: ../src/ott ../tests/test22.1.ott 
	../src/ott -alltt test22.1.alltt.tex ../tests/test22.1.ott

test10_poster.alltt.tex: ../src/ott ../tests/test10_poster.ott 
	../src/ott -alltt test10_poster.alltt.tex ../tests/test10_poster.ott

test10_html.html: test10.alltt.tex test10_html.tex
	hevea -fix test10_html.tex

test11.alltt: ../src/ott ../tests/test11.ott 
	../src/ott -alltt test11.alltt ../tests/test11.ott

test10_homs.alltt: ../src/ott ../tests/test10_homs.ott 
	../src/ott -alltt test10_homs.alltt ../tests/test10_homs.ott

test20.0.alltt: ../src/ott ../tests/test20.0.ott 
	../src/ott -alltt test20.0.alltt ../tests/test20.0.ott

test21.1.alltt: ../src/ott ../tests/test21.1.ott 
	../src/ott -alltt test21.1.alltt ../tests/test21.1.ott

test22.0.alltt: ../src/ott ../tests/test22.0.ott 
	../src/ott -alltt test22.0.alltt ../tests/test22.0.ott

binding.6.alltt.tex: ../src/ott ../tests/binding.6.ott
	../src/ott -alltt binding.6.alltt.tex ../tests/binding.6.ott

squishtex.hand.alltt.tex: ../src/ott squishtex.hand.ott
	../src/ott -alltt squishtex.hand.alltt.tex squishtex.hand.ott

##let.alltt.tex: ../src/ott ../examples/tapl/let.ott
##	../src/ott -alltt let.alltt.tex ../examples/tapl/common.ott ../examples/tapl/common_typing.ott.. /examples/tapl/let.ott

# commented out, as running this - while producing the output we need - also produces an error.  It's not a well-formed standalone file.
#let.alltt.tex: ../src/ott ../examples/tapl/let.ott
#	../src/ott -alltt let.alltt.tex ../examples/tapl/let.ott



test10_tuple.tex: ../src/ott  ../tests/test10_tuple.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10_tuple.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTentuple					\
	       -o test10_tuple.thy 					\
	       -o test10_tuple.v 						\
	       -o test10_tupleScript.sml                                    \
                ../tests/non_super_tabular.ott ../tests/test10_tuple.ott                                      

test10b.tex: ../src/ott  ../tests/test10b.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10b.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTenb					\
	       -o test10b.thy 					\
	       -o test10b.v 						\
	       -o test10bScript.sml                                    \
               ../tests/test10b.ott

test10c.tex: ../src/ott  ../tests/test10c.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10c.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTenc					\
	       -o test10c.thy 					\
	       -o test10c.v 						\
	       -o test10cScript.sml                                    \
                ../tests/non_super_tabular.ott ../tests/test10c.ott                                      

test10st_narrow.tex: ../src/ott  ../tests/test10st_narrow.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10st_narrow.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTenstnarrow					\
	       -o test10st_narrow.thy 					\
	       -o test10st_narrow.v 						\
	       -o test10st_narrowScript.sml                                    \
                ../tests/non_super_tabular.ott ../tests/test10st_narrow.ott                                      

test10.meta.tex: ../src/ott  ../tests/test10.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10.meta.tex						\
	       -tex_show_meta true                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTenMeta					\
                ../tests/non_super_tabular.ott ../tests/test10.ott                                      

test10st.tex: ../src/ott  ../tests/test10st.ott
	../src/ott  -colour true -showraw true  			\
	       -o test10st.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testTenst					\
                ../tests/non_super_tabular.ott ../tests/test10st.ott                                      
#	       -o test10.thy 						\
#	       -o test10.v 						\

test7.tex: ../src/ott ../tests/test7.ott ../tests/test7tt.mng
	cd ../src; make tmp_test7_clean.ott
	../src/ott                                 			\
	       -o test7.tex						\
	       -tex_show_meta false                                     \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testSeven				\
               -tex_filter ../tests/test7tt.mng test7tt.tex               \
                ../tests/non_super_tabular.ott ../src/tmp_test7_clean.ott

test7tt.mng.alltt.tex: ../tests/test7tt.mng
	cat ../tests/test7tt.mng | sed -e 's/\\/BACKSLASH/g' | sed -e 's/{/LEFTBRACKET/g' | sed -e 's/}/\\myrb\{\}/g' | sed -e 's/LEFTBRACKET/\\mylb\{\}/g' | sed -e 's/BACKSLASH/\\mybackslash\{\}/g'  | sed -e 's/\[\[/\\mysym{\[\[}/g' | sed -e 's/\]\]/\\mysym{\]\]}/g' | sed -e 's/:concrete:/\\mykw\{:concrete:\}/g' > test7tt.mng.alltt.tex

#	cat ../tests/test7tt.mng | sed -e 's/{/\\mylb\{\}/g' | sed -e 's/}/\\myrb\{\}/g' | sed -e 's/\[\[/\\mysym\{\[\[\}/g' | sed -e 's/\]\]/\\mysym\{\]\]\}/g' | sed -e 's/\\/\\mybackslash\{\}/g' | sed -e 's/:concrete:/\\mykw\{:concrete\}/g' > test7tt.mng.alltt.tex



test12.thy: ../src/ott  ../tests/test12.ott
	../src/ott  -colour true -showraw true  			\
	       -o test12.thy 						\
	       -o test12.v 						\
	       ../tests/test12.ott

test13.tex: ../src/ott  ../tests/test13.ott
	../src/ott  -colour true -showraw true  			\
	       -o test13.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testThirteen					\
                ../tests/non_super_tabular.ott ../tests/test13.ott                                      
#	       -o test10.thy 						\
#	       -o test10.v 						\

test13d.tex: ../src/ott  ../tests/test13d.ott
	../src/ott  -colour true -showraw true  			\
	       -o test13d.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testThirteend					\
	        ../tests/squishtex.ott \
                ../tests/test13d.ott                                      
#	       -o test10.thy 						\
#	       -o test10.v 						\

test17.10.tex: ../src/ott  ../tests/test17.10.ott
	../src/ott  -colour true -showraw true  			\
	       -o test17.10.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	testSeventeenTen			\
	        ../tests/non_super_tabular.ott  \
                ../tests/test17.10.ott                                      

binding.1.tex: ../src/ott  ../tests/binding.1.ott ../tests/squishtex.ott
	../src/ott  -colour true -showraw true  			\
	       -o binding.1.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	bindingOne					\
	        ../tests/squishtex.ott \
                ../tests/binding.1.ott                                      

binding.2.tex: ../src/ott  ../tests/binding.2.ott ../tests/squishtex.ott
	../src/ott  -colour true -showraw true  			\
	       -o binding.2.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	bindingTwo					\
	        ../tests/squishtex.ott \
                ../tests/binding.2.ott                                      

binding.3.tex: ../src/ott  ../tests/binding.3.ott ../tests/squishtex.ott
	../src/ott  -colour true -showraw true  			\
	       -o binding.3.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	bindingThree					\
	        ../tests/squishtex.ott \
                ../tests/binding.3.ott                                      

binding.4.tex: ../src/ott  ../tests/binding.4.ott ../tests/squishtex.ott
	../src/ott  -colour true -showraw true  			\
	       -o binding.4.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	bindingFour					\
	        ../tests/squishtex.ott \
                ../tests/binding.4.ott                                      

binding.5.tex: ../src/ott  ../tests/binding.5.ott ../tests/squishtex.ott
	../src/ott  -colour true -showraw true  			\
	       -o binding.5.tex						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	bindingFive					\
	        ../tests/squishtex.ott \
                ../tests/binding.5.ott                                      

binding.6b.tex: ../src/ott  ../tests/binding.6.ott ../tests/binding.6b.ott ../tests/squishtex.ott
	../src/ott  -colour true -showraw true  			\
	       -o binding.6b.tex						\
	       -o binding.6bScript.sml						\
	       -tex_show_meta false                                      \
	       -tex_wrap false                                          \
	       -tex_name_prefix	bindingSixb					\
	        ../tests/squishtex.ott \
                ../tests/binding.6.ott                                      \
                ../tests/binding.6b.ott                                      

## Binding
bind.tex: ../src/ott ../tests/bind-*.ott 
	../src/ott -o bind.tex \
               -tex_show_meta false \
               -tex_wrap false \
               -tex_name_prefix bind \
               -merge true \
               -o bind.thy \
               ../tests/bind-*.ott 


bind-doc.ps: bind.tex bind-doc.tex
	latex bind-doc.tex; latex bind-doc.tex; dvips $(DVIPSFLAGS) bind-doc

bind-2.tex: ../src/ott ../tests/bind2-*.ott 
	../src/ott -o bind-2.tex \
               -tex_show_meta false \
               -tex_wrap false \
               -tex_name_prefix bind \
               -merge true \
               -o bind2.thy \
               -o bind2Script.sml \
               -o bind2.v \
               ../tests/bind2-*.ott 

bind-doc-2.ps: bind-2.tex bind-doc-2.tex
	latex bind-doc-2.tex; latex bind-doc-2.tex; dvips $(DVIPSFLAGS) bind-doc-2

bind-wmm.ps: bind-wmm.tex bindbib.bib
	latex bind-wmm; bibtex bind-wmm; latex bind-wmm; latex bind-wmm; dvips $(DVIPSFLAGS) bind-wmm

bind-wmm-2.ps: bind-wmm-2.tex bindbib.bib
	latex bind-wmm-2; bibtex bind-wmm-2; latex bind-wmm-2; latex bind-wmm-2; dvips $(DVIPSFLAGS) bind-wmm-2


options.txt: ../src/ott
	../src/ott -help > options.txt

top.tex: top.mng
	cp -f top.mng top.tex # placeholder for later use of ott as a filter
	chmod ugo-w top.tex

top2.tex: top2.mng
	cp -f top2.mng top2.tex # placeholder for later use of ott as a filter
	chmod ugo-w top2.tex


grammar_parser.tex: ../src/grammar_parser.mly
	cd ../src; make grammar_parser.tex
	cp -f ../src/grammar_parser.tex .

grammar_parser_hevea.tex: grammar_parser.tex
	cat grammar_parser.tex | sed -e 's/longtable/tabular/g' > grammar_parser_hevea.tex

top.ps: top.tex test7.tex test8.tex test10.tex test10.hand.edited.thy  test10.hand.edited.v grammar_parser.tex test10.meta.tex test13.tex options.txt test10st.tex test12.thy ../src/version.tex test17.10.tex
	latex top;latex top;dvips $(DVIPSFLAGS) top

TOP2DEPS = top2.tex test7.tex test8.tex test10.tex test10.hand.edited.thy  test10.hand.edited.v grammar_parser.tex test10.meta.tex test13.tex options.txt test10st.tex test12.thy ../src/version.tex test17.10.tex test10.0.alltt test10.2.alltt test10.4.alltt test10.7.alltt README.tex test10.2.tex test7tt.mng.alltt.tex binding.1.tex binding.2.tex binding.3.tex  binding.4.tex binding.5.tex  binding.6.alltt.tex binding.6b.tex test11.alltt test10_homs.alltt let.alltt.tex grammar_parser_hevea.tex grammar_parser.tex squishtex.hand.alltt.tex test13d.tex test10.despaced.v shorter.bib test21.1.alltt

top2.ps: $(TOP2DEPS) 
	latex top2 && bibtex top2 && latex top2 && latex top2 && dvips $(DVIPSFLAGS) top2

top2.pdf: top2.ps
	ps2pdf $<

top2.html: $(TOP2DEPS)
	hevea -fix top2
	sed 's/textboxed{border:1px/textboxed{border:0px/g' < top2.html > top2.tmp.html
	mv top2.tmp.html top2.html

#	imagen top2


top2: 
	make top2.ps  && make top2.html && make top2.pdf


quick2: $(TOP2DEPS)
	latex top2; dvips $(DVIPSFLAGS) top2


let_alltt.ott: ../examples/tapl/let_alltt.ott
	cp ../examples/tapl/let_alltt.ott .



# these are files for which we update the web page for the current version
# (while other old examples are not)
WEB_FILES=                                              \
	../tests/test10.ott 					\
	test10.thy 					\
	test10.v 					\
	test10Script.sml                                \
	test10.lem                                      \
	test10.ml                                       \
	../revision_history.txt \
	top2.pdf \
	top2.ps \
	top2.html \
	top2*.png

test10.pdf: ../tests/test10.ott
	../bin/ott -i ../tests/test10.ott -o test10.tex
	pdflatex test10

install-web-files: top2.html test10.lem test10.pdf
	cp $(WEB_FILES) ~/public_html/ott

install-top2-built: top2.html top2.ps top2.pdf
	cp top2.ps ../built_doc
	cp top2.pdf ../built_doc
	cp top2.html ../built_doc
	cp top2*.png ../built_doc



# ghastly hackery to make ../README.md work both in the github
# markdown processing and in the latex user guide
README.tex: ../README.md
	rm -rf README.tex
	cat ../README.md | sed -e 's/|//g' > README.tmp.md
	pandoc  README.tmp.md -o README.tmp.tex
	cat README.tmp.tex | sed -e 's/section{Ott}/section{Getting started with Ott (the README)}/g' | sed -e 's/href/ahref/g' | sed -e 's/\\noalign{\\medskip}//g' > README.tex
	chmod ugo-w README.tex


%.pstex %.pstex_t : %.fig
	fig2dev -L pstex               $($*_FIG_OPTS) $< $*.pstex
	fig2dev -L pstex_t -p $*.pstex $($*_FIG_OPTS) $< $*.pstex_t
