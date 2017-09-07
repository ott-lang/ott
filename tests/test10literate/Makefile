all: test10.pdf test10-wrapper.pdf

# first way
test10.tex: test10.ott Makefile
	../../bin/ott -i test10.ott -o test10.tex

test10.pdf: test10.tex
	pdflatex test10.tex

# second way (usually better)
test10-inc.tex: test10.ott Makefile
	../../bin/ott -tex_wrap false -i test10.ott -o test10-inc.tex

test10-wrapper.pdf: test10-inc.tex test10-wrapper.tex
	pdflatex test10-wrapper.tex


clean:
	rm -rf *~
	rm -rf test10.tex *.aux *.log test10.pdf test10-inc.tex test10-wrapper.pdf
