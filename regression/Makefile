##########################################################################
#                                   Ott                                  #
#                                                                        #
#        Peter Sewell, Computer Laboratory, University of Cambridge      #
#      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     #
#                                                                        #
#  Copyright 2005-2008                                                   #
#                                                                        #
#  Redistribution and use in source and binary forms, with or without    #
#  modification, are permitted provided that the following conditions    #
#  are met:                                                              #
#  1. Redistributions of source code must retain the above copyright     #
#  notice, this list of conditions and the following disclaimer.         #
#  2. Redistributions in binary form must reproduce the above copyright  #
#  notice, this list of conditions and the following disclaimer in the   #
#  documentation and/or other materials provided with the distribution.  #
#  3. The names of the authors may not be used to endorse or promote     #
#  products derived from this software without specific prior written    #
#  permission.                                                           #
#                                                                        #
#  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    #
#  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     #
#  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    #
#  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       #
#  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    #
#  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     #
#  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         #
#  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  #
#  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       #
#  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   #
#  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         #
##########################################################################

# REGRESSION ##########################################################

all: regression

regression: regression.ml
	ocamlopt -I +unix -I +str unix.cmxa str.cmxa -o regression -dtypes regression.ml
#	ocamlc -I +unix -I +str unix.cma str.cma -o regression -dtypes regression.ml

regression_p: regression_p_client.ml regression_p_master.ml
	ocamlc -I +unix -I +str unix.cma str.cma -o regression_p_client regression_p_client.ml
	ocamlc -I +unix -I +str unix.cma str.cma -o regression_p_master regression_p_master.ml

regression_para: regression_para.ml
	ocamlp3lopt -par unix.cmxa str.cmxa -o regression_para regression_para.ml

# The report a run is compared against by "make compare".  Point this at
# whichever report you are treating as the reference.
REFERENCE ?= report-2026-09-12.txt
REPORT    ?= report.txt

reg: regression 
	./regression -coq -isa -lem -lean -ocaml -latex -run $(REPORT) ../tests/test*.ott

regh: regression
	./regression -all -run $(REPORT) ../tests/test*.ott

simple: regression
	$(MAKE) clean-regr
	-make -C ../coq
	./regression -all -todo_list -todo_list_file regression-small.otl -keep_temp -run report-small.txt

# compare the latest run against the reference report
compare: regression
	./regression -compare $(REFERENCE) $(REPORT)

# a full run over regression.otl, kept under a dated name
report-2026-09-12.txt: regression
	$(MAKE) clean-regr
	-make -C ../coq
	time ./regression -all -todo_list -todo_list_file regression.otl -keep_temp -run $@ 2>&1 | tee report-2026-09-12-log.txt

clean:
	rm -rf *~
	rm -rf regression regression.annot regression.cmi regression.cmx
	rm -rf testRegr*
	rm -rf .testRegr*
	rm -rf ._ott_coqrc.aux
	rm -rf _ott_coqrc.glob

clean-regr:
	rm -rf testRegr*
	rm -rf *~
	rm -f regression-jenkins tests.xml

# Jenkins

# regression-jenkins: 
# 	ocamlc unix.cma str.cma -o regression-jenkins -dtypes regression-jenkins.ml

run-jenkins: regression
	./regression -all -todo_list -run jenkins-report.txt
	./regression -compare baseline-jenkins.txt jenkins-report.txt -jenkins
