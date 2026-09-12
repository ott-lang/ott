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

reg: regression 
	./regression -no_hol -report ../tests/test*.ott

regb: regression
	./regression -no_hol -baseline ../tests/test*.ott

regh: regression
	./regression -report ../tests/test*.ott

regbh: regression
	./regression -baseline ../tests/test*.ott

simple: regression
	$(MAKE) clean-regr
	-make -C ../coq
	./regression  -todo_list -todo_list_file regression-small.otl -keep_temp


# 2026-09-12 compare against the most recent baseline
baseline-2026-09-12.bl baseline-2026-09-12.txt baseline-2026-09-12-log.txt: regression
	$(MAKE) clean-regr
	-make -C ../coq
	time ./regression -baseline -baseline_file baseline-2026-09-12.bl -todo_list -todo_list_file regression.otl -keep_temp -report 2>&1 | tee baseline-2026-09-12-log.txt
	./regression -dump_baseline -baseline_file baseline-2026-09-12.bl > baseline-2026-09-12.txt

# 2026-09-12 first baseline including the Lem and Lean columns
baseline-2026-09-12-lem-lean.bl baseline-2026-09-12-lem-lean.txt baseline-2026-09-12-lem-lean-log.txt: regression
	$(MAKE) clean-regr
	-make -C ../coq
	time ./regression -baseline -baseline_file baseline-2026-09-12-lem-lean.bl -todo_list -todo_list_file regression.otl -keep_temp -report 2>&1 | tee baseline-2026-09-12-lem-lean-log.txt
	./regression -dump_baseline -baseline_file baseline-2026-09-12-lem-lean.bl > baseline-2026-09-12-lem-lean.txt

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
	./regression -baseline_file baseline-jenkins.bl -todo_list -jenkins
