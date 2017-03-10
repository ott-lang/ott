#!/bin/sh

# this script is invoked by regression -night before running the tests
# defined in regression.otl

cd /home/yquem/moscova/zappa/repo/update/Ott2/tests/
cvs update
cd /home/yquem/moscova/zappa/repo/update/Ott2/src/
cvs update -d
make coq-lib
ln -sf coq/*.vo .
make > /dev/null
make tmp_test7a.ott
make tmp_test7.ott
#make tmp_lj.ott

cd ../examples/tapl/
cvs update
make stlc_coq_prelude
cd ../../src

