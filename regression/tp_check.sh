#!/bin/sh 

# simple regression test

# Usage: 
# tp_check.sh file_name    file_name is processed by Ott, Coq, Isabelle, and HOL
# tp_check.sh              runs Ott, Coq, Isabelle, and HOL over all files in TEST_FILES

TEST_DIR="../tests/"
TEST_FILES="test1.txt test2.txt test3.txt test4.txt test5.txt test6.txt test8.txt test9.txt test10.ott test10st.ott test11.ott test12.ott test13.ott test13b.ott test14.ott"

# do not edit below this line

no_tests=0
succ_isa=0
succ_coq=0
succ_ott=0
succ_hol=0

function test {
  no_tests=`expr $no_tests + 1`
  echo "*** processing "$1
  rm -f outTheory.* # just in case Holmake is wierd

  ./ott -colour true -showraw false -coq out.v -isabelle out.thy $1 > /dev/null

  if [ $? = 0 ]
  then
    succ_ott=`expr $succ_ott + 1`
    # running coqc
    coqc out.v > /dev/null
    if [ $? = 0 ]
    then  
      echo " * Coq: SUCCESS"
      succ_coq=`expr $succ_coq + 1`
      rm out.vo
    else 
      echo " * Coq: FAILURE"
    fi
    # running isabelle
    echo 'use_thy "out" handle e => (OS.Process.exit OS.Process.failure);' | isabelle > /dev/null
    if [ $? = 0 ]
    then 
      echo " * Isa: SUCCESS"      
      succ_isa=`expr $succ_isa + 1`
    else 
      echo " * Isa: FAILURE"
    fi
    # running hol
    Holmake outTheory.uo &> /dev/null
    if [ $? = 0 ]
    then  
      echo " * HOL: SUCCESS"
      succ_hol=`expr $succ_hol + 1`
      rm outTheory.*
    else 
      echo " * HOL: FAILURE"
      rm -f outTheory.*
    fi

  else
    echo " * Ott: FAILURE"
  fi
  }

if [ -n "$1" ]
then test $1
else
  for file in $TEST_DIR*.ott
  do
    test $file
  done
  echo "*** No test: "$no_tests
  echo " *  Ott    : "$succ_ott
  echo " *  Coq    : "$succ_coq
  echo " *  Isa    : "$succ_isa
  echo " *  HOL    : "$succ_hol
fi

exit 
