#########################################################################
#                                   Ott                                  #
#                                                                        #
#        Peter Sewell, Computer Laboratory, University of Cambridge      #
#      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     #
#                                                                        #
#  Copyright 2005-2011                                                   #
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

# make world #############################################################



world:
	cd src; $(MAKE) install

world.byt:
	cd src; $(MAKE) install.byt

# cleanup ################################################################

clean:
	cd src; $(MAKE) clean
	rm -f *~

# tests ##################################################################

LATEX		= latex
DVIPS		= dvips

# normal case, e.g. "make tests/test8.out"

%.out: %.ott 
	bin/ott   							\
                -o out.thy -o out.v -o outScript.sml 	\
	        -o out.tex 						\
                $<                                                      \
	&& ($(LATEX) out; $(DVIPS) out -o)

%.tex.out: %.ott
	bin/ott   							\
	        -o out.tex 						\
                $<                                                      \
	&& ($(LATEX) out; $(DVIPS) out -o)

%.coq.out: %.ott
	bin/ott   							\
                -o out.v  						\
	        -o out.tex 						\
                $<                                                      \
	&& ($(LATEX) out; $(DVIPS) out -o)

%.hol.out: %.ott
	bin/ott   							\
                -o outScript.sml 					\
	        -o out.tex 						\
                $<                                                      \
	&& ($(LATEX) out; $(DVIPS) out -o)

%.isa.out: %.ott
	bin/ott   							\
                -o out.thy 					\
	        -o out.tex 						\
                $<                                                      \
	&& ($(LATEX) out; $(DVIPS) out -o)

# test10 special cases 

test10: tests/test10.ott
	bin/ott   							\
                -o out.thy -o out.v -o outScript.sml 	\
	        -o out.tex 						\
	        -parse ":user_syntax: :user_syntax__t: :concrete: \x1'.x1'"  \
	        -parse ":user_syntax: :concrete: \x1'.x1'"  		\
	        -parse ":user_syntax: \x1'.x1'"  			\
	        -parse ":concrete_t:\x1'.x1'"                      	\
                tests/test10.ott                           		\
	&& ($(LATEX) out; $(DVIPS) out -o)

test10st_halves: tests/test10st_first_half.ott tests/test10st_second_half.ott
	bin/ott  -o out.thy -o out.v -o out.tex 		\
	         -o outScript.sml 					\
                 tests/test10st_first_half.ott 			 	\
                 tests/test10st_second_half.ott    			\
	&& ($(LATEX) out; $(DVIPS) out -o)

test10_isasyn: tests/test10_isasyn.ott
	bin/ott -colour true -showraw false  				\
                -o out.thy -o out.v -o out.tex 		\
                -isa_syntax true 					\
	        -tex_show_meta true                                     \
                tests/test10_isasyn.ott                              	\
	&& ($(LATEX) out; $(DVIPS) out -o)

# test 7 special case - ott as a munger

test7afilter: tests/test7b.ott tests/test7t.mng
	bin/ott  -o out.sty 						\
	       -tex_show_meta false                                     \
	       -tex_wrap false                                          \
	       -tex_name_prefix	ott					\
	       -tex_filter tests/test7t.mng out.tex        		\
               tests/test7b.ott 			      		\
        && ($(LATEX) out; $(DVIPS) out -o)

# TAPL examples

SYS_BOOL = 				\
  examples/tapl/common.ott 		\
  examples/tapl/bool.ott

SYS_ARITH = 				\
  examples/tapl/nat.ott 		\
  $(SYS_BOOL) 

SYS_UNTYPED = 				\
  examples/tapl/common.ott 		\
  examples/tapl/bool.ott

SYS_PURESIMPLE = 			\
  examples/tapl/common.ott 		\
  examples/tapl/common_typing.ott 	\
  examples/tapl/arrow_typing.ott

SYS_TYBOOL = 				\
  examples/tapl/bool.ott 		\
  examples/tapl/bool_typing.ott 	\
  $(SYS_PURESIMPLE)

SYS_SORTOFFULLSIMPLE = 			\
  examples/tapl/common.ott        	\
  examples/tapl/common_typing.ott 	\
  examples/tapl/common_labels.ott 	\
  examples/tapl/common_index.ott 	\
  examples/tapl/arrow_typing.ott  	\
  examples/tapl/basety.ott  	     	\
  examples/tapl/bool.ott  	     	\
  examples/tapl/bool_typing.ott   	\
  examples/tapl/nat.ott	     	\
  examples/tapl/nat_typing.ott    	\
  examples/tapl/unit.ott	     	\
  examples/tapl/seq.ott	     	\
  examples/tapl/ascribe.ott       	\
  examples/tapl/inert.ott         	\
  examples/tapl/let.ott           	\
  examples/tapl/sum.ott        	\
  examples/tapl/variant.ott        	\
  examples/tapl/product.ott       	\
  examples/tapl/tuple.ott        	\
  examples/tapl/record.ott        	\
  examples/tapl/fix.ott  	     
# examples/tapl/arrow.ott  	     	\

SYS_ROUGHLYFULLSIMPLE = \
  examples/tapl/common.ott \
  examples/tapl/common_index.ott \
  examples/tapl/common_labels.ott \
  examples/tapl/common_typing.ott \
  examples/tapl/bool.ott \
  examples/tapl/bool_typing.ott \
  examples/tapl/nat.ott \
  examples/tapl/nat_typing.ott \
  examples/tapl/arrow_typing.ott \
  examples/tapl/basety.ott \
  examples/tapl/unit.ott \
  examples/tapl/seq.ott \
  examples/tapl/ascribe.ott \
  examples/tapl/let.ott \
  examples/tapl/product.ott \
  examples/tapl/sum.ott \
  examples/tapl/fix.ott \
  examples/tapl/tuple.ott \
  examples/tapl/variant.ott
# examples/tapl/record.ott

SYS_TUPLE = 				\
  examples/tapl/common.ott        	\
  examples/tapl/common_typing.ott 	\
  examples/tapl/common_index.ott 	\
  examples/tapl/unit.ott	     	\
  examples/tapl/tuple.ott        
# examples/tapl/arrow.ott  	     	\

SYS_PURESUB = 				\
  examples/tapl/common.ott        	\
  examples/tapl/common_typing.ott 	\
  examples/tapl/arrow_typing.ott  	\
  examples/tapl/sub_arrow.ott     	\
  examples/tapl/top.ott  	     

SYS_PURERCDSUB = $(SYS_PURESUB) 	\
  examples/tapl/common_labels.ott 	\
  examples/tapl/common_index.ott 	\
  examples/tapl/record.ott        	\
  examples/tapl/sub_record.ott        

sys-bool: $(SYS_BOOL) 
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_BOOL) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-arith: $(SYS_ARITH)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_ARITH) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-untyped: $(SYS_UNTYPED)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_UNTYPED) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-puresimple: $(SYS_PURESIMPLE)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_PURESIMPLE) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-tuple: $(SYS_TUPLE)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_TUPLE) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-tybool: $(SYS_TYBOOL)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_TYBOOL) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-sortoffullsimple: $(SYS_SORTOFFULLSIMPLE)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_SORTOFFULLSIMPLE) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-roughlyfullsimple: $(SYS_ROUGHLYFULLSIMPLE)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_ROUGHLYFULLSIMPLE) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-puresub: $(SYS_PURESUB)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_PURESUB) \
	&& ($(LATEX) out; $(DVIPS) out -o)

sys-purercdsub: $(SYS_PURERCDSUB)
	bin/ott -merge true -tex_show_meta false -o out.tex -o out.v -o out.thy -o outScript.sml $(SYS_PURERCDSUB) \
	&& ($(LATEX) out; $(DVIPS) out -o)

