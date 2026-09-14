# Claude: build the Lean that tests/test7.ott generates, and check the
# metatheory statements against it.
#
#   make             generate test7.lean and check the statements and proofs
#   make clean
#
# ott is expected to have been built at the top of this checkout ("make world"
# there), and lean to be on the PATH, which for an elan installation means
# ~/.elan/bin - an interactive shell has it, a bare "env -i make" does not.
#
# The Ott source is tests/tmp_test7.ott, which the top-level Makefile derives
# from tests/test7.ott by stripping the "r" line prefixes; the rule below
# delegates to it.

OTT  = ../../bin/ott
TEST = test7
OTT_SRC = ../../tests/tmp_test7.ott
LEAN ?= lean

.PHONY: all clean

all: $(TEST)_proofs.olean

$(OTT_SRC): ../../tests/test7.ott
	$(MAKE) -C ../.. tests/tmp_test7.ott

# one ott run writes all three files, so this is a grouped target (GNU make 4.3
# and later): the generated module, and the two metatheory files with each piece
# of object syntax replaced by the Lean the grammar gives for it
$(TEST).lean $(TEST)_statements.lean $(TEST)_proofs.lean &: \
		$(OTT_SRC) $(TEST)_statements.mng $(TEST)_proofs.mng
	$(OTT) -i $(OTT_SRC) -o $(TEST).lean \
	  -lean_filter $(TEST)_statements.mng $(TEST)_statements.lean \
	  -lean_filter $(TEST)_proofs.mng $(TEST)_proofs.lean

$(TEST).olean: $(TEST).lean
	$(LEAN) -o $@ $<

# LEAN_PATH so that "import test7" and "import test7_statements" resolve
# against the modules built here
$(TEST)_statements.olean: $(TEST)_statements.lean $(TEST).olean
	LEAN_PATH=. $(LEAN) -o $@ $<

$(TEST)_proofs.olean: $(TEST)_proofs.lean $(TEST)_statements.olean
	LEAN_PATH=. $(LEAN) -o $@ $<

clean:
	rm -f $(TEST).lean $(TEST)_statements.lean $(TEST)_proofs.lean \
	      $(TEST).olean $(TEST)_statements.olean $(TEST)_proofs.olean
