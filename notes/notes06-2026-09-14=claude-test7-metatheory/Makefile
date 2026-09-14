# Claude: build the Lean that tests/test7.ott generates, and check the
# metatheory statements against it.
#
#   make             generate test7.lean and check both files
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

all: $(TEST)-metatheory.olean

$(OTT_SRC): ../../tests/test7.ott
	$(MAKE) -C ../.. tests/tmp_test7.ott

# one ott run writes both files, so this is a grouped target (GNU make 4.3 and
# later): the generated module, and the metatheory file with each piece of
# object syntax replaced by the Lean the grammar gives for it
$(TEST).lean $(TEST)-metatheory.lean &: $(OTT_SRC) $(TEST)-metatheory.mng
	$(OTT) -i $(OTT_SRC) -o $(TEST).lean -lean_filter $(TEST)-metatheory.mng $(TEST)-metatheory.lean

$(TEST).olean: $(TEST).lean
	$(LEAN) -o $@ $<

# LEAN_PATH so that the "import test7" in the .mng resolves against the module
# built here
$(TEST)-metatheory.olean: $(TEST)-metatheory.lean $(TEST).olean
	LEAN_PATH=. $(LEAN) -o $@ $<

clean:
	rm -f $(TEST).lean $(TEST)-metatheory.lean $(TEST).olean $(TEST)-metatheory.olean
