# Claude: build the Lean that tests/test10st.ott generates, and check the
# metatheory statements against it.
#
#   make             generate test10st.lean and check both files
#   make test10st.lean    just the generated module
#   make clean
#
# ott is expected to have been built at the top of this checkout ("make world"
# there), and lean to be on the PATH, which for an elan installation means
# ~/.elan/bin - an interactive shell has it, a bare "env -i make" does not.

OTT  = ../../bin/ott
OTT_SRC = ../../tests/test10st.ott
LEAN ?= lean

.PHONY: all clean

all: test10st-metatheory.olean

# (a) the generated module
test10st.lean: $(OTT_SRC) $(OTT)
	$(OTT) -i $(OTT_SRC) -o $@

test10st.olean: test10st.lean
	$(LEAN) -o $@ $<

# (b) the metatheory statements, checked against it.  Every proof is sorry, so
# a successful run reports "declaration uses 'sorry'" for each result and
# nothing else.
test10st-metatheory.olean: test10st-metatheory.lean test10st.olean
	LEAN_PATH=. $(LEAN) -o $@ $<

clean:
	rm -f test10st.lean test10st.olean test10st-metatheory.olean
