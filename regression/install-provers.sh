#!/usr/bin/env bash
#
# install-provers.sh — install the theorem provers Ott targets (Rocq/Coq,
# HOL4, Isabelle, Lean) on an Ubuntu system that already has opam and an
# OCaml switch set up. Runs entirely as the current user: no sudo.
#
# Run install-provers-prerequisites.sh first (as a user with sudo rights)
# to get the apt packages these installs need.
#
# Claude: written to be re-run safely — each section skips work it has
# already done, so a failed run can just be re-invoked.
#
# Usage:
#   ./install-provers.sh              # install everything
#   ./install-provers.sh rocq hol4    # install only the named provers
#
# Recognised names: rocq, hol4, isabelle, lean
#
# Environment overrides:
#   HOL_DIR             where to clone/build HOL4      (default: $HOME/HOL)
#   ISABELLE_VERSION    Isabelle release to install     (default: Isabelle2025)
#   ISABELLE_DIR        where to unpack Isabelle         (default: $HOME/Isabelle)

set -euo pipefail

log() { printf '\n== %s ==\n' "$*"; }

# Claude: fail early with a clear pointer at the prerequisites script,
# rather than partway through a build with a confusing "command not found".
need() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing: $1 — run install-provers-prerequisites.sh first" >&2
    exit 1
  }
}

HOL_DIR="${HOL_DIR:-$HOME/HOL}"
ISABELLE_VERSION="${ISABELLE_VERSION:-Isabelle2025}"
ISABELLE_DIR="${ISABELLE_DIR:-$HOME/Isabelle}"

# Claude: directories the installs below add to, collected here so we can
# print one suggested PATH line at the end instead of scattered ones.
path_additions=()

install_rocq() {
  log "Rocq"
  if command -v coqc >/dev/null 2>&1; then
    echo "already installed: $(coqc --version | head -1)"
    return
  fi
  need opam
  opam update
  # Claude: "coq" was renamed "rocq-prover" upstream.
  opam install -y rocq-prover
}

install_hol4() {
  log "HOL4"
  if command -v hol >/dev/null 2>&1 || [ -x "$HOL_DIR/bin/hol.bare" ]; then
    echo "already installed in $HOL_DIR"
    return
  fi
  need git
  need poly
  if [ ! -d "$HOL_DIR" ]; then
    git clone https://github.com/HOL-Theorem-Prover/HOL.git "$HOL_DIR"
  fi
  (
    cd "$HOL_DIR"
    poly < tools/smart-configure.sml
    bin/build
  )
  path_additions+=("$HOL_DIR/bin")
}

install_isabelle() {
  log "Isabelle"
  if command -v isabelle >/dev/null 2>&1; then
    echo "already installed: $(isabelle version)"
    return
  fi
  need curl
  need tar
  mkdir -p "$ISABELLE_DIR"
  if [ ! -d "$ISABELLE_DIR/$ISABELLE_VERSION" ]; then
    curl -fL -o /tmp/"$ISABELLE_VERSION"_linux.tar.gz \
      "https://isabelle.in.tum.de/dist/${ISABELLE_VERSION}_linux.tar.gz"
    tar -xzf /tmp/"$ISABELLE_VERSION"_linux.tar.gz -C "$ISABELLE_DIR"
    rm -f /tmp/"$ISABELLE_VERSION"_linux.tar.gz
  fi
  path_additions+=("$ISABELLE_DIR/$ISABELLE_VERSION/bin")
}

install_lean() {
  log "Lean (via elan)"
  if command -v elan >/dev/null 2>&1 || command -v lean >/dev/null 2>&1; then
    echo "already installed: $(lean --version 2>/dev/null || elan --version)"
    return
  fi
  need curl
  curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y
  path_additions+=("$HOME/.elan/bin")
}

targets=("$@")
[ ${#targets[@]} -eq 0 ] && targets=(rocq hol4 isabelle lean)

for t in "${targets[@]}"; do
  case "$t" in
    rocq)     install_rocq ;;
    hol4)     install_hol4 ;;
    isabelle) install_isabelle ;;
    lean)     install_lean ;;
    *) echo "unknown target: $t (expected: rocq hol4 isabelle lean)" >&2; exit 1 ;;
  esac
done

log "done"
if [ ${#path_additions[@]} -gt 0 ]; then
  # Claude: join with ':' by hand rather than `IFS=: "${path_additions[*]}"`,
  # so this still reads clearly if entries are ever added with spaces in them.
  joined=""
  for d in "${path_additions[@]}"; do
    joined="${joined:+$joined:}$d"
  done
  echo "Add this to ~/.profile, then log in again (or run it directly now):"
  echo
  echo "  export PATH=\"$joined:\$PATH\""
else
  echo "Nothing new needs adding to PATH."
fi
