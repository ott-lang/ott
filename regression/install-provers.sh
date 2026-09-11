#!/usr/bin/env bash
#
# install-provers.sh — install the theorem provers Ott targets (Rocq/Coq,
# HOL4, Isabelle, Lean) on an Ubuntu system that already has opam and an
# OCaml switch set up.
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
#   HOL_DIR            where to clone/build HOL4      (default: $HOME/HOL)
#   ISABELLE_VERSION    Isabelle release to install    (default: Isabelle2025)
#   ISABELLE_DIR        where to unpack Isabelle        (default: $HOME/.isabelle)

set -euo pipefail

log() { printf '\n== %s ==\n' "$*"; }

HOL_DIR="${HOL_DIR:-$HOME/HOL}"
ISABELLE_VERSION="${ISABELLE_VERSION:-Isabelle2025}"
ISABELLE_DIR="${ISABELLE_DIR:-$HOME/.isabelle}"

# Claude: packages needed across the four installs, not by any one prover
# alone (opam packages like coq-ott and ocamlgraph need libgmp-dev and
# pkg-config too).
apt_prereqs() {
  log "apt prerequisites"
  sudo apt-get update
  sudo apt-get install -y \
    build-essential git curl ca-certificates m4 unzip \
    pkg-config libgmp-dev
}

install_rocq() {
  log "Rocq (Coq)"
  if command -v coqc >/dev/null 2>&1; then
    echo "already installed: $(coqc --version | head -1)"
    return
  fi
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
  sudo apt-get install -y polyml libpolyml-dev
  if [ ! -d "$HOL_DIR" ]; then
    git clone https://github.com/HOL-Theorem-Prover/HOL.git "$HOL_DIR"
  fi
  (
    cd "$HOL_DIR"
    poly < tools/smart-configure.sml
    bin/build
  )
  echo "add to PATH: $HOL_DIR/bin"
}

install_isabelle() {
  log "Isabelle"
  if command -v isabelle >/dev/null 2>&1; then
    echo "already installed: $(isabelle version)"
    return
  fi
  mkdir -p "$ISABELLE_DIR"
  if [ ! -d "$ISABELLE_DIR/$ISABELLE_VERSION" ]; then
    curl -fL -o /tmp/"$ISABELLE_VERSION"_linux.tar.gz \
      "https://isabelle.in.tum.de/dist/${ISABELLE_VERSION}_linux.tar.gz"
    tar -xzf /tmp/"$ISABELLE_VERSION"_linux.tar.gz -C "$ISABELLE_DIR"
    rm -f /tmp/"$ISABELLE_VERSION"_linux.tar.gz
  fi
  echo "add to PATH: $ISABELLE_DIR/$ISABELLE_VERSION/bin"
}

install_lean() {
  log "Lean (via elan)"
  if command -v elan >/dev/null 2>&1 || command -v lean >/dev/null 2>&1; then
    echo "already installed: $(lean --version 2>/dev/null || elan --version)"
    return
  fi
  curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y
  echo "add to PATH: \$HOME/.elan/bin"
}

targets=("$@")
[ ${#targets[@]} -eq 0 ] && targets=(rocq hol4 isabelle lean)

apt_prereqs
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
echo "Start a new shell, or source ~/.bashrc after adding the PATH lines above,"
echo "for hol/isabelle/lean to be found."
