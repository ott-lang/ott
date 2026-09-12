#!/usr/bin/env bash
#
# install-provers.sh — install the theorem provers Ott targets (Rocq/Coq,
# HOL4, Isabelle, Lean, Lem) on an Ubuntu system that already has opam and
# an OCaml switch set up. Runs entirely as the current user: no sudo.
#
# Run install-provers-prerequisites.sh first (as a user with sudo rights)
# to get the apt packages these installs need.
#
# Claude: written to be re-run safely — each section skips work it has
# already done, so a failed run can just be re-invoked.
#
# Usage:
#   ./install-provers.sh                    # install everything
#   ./install-provers.sh rocq hol4          # install only the named provers
#   ./install-provers.sh --clean            # remove everything this script installed
#   ./install-provers.sh --clean hol4 lean  # remove only the named provers
#
# Recognised names: rocq, hol4, isabelle, lean, lem
#
# Environment overrides:
#   HOL_DIR             where to clone/build HOL4      (default: $HOME/HOL)
#   ISABELLE_VERSION    Isabelle release to install     (default: Isabelle2025-2)
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

# Claude: show curl's normal progress meter when run interactively; suppress
# it when stdout isn't a terminal (e.g. piped to a log file), where it's just
# noise.
curl_quiet=()
[ -t 1 ] || curl_quiet=(--no-progress-meter)

HOL_DIR="${HOL_DIR:-$HOME/HOL}"
ISABELLE_VERSION="${ISABELLE_VERSION:-Isabelle2025-2}"
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

clean_rocq() {
  log "Rocq (clean)"
  if command -v coqc >/dev/null 2>&1; then
    opam remove -y rocq-prover
  else
    echo "not installed, nothing to remove"
  fi
}

install_lem() {
  log "Lem"
  if command -v lem >/dev/null 2>&1; then
    echo "already installed: $(lem -v)"   # Claude: "lem -v", not the GNU-style "--version"
    return
  fi
  need opam
  opam update
  # Claude: github.com/rems-project/lem's released-version instructions:
  # opam 2.0+ (already required above) and `opam install lem`.
  opam install -y lem
}

clean_lem() {
  log "Lem (clean)"
  if command -v lem >/dev/null 2>&1; then
    opam remove -y lem
  else
    echo "not installed, nothing to remove"
  fi
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
    # Claude: smart-configure's own search for libpolymain.a doesn't check
    # Ubuntu's multiarch library directories, and then stops to ask for this
    # file by hand; write it ourselves first when we can find the library.
    if [ ! -f tools-poly/poly-includes.ML ]; then
      libpolymain=$(find /usr/lib /usr/local/lib -maxdepth 3 -name libpolymain.a 2>/dev/null | head -1)
      if [ -n "$libpolymain" ]; then
        echo "val polymllibdir = \"$(dirname "$libpolymain")\";" > tools-poly/poly-includes.ML
      fi
    fi
    poly --script tools/smart-configure.sml
    bin/build
  )
  path_additions+=("$HOL_DIR/bin")
}

clean_hol4() {
  log "HOL4 (clean)"
  if [ -d "$HOL_DIR" ]; then
    rm -rf "$HOL_DIR"
    echo "removed $HOL_DIR"
  else
    echo "not installed, nothing to remove"
  fi
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
    # Claude: the Munich (.de) site, https://isabelle.in.tum.de/dist/..., 301s
    # to a dist.isabelle.cit.tum.de URL over plain http, not https, and that
    # host was unreachable when this was tried — use the Cambridge (.uk)
    # mirror instead, which serves the tarball directly over https. Bounded
    # timeouts turn a network problem reaching either host into a clear
    # failure within a few minutes rather than a silent multi-minute hang.
    curl -fL --connect-timeout 15 --max-time 900 "${curl_quiet[@]}" \
      -o /tmp/"$ISABELLE_VERSION"_linux.tar.gz \
      "https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/${ISABELLE_VERSION}_linux.tar.gz"
      # "https://isabelle.in.tum.de/dist/${ISABELLE_VERSION}_linux.tar.gz"
    tar -xzf /tmp/"$ISABELLE_VERSION"_linux.tar.gz -C "$ISABELLE_DIR"
    rm -f /tmp/"$ISABELLE_VERSION"_linux.tar.gz
  fi
  path_additions+=("$ISABELLE_DIR/$ISABELLE_VERSION/bin")
}

clean_isabelle() {
  log "Isabelle (clean)"
  if [ -d "$ISABELLE_DIR/$ISABELLE_VERSION" ]; then
    rm -rf "$ISABELLE_DIR/$ISABELLE_VERSION"
    echo "removed $ISABELLE_DIR/$ISABELLE_VERSION"
    rmdir "$ISABELLE_DIR" 2>/dev/null || true   # only if now empty
  else
    echo "not installed, nothing to remove"
  fi
}

install_lean() {
  log "Lean (via elan)"
  if command -v elan >/dev/null 2>&1 || command -v lean >/dev/null 2>&1; then
    echo "already installed: $(lean --version 2>/dev/null || elan --version)"
    return
  fi
  need curl
  curl -fL --connect-timeout 15 --max-time 120 "${curl_quiet[@]}" \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y
  path_additions+=("$HOME/.elan/bin")
}

clean_lean() {
  log "Lean (clean)"
  if [ -x "$HOME/.elan/bin/elan" ]; then
    "$HOME/.elan/bin/elan" self uninstall -y   # removes ~/.elan, toolchains included
  else
    echo "not installed, nothing to remove"
  fi
}

# Claude: pull --clean out from among the target names rather than giving it
# its own getopts pass, so it can go anywhere on the command line.
clean=false
targets=()
for a in "$@"; do
  case "$a" in
    --clean) clean=true ;;
    *) targets+=("$a") ;;
  esac
done
[ ${#targets[@]} -eq 0 ] && targets=(rocq hol4 isabelle lean lem)

action=install
$clean && action=clean

for t in "${targets[@]}"; do
  case "$t" in
    rocq|hol4|isabelle|lean|lem) "${action}_${t}" ;;
    *) echo "unknown target: $t (expected: rocq hol4 isabelle lean lem)" >&2; exit 1 ;;
  esac
done

log "done"
if $clean; then
  echo "If you added a PATH export for these tools to ~/.profile, remove it now."
elif [ ${#path_additions[@]} -gt 0 ]; then
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
