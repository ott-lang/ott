#!/usr/bin/env bash
#
# install-provers-prerequisites.sh — apt packages needed to build the
# theorem provers Ott targets (Rocq/Coq, HOL4, Isabelle, Lean) on Ubuntu.
# Run this once, with sudo rights; then run install-provers.sh (which
# needs no sudo) to do the actual installs.

set -euo pipefail

# Claude: linux-libc-dev and findutils are usually already present on any
# Ubuntu system (pulled in by build-essential, or part of the base install),
# but opam's rocq-prover / lem solves fail outright if either is missing —
# they depend on conf-linux-libc-dev / conf-findutils — so both are listed
# explicitly rather than relied on.
sudo apt-get update
sudo apt-get install -y \
  build-essential git curl ca-certificates m4 unzip \
  pkg-config libgmp-dev linux-libc-dev findutils \
  polyml libpolyml-dev
