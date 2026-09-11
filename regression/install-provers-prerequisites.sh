#!/usr/bin/env bash
#
# install-provers-prerequisites.sh — apt packages needed to build the
# theorem provers Ott targets (Rocq/Coq, HOL4, Isabelle, Lean) on Ubuntu.
# Run this once, with sudo rights; then run install-provers.sh (which
# needs no sudo) to do the actual installs.

set -euo pipefail

sudo apt-get update
sudo apt-get install -y \
  build-essential git curl ca-certificates m4 unzip \
  pkg-config libgmp-dev \
  polyml libpolyml-dev
