#!/usr/bin/env bash
# CI axiom audit — delegates to scripts/axiom_audit.py (manifest: flagship_axioms.txt).
#
# The legacy shell implementation and scripts/flagship-theorems.txt are deprecated.
# Use: python3 scripts/axiom_audit.py
#
# Implements requirements (3) and (4) of issue #47.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

exec python3 ./scripts/axiom_audit.py "$@"
