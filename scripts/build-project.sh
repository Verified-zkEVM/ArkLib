#!/usr/bin/env bash

# Compile-only helper. For the recommended routine validation wrapper, use ./scripts/validate.sh.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

echo "# Building project"
lake build
