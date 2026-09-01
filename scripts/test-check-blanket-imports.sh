#!/usr/bin/env bash

# Focused fixtures for scripts/check-blanket-imports.py.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

scanner="scripts/check-blanket-imports.py"
fixtures="scripts/import-fixtures"

for fixture in allowed.lean commented-out.lean; do
  if ! python3 "$scanner" "$fixtures/$fixture"; then
    echo "ERROR: allowed fixture was rejected: $fixture" >&2
    exit 1
  fi
done

for fixture in \
    ordinary-root.lean \
    public-meta-root.lean \
    import-all-root.lean \
    escaped-root.lean \
    multiline-root.lean \
    interposed-comment-root.lean \
    multiple-modules-root.lean; do
  if python3 "$scanner" "$fixtures/$fixture" >/dev/null; then
    echo "ERROR: blanket-import fixture was accepted: $fixture" >&2
    exit 1
  fi
done

echo "✓ Blanket-import scanner fixtures passed!"
