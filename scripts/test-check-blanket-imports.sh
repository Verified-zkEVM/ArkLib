#!/usr/bin/env bash

# Focused fixtures for scripts/check-blanket-imports.awk.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

scanner="scripts/check-blanket-imports.awk"
fixtures="scripts/import-fixtures"

if ! awk -f "$scanner" "$fixtures/allowed.txt"; then
  echo "ERROR: owner-module imports were rejected" >&2
  exit 1
fi

for fixture in \
    ordinary-root.txt \
    public-meta-root.txt \
    import-all-root.txt \
    multiple-modules-root.txt; do
  if awk -f "$scanner" "$fixtures/$fixture" >/dev/null; then
    echo "ERROR: blanket-import fixture was accepted: $fixture" >&2
    exit 1
  fi
done

echo "✓ Blanket-import scanner fixtures passed!"
