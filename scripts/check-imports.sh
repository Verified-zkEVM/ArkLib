#!/usr/bin/env bash

# Check whether ArkLib.lean matches the tracked ArkLib/**/*.lean file set.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

echo "Checking if all imports are up to date..."

backup_file="$(mktemp "${TMPDIR:-/tmp}/ArkLib.lean.backup.XXXXXX")"
cp ArkLib.lean "$backup_file"

restore_original() {
  if [[ -f "$backup_file" ]]; then
    mv "$backup_file" ArkLib.lean
  fi
}
trap restore_original EXIT

./scripts/update-lib.sh

if git diff --quiet -- ArkLib.lean; then
  echo "✓ All imports are up to date!"
  exit 0
fi

echo "❌ Import file is out of date!"
echo "Differences found:"
git diff -- ArkLib.lean
echo ""
echo "To fix this, run: ./scripts/update-lib.sh"
exit 1
