#!/usr/bin/env bash

# Check whether ArkLib.lean matches the tracked ArkLib/**/*.lean file set.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

echo "Checking if all imports are up to date..."

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
echo "Then stage ArkLib.lean and commit."
exit 1
