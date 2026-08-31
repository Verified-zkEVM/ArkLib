#!/usr/bin/env bash

# Check whether ArkLib.lean matches the tracked ArkLib/**/*.lean file set.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

echo "Checking for blanket package-root imports..."

# `ArkLib.lean` is the generated package umbrella and is checked separately below. Source modules
# under `ArkLib/` must name stable owner modules instead of importing a dependency's package root.
# Keep this check separate from the generated-file check so directory-layer rules can be added here.
tracked_lean_files=()
while IFS= read -r file; do
  tracked_lean_files+=("$file")
done < <(git ls-files -- 'ArkLib/**/*.lean')

blanket_status=0
blanket_imports="$(
  awk -f scripts/check-blanket-imports.awk "${tracked_lean_files[@]}"
)" || blanket_status=$?

if (( blanket_status > 1 )); then
  echo "ERROR: blanket-import scanner failed with exit code $blanket_status" >&2
  exit "$blanket_status"
fi

if (( blanket_status == 1 )); then
  echo "❌ Blanket package-root imports found in ArkLib source modules:"
  echo "$blanket_imports"
  echo ""
  echo "Import the stable owner module instead. Any umbrella exception must be file-scoped and"
  echo "documented in scripts/check-imports.sh."
  exit 1
fi

echo "✓ No blanket package-root imports found!"

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
