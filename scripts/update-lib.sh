#!/usr/bin/env bash

# Update ArkLib.lean with all imports.
# This script only considers tracked files. New ArkLib/**/*.lean files must be staged first.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

if [[ ! -d "ArkLib" || ! -f "ArkLib.lean" ]]; then
  echo "ERROR: Run this script from inside the ArkLib repository." >&2
  exit 1
fi

untracked_lean_files=()
while IFS= read -r file; do
  if [[ -n "$file" ]]; then
    untracked_lean_files+=("$file")
  fi
done < <(git ls-files --others --exclude-standard -- 'ArkLib/*.lean')

if (( ${#untracked_lean_files[@]} > 0 )); then
  echo "ERROR: Untracked Lean files under ArkLib/ are not included in ArkLib.lean generation." >&2
  echo "Stage them first, then rerun this script:" >&2
  printf '  git add %q\n' "${untracked_lean_files[@]}" >&2
  exit 1
fi

echo "Updating ArkLib.lean with all tracked imports..."

tmp_file="$(mktemp "${TMPDIR:-/tmp}/arklib-imports.XXXXXX")"
cleanup() {
  rm -f "$tmp_file"
}
trap cleanup EXIT

git ls-files -- 'ArkLib/*.lean' \
  | LC_ALL=C sort \
  | sed 's/\.lean//;s,/,.,g;s/^/import /' > "$tmp_file"

mv "$tmp_file" ArkLib.lean
trap - EXIT

echo "✓ ArkLib.lean updated with $(wc -l < ArkLib.lean) imports"
