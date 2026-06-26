#!/usr/bin/env bash

# Cheap repo-wide checks for tracked Lean files.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

executable_files="$(
  while IFS= read -r -d '' path; do
    if [[ -x "$path" ]]; then
      printf '%s\n' "$path"
    fi
  done < <(git ls-files -z '*.lean')
)"

if [[ -n "$executable_files" ]]; then
  echo "ERROR: The following tracked Lean files have the executable bit set."
  echo "$executable_files"
  exit 1
fi

ignore_case_clashes="$(git ls-files | sort --ignore-case | uniq -D --ignore-case)"

if [[ -n "$ignore_case_clashes" ]]; then
  printf 'The following files have the same lower-case form:\n\n%s\n\n' "$ignore_case_clashes"
  printf 'Please avoid case-insensitive filename clashes.\n'
  exit 1
fi
