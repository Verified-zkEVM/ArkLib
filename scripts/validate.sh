#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in ArkLib.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_lint=0
run_docs=0
run_site=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint] [--docs] [--site]

Default checks:
  - lake build
  - ./scripts/check-imports.sh
  - python3 ./scripts/check-docs-integrity.py

Optional checks:
  --lint   Run ./scripts/lint-style.sh
  --docs   Run DISABLE_EQUATIONS=1 lake build ArkLib:docs
  --site   Run ./scripts/build-web.sh (implies --docs)
EOF
}

for arg in "$@"; do
  case "$arg" in
    --lint)
      run_lint=1
      ;;
    --docs)
      run_docs=1
      ;;
    --site)
      run_docs=1
      run_site=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "ERROR: Unknown flag: $arg" >&2
      usage >&2
      exit 1
      ;;
  esac
done

echo "# Building project"
lake build

echo ""
echo "# Checking umbrella imports"
./scripts/check-imports.sh

echo ""
echo "# Checking docs integrity"
python3 ./scripts/check-docs-integrity.py

if (( run_lint )); then
  echo ""
  echo "# Running Lean style lint"
  ./scripts/lint-style.sh
fi

if (( run_docs )); then
  echo ""
  echo "# Building API docs"
  DISABLE_EQUATIONS=1 lake build ArkLib:docs
fi

if (( run_site )); then
  echo ""
  echo "# Building website and blueprint outputs"
  ./scripts/build-web.sh
fi

echo ""
echo "All requested validation checks passed."
