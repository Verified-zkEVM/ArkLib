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

Default checks (mirrors the CI gates so local == CI):
  - python3 ./scripts/forbidden_tokens.py          (CI gate 1, precheck)
  - lake build
  - fail on non-`sorry` warnings under ArkLib/Data/
  - python3 ./scripts/sorry_census.py --fail-on-holes  (CI gate 2)
  - python3 ./scripts/axiom_audit.py                   (CI gate 3)
  - ./scripts/check-imports.sh
  - python3 ./scripts/check-docs-integrity.py
  - python3 ./scripts/kb/check_generated.py
  - python3 ./scripts/kb/lint.py --strict-cited-pages
  - bash ./scripts/security-scan.sh

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

build_log="$(mktemp "${TMPDIR:-/tmp}/arklib-validate-build.XXXXXX")"
cleanup() {
  rm -f "$build_log"
}
trap cleanup EXIT

# CI gate 1: fast laundering-token precheck (no Lean toolchain needed), run
# before the build so a forbidden token / undocumented axiom fails fast.
echo "# Forbidden-token precheck (native_decide / bv_decide / undocumented axiom)"
python3 ./scripts/forbidden_tokens.py

echo ""
echo "# Building project"
lake build 2>&1 | tee "$build_log"

echo ""
echo "# Checking Data warning budget"
python3 ./scripts/check-warning-log.py "$build_log" \
  --path-prefix ArkLib/Data/ \
  --exclude-substring 'declaration uses `sorry`' \
  --label 'ArkLib/Data non-sorry warnings'

# CI gate 2: zero live sorry/admit holes in ArkLib source.
echo ""
echo "# Sorry census (zero live holes)"
python3 ./scripts/sorry_census.py --fail-on-holes

# CI gate 3: flagship theorems depend only on the standard axioms.
echo ""
echo "# Axiom audit (flagship theorems)"
python3 ./scripts/axiom_audit.py

echo ""
echo "# Proximity prize clean-room audit (pinned prize-resolution declarations)"
python3 ./scripts/proximity_prize_cleanroom_audit.py

echo ""
echo "# Checking umbrella imports"
./scripts/check-imports.sh

echo ""
echo "# Checking docs integrity"
python3 ./scripts/check-docs-integrity.py

echo ""
echo "# Checking knowledge base"
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py --strict-cited-pages

echo ""
echo "# Security scan (pinned Python manifests)"
bash ./scripts/security-scan.sh

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
