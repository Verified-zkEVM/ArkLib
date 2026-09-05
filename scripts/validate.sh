#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in ArkLib.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_docs=0
run_site=0
run_axioms=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint] [--docs] [--site] [--axioms]

Default checks:
  - lake build
  - lake test (ArkLibTest compile-time acceptance clients)
  - lake exe lint-style
  - ./scripts/test-lint-plugin.sh
  - lake exe toyproblem-runtime
  - lake exe hachi-runtime
  - fail on non-`sorry` warnings under ArkLib/
  - ./scripts/check-imports.sh
  - ./scripts/test-build-timing-report.sh
  - python3 ./scripts/check-docs-integrity.py
  - python3 ./scripts/kb/lint.py

Optional checks:
  --lint    Deprecated compatibility flag; style linting is always enforced
  --docs    Run DISABLE_EQUATIONS=1 lake build ArkLib:docs
  --site    Run ./scripts/build-web.sh (implies --docs)
  --axioms  Test the axiomsweep tool, then run the axiom/sorry regression gate
EOF
}

for arg in "$@"; do
  case "$arg" in
    --lint)
      echo "NOTE: --lint is no longer needed; Lean source style is checked by default."
      ;;
    --docs)
      run_docs=1
      ;;
    --site)
      run_docs=1
      run_site=1
      ;;
    --axioms)
      run_axioms=1
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

echo "# Building project"
lake build 2>&1 | tee "$build_log"

echo ""
echo "# Building compile-time acceptance clients"
lake test 2>&1 | tee -a "$build_log"

echo ""
echo "# Checking ArkLibTest warning budget"
python3 ./scripts/check-warning-log.py "$build_log" \
  --path-prefix ArkLibTest/ \
  --label "ArkLibTest warnings (including admissions)"

echo ""
echo "# Checking ArkLib warning budget"
python3 ./scripts/check-warning-log.py "$build_log" \
  --path-prefix ArkLib/ \
  --exclude-substring 'declaration uses `sorry`' \
  --label 'ArkLib non-sorry warnings'

echo ""
echo "# Running Lean-native source-policy gate"
if [[ "${GITHUB_ACTIONS:-}" == "true" ]]; then
  lake exe lint-style --github
else
  lake exe lint-style
fi

echo ""
echo "# Testing build-time source-policy plugin"
./scripts/test-lint-plugin.sh

echo ""
echo "# Running toy-problem compiled runtime checks"
lake exe toyproblem-runtime

echo ""
echo "# Running nonrecursive-Hachi compiled runtime checks"
# Default target only: the composed opening run (`--full`) is dominated by the honest sumcheck
# prover and is far too slow to gate on. See scripts/HachiRuntime.lean.
lake exe hachi-runtime

echo ""
echo "# Checking umbrella imports"
./scripts/check-imports.sh

echo ""
echo "# Testing build timing report fixtures"
./scripts/test-build-timing-report.sh

echo ""
echo "# Checking docs integrity"
python3 ./scripts/check-docs-integrity.py

echo ""
echo "# Checking knowledge base"
python3 ./scripts/kb/lint.py

if (( run_axioms )); then
  echo ""
  echo "# Testing the axiom sweep tool against its fixture matrix"
  ./scripts/test-axiomsweep.sh
  echo ""
  echo "# Checking axiom/sorry regression baseline"
  # VCVio's FFI C sources live in git submodules that Lake does not fetch,
  # and every root-package executable links them.
  if [ -e .lake/packages/VCVio/.git ]; then
    git -C .lake/packages/VCVio submodule update --init --recursive --quiet
  fi
  lake exe axiomsweep --check
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
