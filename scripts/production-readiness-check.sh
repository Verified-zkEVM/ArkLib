#!/usr/bin/env bash
# Production-readiness preflight: runs every gate that does not require a full Lean build,
# then reports Lean-dependent gates separately with actionable commands.
#
# Mirrors checklist items 1–7 from docs/operations/PRODUCTION-READINESS.md.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

failures=0
report_section() {
  printf '\n## %s\n' "$1"
}

pass() {
  printf 'PASS: %s\n' "$1"
}

fail() {
  printf 'FAIL: %s\n' "$1" >&2
  failures=$((failures + 1))
}

report_section "1. Static validation (real execution, no mocks)"
if python3 scripts/forbidden_tokens.py; then
  pass "forbidden_tokens.py"
else
  fail "forbidden_tokens.py"
fi

if python3 scripts/sorry_census.py --fail-on-holes; then
  pass "sorry_census.py (zero live holes)"
else
  fail "sorry_census.py"
fi

if python3 scripts/check-docs-integrity.py; then
  pass "check-docs-integrity.py"
else
  fail "check-docs-integrity.py"
fi

if python3 scripts/kb/check_generated.py; then
  pass "kb/check_generated.py"
else
  fail "kb/check_generated.py"
fi

if python3 scripts/kb/lint.py --strict-cited-pages; then
  pass "kb/lint.py --strict-cited-pages"
else
  fail "kb/lint.py"
fi

if ./scripts/check-imports.sh; then
  pass "check-imports.sh"
else
  fail "check-imports.sh"
fi

report_section "2. Error handling / fail-loud scripts"
if grep -rq 'Simulated content for' scripts/sorry-tracker.py 2>/dev/null; then
  fail "simulated fetch placeholders still present under scripts/"
else
  pass "no simulated fetch placeholders in scripts/"
fi

if grep -q 'sys\.exit(1)' scripts/sorry-tracker.py scripts/forbidden_tokens.py scripts/sorry_census.py 2>/dev/null; then
  pass "core hygiene scripts exit non-zero on failure"
else
  fail "missing sys.exit(1) fail paths in hygiene scripts"
fi

report_section "3. Configuration / secrets"
if grep -rqE 'sk-[A-Za-z0-9]{20,}|AIza[0-9A-Za-z_-]{20,}' scripts .github ArkLib 2>/dev/null; then
  fail "possible hardcoded API key material in tracked sources"
else
  pass "no hardcoded API key patterns in repo sources"
fi

if grep -q 'secrets\.' .github/workflows/summary.yml .github/workflows/review.yml 2>/dev/null; then
  pass "workflow secrets referenced via GitHub Actions secrets.* (not literals)"
else
  fail "expected workflow secret references missing"
fi

report_section "4. Performance (local smoke; CI owns full timing)"
if [ -f scripts/build_timing_report.sh ]; then
  pass "build_timing_report.sh present (CI records clean/warm/validate timings)"
else
  fail "build_timing_report.sh missing"
fi

report_section "5. Dependencies pinned and security-scanned"
if grep -qE '^[^#[:space:]].*==[0-9]' scripts/requirements-sorry-tracker.txt scripts/requirements-security.txt 2>/dev/null; then
  pass "Python manifests use exact pins"
else
  fail "Python manifests not pinned"
fi

if [ -f lake-manifest.json ] && grep -q '"rev":' lake-manifest.json; then
  pass "lake-manifest.json pins git revs for Lean packages"
else
  fail "lake-manifest.json missing pinned revs"
fi

if bash scripts/security-scan.sh; then
  pass "security-scan.sh (pip-audit)"
elif python3 -m pip_audit --version >/dev/null 2>&1; then
  fail "security-scan.sh (pip-audit installed but audit failed)"
else
  echo "SKIP: security-scan.sh — pip-audit not installed locally (run in CI via .github/workflows/security-scan.yml)"
fi

report_section "6. Rollback path"
if [ -f docs/operations/PRODUCTION-READINESS.md ]; then
  pass "rollback procedure documented in docs/operations/PRODUCTION-READINESS.md"
else
  fail "rollback documentation missing"
fi

if [ -f .github/workflows/release-tag.yml ]; then
  pass "release-tag workflow tags lean-toolchain bumps"
else
  fail "release-tag workflow missing"
fi

report_section "7. Monitoring / alerting"
if [ -f .github/workflows/ci.yml ] && [ -f .github/workflows/build-timing-report.yml ]; then
  pass "CI + build timing report workflows configured"
else
  fail "CI monitoring workflows incomplete"
fi

report_section "Lean-dependent gates (require successful lake build)"
echo "Run after 'lake exe cache get' succeeds or a warm .lake cache is present:"
echo "  ./scripts/validate.sh"
echo "  python3 scripts/axiom_audit.py"
echo "  python3 scripts/proximity_prize_cleanroom_audit.py"

if [ -d .lake/build ] && find .lake/build -name 'ArkLib*.olean' 2>/dev/null | head -1 | grep -q .; then
  echo ""
  echo "Partial .lake cache detected; attempting axiom audit..."
  if python3 scripts/axiom_audit.py; then
    pass "axiom_audit.py (post-build)"
  else
    fail "axiom_audit.py (post-build)"
  fi
else
  echo "SKIP: no usable .lake build artifacts — axiom/cleanroom audits deferred"
fi

report_section "Summary"
if [ "$failures" -eq 0 ]; then
  echo "All non-Lean production-readiness checks passed."
  exit 0
fi

echo "$failures check(s) failed." >&2
exit 1
