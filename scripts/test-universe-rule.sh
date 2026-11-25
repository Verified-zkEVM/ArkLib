#!/usr/bin/env bash

# Check `lake exe universe-rule` against the fixtures in scripts/UniverseRuleTestFixtures/:
# the passing module, the failing module, and the allowlist directions (an unlisted violation,
# a stale entry, a malformed entry).

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

FIXTURE_TMP="$(mktemp -d "${TMPDIR:-/tmp}/arklib-universe-rule.XXXXXX")"
trap 'rm -rf -- "$FIXTURE_TMP"' EXIT

FIXTURES=scripts/UniverseRuleTestFixtures
PASS=UniverseRuleTestFixtures.Pass
FAIL=UniverseRuleTestFixtures.Fail

# Run the checker, require exit status $1, and keep standard output in $FIXTURE_TMP/$2.out.
expect_status() {
  local expected="$1"
  local label="$2"
  shift 2
  local actual=0
  lake exe universe-rule "$@" >"$FIXTURE_TMP/$label.out" 2>"$FIXTURE_TMP/$label.err" || actual=$?
  if [[ "$actual" -ne "$expected" ]]; then
    echo "ERROR: $label: universe-rule returned $actual; expected $expected" >&2
    cat "$FIXTURE_TMP/$label.out" "$FIXTURE_TMP/$label.err" >&2
    exit 1
  fi
}

# Require standard output of case $1 to equal the remaining arguments, one line each.
expect_lines() {
  local label="$1"
  shift
  printf '%s\n' "$@" >"$FIXTURE_TMP/$label.expected"
  if ! diff -u "$FIXTURE_TMP/$label.expected" "$FIXTURE_TMP/$label.out" >&2; then
    echo "ERROR: $label: unexpected violations" >&2
    exit 1
  fi
}

lake build UniverseRuleTestFixtures universe-rule

: >"$FIXTURE_TMP/empty.txt"

# The passing module: argument universes, a monad result universe, generated constants, and an
# adversary universe that the fixture allowlist covers.
expect_status 0 pass --root "$PASS" --allowlist "$FIXTURES/allowlist.txt"
expect_lines pass "$PASS $PASS.AdversaryModel w"

# Without the allowlist, the adversary universe is a violation.
expect_status 1 pass-unlisted --root "$PASS" --allowlist "$FIXTURE_TMP/empty.txt"

# An entry that matches no violation fails. The allowlist can therefore only shrink.
cp "$FIXTURES/allowlist.txt" "$FIXTURE_TMP/stale.txt"
echo "$PASS $PASS.pick u # pending: fixed already" >>"$FIXTURE_TMP/stale.txt"
expect_status 1 pass-stale --root "$PASS" --allowlist "$FIXTURE_TMP/stale.txt"
grep -q "match no violation" "$FIXTURE_TMP/pass-stale.err"

# An entry without a reason is malformed.
echo "$PASS $PASS.AdversaryModel w" >"$FIXTURE_TMP/no-reason.txt"
expect_status 2 pass-no-reason --root "$PASS" --allowlist "$FIXTURE_TMP/no-reason.txt"

# The failing module: a constant without arguments, a universe that only a structure field
# mentions, one that only the result type mentions, a hand-written instance, and one that only
# a `Prop` body mentions. Each structure is reported once, not its constructor, projection or
# derived instance.
expect_status 1 fail --root "$FAIL" --allowlist "$FIXTURE_TMP/empty.txt"
expect_lines fail \
  "$FAIL $FAIL.Bundle u" \
  "$FAIL $FAIL.HasWitness k" \
  "$FAIL $FAIL.Marker u" \
  "$FAIL $FAIL.instInhabitedMarker u" \
  "$FAIL $FAIL.lift v" \
  "$FAIL $FAIL.noArgs u"

# Report mode lists the same violations and exits 0. `--explain-skips` shows that the skip rules
# hid the generated constants: the derived instances, the constructor and the `sizeOf` instance.
expect_status 0 fail-report --root "$FAIL" --report --explain-skips
cmp "$FIXTURE_TMP/fail.out" "$FIXTURE_TMP/fail-report.out"
for skipped in \
  "$FAIL.instNonemptyBundle u_1 (derived instance for $FAIL.Bundle)" \
  "$FAIL.instReprMarker u_1 (derived instance for $FAIL.Marker)" \
  "$FAIL.Marker.mk u (constructor)" \
  "$FAIL.Bundle._sizeOf_inst u (internal name)"; do
  if ! grep -Fq -- "$skipped" "$FIXTURE_TMP/fail-report.err"; then
    echo "ERROR: fail-report: expected the skip \`$skipped\`" >&2
    cat "$FIXTURE_TMP/fail-report.err" >&2
    exit 1
  fi
done

echo "Universe rule fixtures passed"
