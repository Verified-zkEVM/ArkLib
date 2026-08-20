#!/usr/bin/env bash

# Execute falsifiable fixtures for the kernel-level axiom sweep.
#
# Ported from PolyFun's `scripts/test-axiomsweep.sh` via VCV-io, with the exit-code
# matrix matching ArkLib's policy: the baseline is an allowlist for `sorryAx` debt
# (PolyFun forbids a nonempty baseline outright; ArkLib carries genuine work in
# progress), while native trust is held to the same zero-debt rule through
# `neverAllowlistable`.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

FIXTURE_TMP="$(mktemp -d "${TMPDIR:-/tmp}/arklib-axiomsweep.XXXXXX")"
trap 'rm -rf -- "$FIXTURE_TMP"' EXIT

expect_status() {
  local expected="$1"
  local label="$2"
  shift 2
  local log="$FIXTURE_TMP/${label}.log"
  local actual=0
  "$@" >"$log" 2>&1 || actual=$?
  if [[ "$actual" -ne "$expected" ]]; then
    echo "ERROR: $label returned $actual; expected $expected" >&2
    sed -n '1,160p' "$log" >&2
    return 1
  fi
}

EMPTY_BASELINE="$FIXTURE_TMP/empty.json"
INVALID_BASELINE="$FIXTURE_TMP/invalid.json"
MISSING_BASELINE="$FIXTURE_TMP/missing.json"
COVERING_BASELINE="$FIXTURE_TMP/covering.json"
CLEAN_REPORT="$FIXTURE_TMP/clean.json"
TAINTED_REPORT="$FIXTURE_TMP/tainted.json"
TAINTED_REPORT_2="$FIXTURE_TMP/tainted-2.json"
UNIMPORTED_REPORT="$FIXTURE_TMP/unimported.json"

printf '{"sorry": [], "nonstandard": []}\n' >"$EMPTY_BASELINE"
printf '{not-json}\n' >"$INVALID_BASELINE"

# VCVio's FFI C sources live in git submodules that Lake does not fetch, and every
# root-package executable links them.
if [ -e .lake/packages/VCVio/.git ]; then
  git -C .lake/packages/VCVio submodule update --init --recursive
fi

lake build AxiomSweepTestFixtures
lake exe axiomsweep --root AxiomSweepTestFixtures.Clean --out "$CLEAN_REPORT"
lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted --out "$TAINTED_REPORT"
lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted --out "$TAINTED_REPORT_2"
lake exe axiomsweep --root AxiomSweepTestFixtures.Unimported --out "$UNIMPORTED_REPORT"

# The sweep must be deterministic: same build, byte-identical report.
cmp "$TAINTED_REPORT" "$TAINTED_REPORT_2"

python3 - "$CLEAN_REPORT" "$TAINTED_REPORT" "$UNIMPORTED_REPORT" "$COVERING_BASELINE" <<'PY'
import json
import sys

clean_path, tainted_path, unimported_path, covering_path = sys.argv[1:]

with open(clean_path, encoding="utf-8") as stream:
    clean = json.load(stream)
with open(tainted_path, encoding="utf-8") as stream:
    tainted = json.load(stream)
with open(unimported_path, encoding="utf-8") as stream:
    unimported = json.load(stream)

clean_entries = {entry["name"]: entry for entry in clean["declarations"]}
tainted_entries = {entry["name"]: entry for entry in tainted["declarations"]}
unimported_entries = {entry["name"]: entry for entry in unimported["declarations"]}

assert clean_entries
assert all(not entry["axioms"] for entry in clean_entries.values())

prefix = "AxiomSweepTestFixtures.Tainted."

# `sorryAx` reached directly, and through an intervening definition.
assert "sorryAx" in tainted_entries[prefix + "directSorry"]["axioms"]
assert "sorryAx" in tainted_entries[prefix + "transitiveSorry"]["axioms"]

# An axiom occurring only in a *type* still counts, matching Lean's `CollectAxioms`.
assert prefix + "typeIndex" in tainted_entries[prefix + "axiomInType"]["axioms"]

# The fixpoint repair pass: `MutualRight` never mentions the axiom itself, and inherits it
# only across the mutual-inductive cycle. This is the witness for the `repair` phase.
assert prefix + "mutualAxiom" in tainted_entries[prefix + "MutualRight"]["axioms"]

all_axioms = {axiom for entry in tainted_entries.values() for axiom in entry["axioms"]}

# A well-formed generated suffix collapses to its owning declaration...
generated = prefix + "Generated._native.native_decide"
assert generated in all_axioms
assert generated + ".ax_12_34" not in all_axioms

# ...and nothing else does. Collapsing these would let distinct axioms share one baseline
# key, so real taint could hide behind an accepted entry.
assert prefix + "Collision._native.native_decide.ax_12_extra" in all_axioms
assert prefix + "Collision._native.native_decide.ax_x_34" in all_axioms
assert prefix + "Collision._native.native_decide.ax_12_34.extra" in all_axioms

# A file no root transitively imports is invisible to any environment-walking census.
hidden = "AxiomSweepTestFixtures.Unimported.hiddenSorry"
assert hidden not in tainted_entries
assert hidden in unimported_entries
assert "sorryAx" in unimported_entries[hidden]["axioms"]

# A baseline that covers every tainted declaration of the fixture root, used below to
# check that full coverage is accepted and that native trust is refused even so.
covering = {
    "sorry": sorted(n for n, e in tainted_entries.items() if "sorryAx" in e["axioms"]),
    "nonstandard": [
        {"name": n, "axioms": sorted(a for a in e["axioms"]
                                     if a != "sorryAx"
                                     and a not in ("propext", "Classical.choice", "Quot.sound"))}
        for n, e in sorted(tainted_entries.items())
        if any(a != "sorryAx" and a not in ("propext", "Classical.choice", "Quot.sound")
               for a in e["axioms"])
    ],
}
with open(covering_path, "w", encoding="utf-8") as stream:
    json.dump(covering, stream)
PY

# --- gate directions -------------------------------------------------------------------

expect_status 0 clean-check \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --check --baseline "$EMPTY_BASELINE"
expect_status 1 uncovered-taint \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted \
    --check --baseline "$EMPTY_BASELINE"

# Full coverage still fails: the fixtures mint `._native.` axioms outside
# `grandfatheredNativeTrust`, and no baseline edit may green those.
expect_status 1 native-trust-floor \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted \
    --check --baseline "$COVERING_BASELINE"
grep -q "never-allowlistable" "$FIXTURE_TMP/native-trust-floor.log"

# --- infrastructure failures must never read as a taint verdict ------------------------

expect_status 2 missing-baseline \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --check --baseline "$MISSING_BASELINE"
expect_status 2 invalid-baseline \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --check --baseline "$INVALID_BASELINE"
expect_status 2 conflicting-flags \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --check --update-baseline --baseline "$EMPTY_BASELINE"
expect_status 2 unknown-flag \
  lake exe axiomsweep --bogus
expect_status 2 bad-root \
  lake exe axiomsweep --root NoSuchModule --check --baseline "$EMPTY_BASELINE"
expect_status 2 unwritable-out \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --out "$FIXTURE_TMP/no-such-dir/report.json"

# --- baseline writing -------------------------------------------------------------------

# Shrinking is allowed once the debt is gone.
cp "$COVERING_BASELINE" "$FIXTURE_TMP/shrink.json"
expect_status 0 shrink-baseline \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --update-baseline --baseline "$FIXTURE_TMP/shrink.json"
python3 -c "
import json,sys
b=json.load(open(sys.argv[1]))
assert b['sorry'] == [] and b['nonstandard'] == [], b
" "$FIXTURE_TMP/shrink.json"

# Pre-authorizing native trust is not, and the file must be left untouched.
cp "$EMPTY_BASELINE" "$FIXTURE_TMP/growth.json"
cp "$FIXTURE_TMP/growth.json" "$FIXTURE_TMP/growth-before.json"
expect_status 1 reject-native-trust-growth \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted \
    --update-baseline --baseline "$FIXTURE_TMP/growth.json"
cmp "$FIXTURE_TMP/growth-before.json" "$FIXTURE_TMP/growth.json"

echo "✓ Axiom sweep executable fixture matrix passed."
