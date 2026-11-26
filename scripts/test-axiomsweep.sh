#!/usr/bin/env bash

# Execute falsifiable fixtures for the kernel-level axiom sweep.
#
# Ported from PolyFun's `scripts/test-axiomsweep.sh` via VCV-io. ArkLib's gate is zero-debt:
# `--check` fails on any `sorryAx` or other non-standard axiom, with no allowlist.

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

CLEAN_REPORT="$FIXTURE_TMP/clean.json"
TAINTED_REPORT="$FIXTURE_TMP/tainted.json"
TAINTED_REPORT_2="$FIXTURE_TMP/tainted-2.json"
UNIMPORTED_REPORT="$FIXTURE_TMP/unimported.json"

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

uv run --no-project --python 3.12 python - "$CLEAN_REPORT" "$TAINTED_REPORT" "$UNIMPORTED_REPORT" <<'PY'
import json
import sys

clean_path, tainted_path, unimported_path = sys.argv[1:]

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

# ...and nothing else does. Collapsing these would give distinct axioms one report name.
assert prefix + "Collision._native.native_decide.ax_12_extra" in all_axioms
assert prefix + "Collision._native.native_decide.ax_x_34" in all_axioms
assert prefix + "Collision._native.native_decide.ax_12_34.extra" in all_axioms

# A file no root transitively imports is invisible to any environment-walking census.
hidden = "AxiomSweepTestFixtures.Unimported.hiddenSorry"
assert hidden not in tainted_entries
assert hidden in unimported_entries
assert "sorryAx" in unimported_entries[hidden]["axioms"]

PY

# --- gate directions -------------------------------------------------------------------

expect_status 0 clean-check \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean --check
grep -q "check passed" "$FIXTURE_TMP/clean-check.log"

# Any `sorryAx`, direct or transitive, fails the gate: there is no allowlist.
expect_status 1 sorry-check \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted.DirectSorry --check
grep -q 'directSorry : #\[sorryAx\]' "$FIXTURE_TMP/sorry-check.log"
grep -q 'transitiveSorry : #\[sorryAx\]' "$FIXTURE_TMP/sorry-check.log"

# Native trust and other non-standard axioms fail it too.
expect_status 1 tainted-check \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted --check
grep -q 'Generated._native.native_decide' "$FIXTURE_TMP/tainted-check.log"
grep -q 'AxiomSweepTestFixtures.Tainted.typeIndex' "$FIXTURE_TMP/tainted-check.log"

# --- infrastructure failures must never read as a taint verdict ------------------------

expect_status 2 unknown-flag \
  lake exe axiomsweep --bogus
expect_status 2 removed-baseline-flag \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean --update-baseline
expect_status 2 bad-root \
  lake exe axiomsweep --root NoSuchModule --check
expect_status 2 unwritable-out \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --out "$FIXTURE_TMP/no-such-dir/report.json"

echo "✓ Axiom sweep executable fixture matrix passed."
