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
SORRY_BASELINE="$FIXTURE_TMP/sorry-growth.json"
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

# A stale allowlist must not freeze cleanup: removals stay green and prompt the
# contributor to shrink the baseline in the same change.
expect_status 0 stale-baseline-removal \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Clean \
    --check --baseline "$COVERING_BASELINE"
grep -q "good news" "$FIXTURE_TMP/stale-baseline-removal.log"

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

# Intentional `sorryAx` debt can be written explicitly, reviewed, and then passes the check.
cp "$EMPTY_BASELINE" "$SORRY_BASELINE"
expect_status 0 allow-sorry-growth \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted.DirectSorry \
    --update-baseline --baseline "$SORRY_BASELINE"
grep -q 'directSorry' "$SORRY_BASELINE"
expect_status 0 covered-sorry \
  lake exe axiomsweep --root AxiomSweepTestFixtures.Tainted.DirectSorry \
    --check --baseline "$SORRY_BASELINE"

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

# --- --must-depend-on: required proof dependencies ---------------------------------------
#
# Fixtures live in `AxiomSweepTestFixtures.MustDependOn`; each requirement file below holds
# one requirement on one fixture theorem. `1` is an unmet-requirement verdict, `2` a
# configuration or infrastructure error, exactly as for the baseline gate.

MDO="AxiomSweepTestFixtures.MustDependOn"

# requirement FILE THEOREM MODULE DEP... — write a one-requirement file.
requirement() {
  local out="$1" theorem="$2" module="$3"
  shift 3
  local deps
  deps="$(printf '"%s", ' "$@")"
  printf '{"requirements": [{"theorem": "%s", "module": "%s", "mustDependOn": [%s]}]}\n' \
    "$theorem" "$module" "${deps%, }" >"$out"
}

# must_depend_on STATUS LABEL THEOREM DEP... — check one requirement on a fixture theorem.
must_depend_on() {
  local status="$1" label="$2" theorem="$3"
  shift 3
  requirement "$FIXTURE_TMP/$label.json" "$MDO.$theorem" "$MDO" "$@"
  expect_status "$status" "$label" \
    lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/$label.json"
}

# Used in the proof: directly, through an intermediate lemma, through a private lemma (named
# as in source), and through a generated `_proof_` auxiliary of a definition.
must_depend_on 0 mdo-direct usesDirectly "$MDO.sharedLaw"
must_depend_on 0 mdo-transitive usesTransitively "$MDO.sharedLaw" "$MDO.intermediate"
grep -q "usesTransitively -> $MDO.intermediate -> $MDO.sharedLaw" \
  "$FIXTURE_TMP/mdo-transitive.log"
must_depend_on 0 mdo-private usesThroughPrivate "$MDO.sharedLaw" "$MDO.privateStep"
grep -q "_private\..*privateStep -> $MDO.sharedLaw" "$FIXTURE_TMP/mdo-private.log"
must_depend_on 0 mdo-aux-proof usesThroughAuxProof "$MDO.sharedLaw"
grep -q "usesThroughAuxProof\._proof_1 -> $MDO.sharedLaw" "$FIXTURE_TMP/mdo-aux-proof.log"

# Not used: absent altogether, named only by the statement (a definition, and a theorem),
# and named only by the statement of a lemma the proof applies.
must_depend_on 1 mdo-absent independent "$MDO.sharedLaw"
grep -q "UNMET.*sharedLaw: not used by the proof" "$FIXTURE_TMP/mdo-absent.log"
must_depend_on 1 mdo-const-type-only constOnlyInType "$MDO.sharedConst"
grep -q "UNMET.*sharedConst: named by the statement" "$FIXTURE_TMP/mdo-const-type-only.log"
must_depend_on 1 mdo-law-type-only lawOnlyInType "$MDO.sharedLaw"
grep -q "UNMET.*sharedLaw: named by the statement" "$FIXTURE_TMP/mdo-law-type-only.log"
must_depend_on 1 mdo-wrapper-type-only constOnlyInWrapperType "$MDO.sharedConst"

# stmt_depends_on STATUS LABEL THEOREM DEP... — the same, for a theorem of the separate
# consumer module `$MDO.Statement`.
MDS="$MDO.Statement"
stmt_depends_on() {
  local status="$1" label="$2" theorem="$3"
  shift 3
  requirement "$FIXTURE_TMP/$label.json" "$MDS.$theorem" "$MDS" "$@"
  expect_status "$status" "$label" \
    lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/$label.json"
}
THROUGH_STATEMENT="reachable only through constants named by the statement"

# Statement blocking: a proof term repeats its statement's constants (binder types, `rfl`
# arguments), and those constants' bodies must not count as use.
stmt_depends_on 1 mdo-stmt-relation stmtRelIdentity "$MDO.sharedLaw"
grep -q "$THROUGH_STATEMENT" "$FIXTURE_TMP/mdo-stmt-relation.log"
stmt_depends_on 1 mdo-stmt-instance stmtInstance "$MDO.sharedLaw"
grep -q "$THROUGH_STATEMENT" "$FIXTURE_TMP/mdo-stmt-instance.log"
stmt_depends_on 1 mdo-stmt-def-binder stmtDefInBinder "$MDO.sharedLaw"
grep -q "$THROUGH_STATEMENT" "$FIXTURE_TMP/mdo-stmt-def-binder.log"
stmt_depends_on 1 mdo-stmt-structure-binder stmtStructureInBinder "$MDO.sharedLaw"
grep -q "$THROUGH_STATEMENT" "$FIXTURE_TMP/mdo-stmt-structure-binder.log"

# Dead code is not use: a `have` the proof never consults, by value or by type.
stmt_depends_on 1 mdo-dead-have deadHave "$MDO.sharedLaw"
grep -q "UNMET.*sharedLaw: not used by the proof" "$FIXTURE_TMP/mdo-dead-have.log"
stmt_depends_on 1 mdo-dead-have-type deadHaveType "$MDO.sharedLaw"
grep -q "UNMET.*sharedLaw: not used by the proof" "$FIXTURE_TMP/mdo-dead-have-type.log"
# Dead code is removed to a fixpoint: a chain of unused `have`s, a `have` consumed only by a
# discarding redex, nested discarding redexes, and an `obtain`ed proof whose fields are unused.
stmt_depends_on 1 mdo-dead-have-chain deadHaveChain "$MDO.sharedLaw"
stmt_depends_on 1 mdo-dead-have-then-redex deadHaveThenRedex "$MDO.sharedLaw"
stmt_depends_on 1 mdo-dead-nested-redex deadNestedRedex "$MDO.sharedLaw"
stmt_depends_on 1 mdo-dead-obtain deadObtain "$MDO.sharedLaw"
for label in mdo-dead-have-chain mdo-dead-have-then-redex mdo-dead-nested-redex \
  mdo-dead-obtain; do
  grep -q "UNMET.*sharedLaw: not used by the proof" "$FIXTURE_TMP/$label.log"
done
# ...but an `obtain`ed proof whose fields are used still counts, and so does eliminating an
# empty proposition, whose proof is the only one there is.
stmt_depends_on 0 mdo-use-obtain useObtain "$MDO.sharedLaw"
stmt_depends_on 0 mdo-use-obtain-false useObtainFalse "$MDO.sharedLaw"
stmt_depends_on 0 mdo-use-cases-false useCasesFalse "$MDO.sharedLaw"

# A gap the proof relies on fails the requirement even when the dependency is used: directly,
# and in a helper.
stmt_depends_on 1 mdo-sorry useWithSorry "$MDO.sharedLaw"
grep -q "depends on sorryAx" "$FIXTURE_TMP/mdo-sorry.log"
stmt_depends_on 1 mdo-sorry-helper useThroughSorriedHelper "$MDO.sharedLaw"
grep -q "via $MDS.useThroughSorriedHelper -> $MDO.sorriedHelper -> sorryAx" \
  "$FIXTURE_TMP/mdo-sorry-helper.log"
# Only gaps the proof relies on count: admitted debt inside an object the statement names
# does not block a sorry-free proof.
stmt_depends_on 0 mdo-sorry-in-statement useWithAdmittedStatement "$MDO.sharedLaw"
grep -q "note .*reachable only through constants the statement names.*admittedObject" \
  "$FIXTURE_TMP/mdo-sorry-in-statement.log"
# The same when the proof projects the admitted law field out of the statement's object.
stmt_depends_on 0 mdo-sorry-projected useAdmittedField "$MDO.sharedLaw"
grep -q "note .*reachable only through constants the statement names.*admittedLaw" \
  "$FIXTURE_TMP/mdo-sorry-projected.log"

# Documented false negative: `simp only` with an `rfl` lemma leaves no trace.
stmt_depends_on 1 mdo-simp-rfl simpRflUse "$MDO.myId_eq"

# Genuine use from the consumer module keeps passing: through an instance or a projection
# the statement does not name, by rewriting, in a match arm, in an induction step, and as a
# direct occurrence of a name the statement also mentions (reported as such).
stmt_depends_on 0 mdo-use-instance useInstance "$MDO.sharedLaw"
grep -q "useInstance -> $MDO.idLaw -> $MDO.sharedLaw" "$FIXTURE_TMP/mdo-use-instance.log"
stmt_depends_on 0 mdo-use-projection useProjection "$MDO.sharedLaw"
stmt_depends_on 0 mdo-use-rewrite useRewrite "$MDO.myId_eq"
stmt_depends_on 0 mdo-use-match useMatch "$MDO.sharedLaw"
stmt_depends_on 0 mdo-use-induction useInduction "$MDO.sharedLaw"
stmt_depends_on 0 mdo-use-named-by-statement useNamedByStatement "$MDO.sharedLaw"
grep -q "also named by the statement" "$FIXTURE_TMP/mdo-use-named-by-statement.log"

# One unmet dependency fails the requirement even when the others are met, and one unmet
# requirement fails the file even when the others pass.
must_depend_on 1 mdo-partial usesTransitively "$MDO.sharedLaw" "$MDO.sharedConst"
grep -q "ok .*sharedLaw" "$FIXTURE_TMP/mdo-partial.log"
grep -q "UNMET.*sharedConst" "$FIXTURE_TMP/mdo-partial.log"
printf '{"requirements": [
  {"theorem": "%s.usesDirectly", "module": "%s", "mustDependOn": ["%s.sharedLaw"]},
  {"theorem": "%s.independent", "module": "%s", "mustDependOn": ["%s.sharedLaw"],
   "note": "free text"}]}\n' \
  "$MDO" "$MDO" "$MDO" "$MDO" "$MDO" "$MDO" >"$FIXTURE_TMP/mdo-mixed.json"
expect_status 1 mdo-mixed \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-mixed.json"

# Configuration errors are never a pass and never a verdict.
must_depend_on 2 mdo-unknown-dependency usesDirectly "$MDO.noSuchLemma"
grep -q "unknown declaration $MDO.noSuchLemma" "$FIXTURE_TMP/mdo-unknown-dependency.log"
must_depend_on 2 mdo-unknown-theorem noSuchTheorem "$MDO.sharedLaw"
grep -q "unknown declaration $MDO.noSuchTheorem" "$FIXTURE_TMP/mdo-unknown-theorem.log"
must_depend_on 2 mdo-no-proof-term noProof "$MDO.sharedLaw"
grep -q "has no proof term" "$FIXTURE_TMP/mdo-no-proof-term.log"
# The configured module imports the subject's module, so the subject is in the environment
# but declared elsewhere.
requirement "$FIXTURE_TMP/mdo-wrong-module.json" "$MDO.usesDirectly" "$MDS" "$MDO.sharedLaw"
expect_status 2 mdo-wrong-module \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-wrong-module.json"
grep -q "is declared in $MDO, not in the configured module $MDS" \
  "$FIXTURE_TMP/mdo-wrong-module.log"
requirement "$FIXTURE_TMP/mdo-bad-module.json" "$MDO.usesDirectly" NoSuchModule \
  "$MDO.sharedLaw"
expect_status 2 mdo-bad-module \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-bad-module.json"
printf '{"requirements": [{"theorem": "%s.usesDirectly", "module": "%s", "mustDependOn": []}]}\n' \
  "$MDO" "$MDO" >"$FIXTURE_TMP/mdo-no-dependencies.json"
expect_status 2 mdo-no-dependencies \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-no-dependencies.json"
printf '{"requirements": [
  {"theorem": "%s.usesDirectly", "module": "%s", "mustDependOn": ["%s.sharedLaw"]},
  {"theorem": "%s.usesDirectly", "module": "%s", "mustDependOn": ["%s.sharedConst"]}]}\n' \
  "$MDO" "$MDO" "$MDO" "$MDO" "$MDO" "$MDO" >"$FIXTURE_TMP/mdo-duplicate.json"
expect_status 2 mdo-duplicate \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-duplicate.json"
must_depend_on 2 mdo-self-reference usesDirectly "$MDO.usesDirectly"
# Two spellings of one private declaration (as in source, and fully mangled) are one name.
must_depend_on 2 mdo-duplicate-spelling usesThroughPrivate "$MDO.privateStep" \
  "_private.$MDO.0.$MDO.privateStep"
grep -q "more than once" "$FIXTURE_TMP/mdo-duplicate-spelling.log"
printf '{"requirements": [{"theorem": "%s.usesDirectly", "module": "%s"}]}\n' \
  "$MDO" "$MDO" >"$FIXTURE_TMP/mdo-misspelt-field.json"
expect_status 2 mdo-misspelt-field \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-misspelt-field.json"
printf '{"requirements": [{"theorem": "%s.usesDirectly", "module": "%s",
  "mustDependOn": ["%s.sharedLaw"], "mustAlsoDependOn": ["%s.sharedConst"]}]}\n' \
  "$MDO" "$MDO" "$MDO" "$MDO" >"$FIXTURE_TMP/mdo-unknown-key.json"
expect_status 2 mdo-unknown-key \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-unknown-key.json"
grep -q 'unknown key "mustAlsoDependOn"' "$FIXTURE_TMP/mdo-unknown-key.log"
printf '{"requirements": [], "extra": 1}\n' >"$FIXTURE_TMP/mdo-unknown-top-key.json"
expect_status 2 mdo-unknown-top-key \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-unknown-top-key.json"
expect_status 2 mdo-invalid-file \
  lake exe axiomsweep --must-depend-on --requirements "$INVALID_BASELINE"
expect_status 2 mdo-missing-file \
  lake exe axiomsweep --must-depend-on --requirements "$MISSING_BASELINE"
expect_status 2 mdo-conflicting-flags \
  lake exe axiomsweep --must-depend-on --check
expect_status 2 mdo-conflicting-baseline \
  lake exe axiomsweep --must-depend-on --baseline "$EMPTY_BASELINE"
expect_status 2 mdo-requirements-without-mode \
  lake exe axiomsweep --requirements "$FIXTURE_TMP/mdo-direct.json"

# An empty requirement list imports nothing and passes. (The committed
# `scripts/must_depend_on.json` is checked by `validate.sh --axioms`, after `lake test`
# has built the conformance modules it names; this harness does not depend on them.)
printf '{"requirements": []}\n' >"$FIXTURE_TMP/mdo-empty.json"
expect_status 0 mdo-empty \
  lake exe axiomsweep --must-depend-on --requirements "$FIXTURE_TMP/mdo-empty.json"
grep -q "no must-depend-on requirements" "$FIXTURE_TMP/mdo-empty.log"

echo "✓ Axiom sweep executable fixture matrix passed."
