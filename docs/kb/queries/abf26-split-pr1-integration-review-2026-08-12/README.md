# PR 701 integration review — 2026-08-12

Third review of PR 701 (*ABF26 foundations and code families*, split 2/4), at head `b425ef51b`.

Scope chosen to complement, not repeat, the two existing records:

- [`../abf26-split-pr1-review-2026-08-07/`](../abf26-split-pr1-review-2026-08-07/README.md) —
  immutable evidence for candidate `3c303efa`.
- [`../abf26-split-pr1-deep-review-2026-08-11/`](../abf26-split-pr1-deep-review-2026-08-11/README.md)
  — eleven-reviewer pre-merge pass at `103ffe89a`, one HIGH + ~14 MEDIUM, remediation applied.

This pass covers three things those two could not:

1. **The four commits that postdate them** — the `103ffe89a` remediation itself
   (`3d0d42f72`, `fbb8b40fa`) and the *new* module-alphabet material added afterwards
   (`0fed05006`, `b425ef51b`: the MDS rate-distance equations, the two Johnson consumers,
   the interleaved distance/rate layer, and the extension-code bridge).
2. **First-hand source re-derivation** rather than trust in the earlier records: the pinned
   ABF26 tex, `abf26-refs/ABF26.pdf`, and `abf26-refs/GuruswamiK16.pdf` were read directly for
   every §2/§3 item this PR claims.
3. **Repo integration against the live PR queue** — the question "does this land well in
   ArkLib as it actually is today", tested by building merged trees rather than by inspection.

## Contents

- [`VERDICT.md`](VERDICT.md) — gates, faithfulness table, the eleven compiled probes, findings
  F1–F12, and the forward-looking items FW1–FW5.

## Outcome

**GO on the mathematics.** Nothing false, nothing vacuous, no new admit or axiom, every headline
declaration axiom-clean, all gates green. The material is faithful to the sources — including
three places where it is deliberately and correctly *sharper* than what the papers print.

One HIGH finding, and it is not mathematical: the `namespace Probability` consolidation is a
breaking change to a shared API that **seven open PRs depend on**, demonstrated by building the
merged trees. Five MEDIUM findings are documentation drift left by the 2026-08-11 remediation
itself (renamed and relocated declarations that the KB pages still name at their old
names/locations), plus one docstring over-claim. The rest is polish.

**All findings F2–F12 and FW1 were remediated in-tree**; F1 was resolved by the owner as
*merge as-is and announce*, so the migration path is documented in
`docs/wiki/probability-conventions.md` rather than papered over with aliases. See
`VERDICT.md` § *Remediation applied*, and § *Remaining, deliberately not changed here* for the
three items that belong to other branches.

## Method notes worth reusing

- **Build the merge, don't read it.** `git merge-tree` reported #692 × #701 as conflict-free;
  the merged tree then *failed to build*. Textual cleanliness is not compatibility.
- **`ef-millenium.pdf` in the author repo is a stale build** and disagrees with the tex beside
  it on definition numbering. `abf26-refs/ABF26.pdf` is the artefact whose numbering the Lean
  docstrings use, and it agrees with the pinned tex. Always cross-check which PDF is being read.
- Docstring claims of the form "counterexample checked by machine at …" were re-derived by
  *instantiating the shipped theorem* at those parameters, which turns the claim from an
  assertion into a machine-checked consequence. Probe A does this for the FRS
  non-divisibility counterexample.
- A `grep` of Markdown for backticked identifiers, checked against the declaration names in
  `ArkLib/`, found all five stale-name findings mechanically. Worth turning into a lint gate.
