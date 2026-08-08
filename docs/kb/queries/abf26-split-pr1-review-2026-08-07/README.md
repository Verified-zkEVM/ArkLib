# PR #701 adversarial review — 2026-08-07

Full fresh adversarial review of [#701](https://github.com/Verified-zkEVM/ArkLib/pull/701)
(*feat(coding-theory): ABF26 foundations and code families [split 2/4]*) at head `ffa0733a`,
against `origin/main` `02d759d5` (merge-base `4f386913`).

Start with **[`VERDICT.md`](VERDICT.md)** — the consolidated verdict, the paper-defect table,
and the prioritised fix list. The `R*.md` files are the eleven independent cluster reports it
consolidates.

| Report | Cluster |
|---|---|
| [`R1-probability.md`](R1-probability.md) | `Data/Probability/Instances.lean` namespace migration, `Notation.lean`, `Fin/Basic.lean`, the six `open Probability` consumers |
| [`R2-combinatorial.md`](R2-combinatorial.md) | `Data/Probability/Combinatorial.lean` (ABF26 Claim B.1) |
| [`R3-distance-list.md`](R3-distance-list.md) | `Basic/Distance.lean`, `Basic/RelativeDistance.lean`, `Basic/Entropy.lean`, `HammingBallVolume.lean`, `ListDecodability.lean`, `Erasure.lean` |
| [`R4-johnson.md`](R4-johnson.md) | `JohnsonBound/*`, `Basic/LinearCode.lean` |
| [`R5-rs-families.md`](R5-rs-families.md) | `ReedSolomon/{Folded,Interleaved,Multiplicity}.lean` |
| [`R6-subspace-wronskian.md`](R6-subspace-wronskian.md) | `SubspaceDesign.lean`, `Data/Polynomial/FoldedWronskian.lean` (the two crown jewels) |
| [`R7-extension-codes.md`](R7-extension-codes.md) | `ExtensionCodes.lean` |
| [`R8-duplication.md`](R8-duplication.md) | Cross-cutting duplication / missed-generalization audit |
| [`R9-vacuity-axioms.md`](R9-vacuity-axioms.md) | Cross-cutting vacuity, axiom hygiene, build/lint hygiene |
| [`R10-docs-integration.md`](R10-docs-integration.md) | Docs accuracy, conventions compliance, repo integration |
| [`R11-library-value.md`](R11-library-value.md) | Consumer analysis, reusability, "progresses the library" bar |

## Headline

**0 CRITICAL · 2 HIGH · 42 MEDIUM · 65 LOW.** No false statement, no vacuous hypothesis set,
no trivially-true conclusion, no proof cheat, no `sorry`, no non-standard axiom. Both HIGH
findings are duplication / missed generalization. The two formerly-admitted crown jewels
(ABF26 L2.17, T2.18) are genuinely proven, and T2.18 is a faithful, correctly-streamlined
rendering of [GK16] Theorem 14 that additionally *proves* the irreducibility of
`X^{q−1} − ω` that [GK16] only asserts.

Three defects in the source paper were found and validated with compiled counterexamples —
see `VERDICT.md` §3. Two of them (the inverted Johnson list factor, the missing `ω`-order
condition on Thm 2.18) were already known and handled; the third (Thm 2.18 is false when
`0 ∈ L`, *even with* the order condition) is new and should go upstream.

## These reports are a snapshot, deliberately not updated

Every report here describes the tree **as reviewed, at `ffa0733a`**, and is left that way on
purpose so the findings stay checkable against the commit they were made against. Fixes were
applied afterwards in the same PR, so declaration names and line numbers quoted below may no
longer resolve. Notably `additive_code_supports_erasure_correction_grs12` was renamed to
`exists_erasure_corrector`, `Polynomial.pow_dvd_det_of_forall_mem_col_dvd` moved to
`Matrix.pow_dvd_det_of_forall_mem_col_dvd`, and `Fin.induction_three`/`'` were deleted.
For the current state of the tree, read
[`../../audits/open-problems-list-decoding-and-correlated-agreement.md`](../../audits/open-problems-list-decoding-and-correlated-agreement.md)
and the module docstrings, not these reports.

## A note on paths

The reports cite `(session-local probe)` files and a few `SCRATCH/*` logs. Those were
per-reviewer scratch artifacts (compiled Lean probes, build and lint logs) from the review
session and are **not committed** — the reports quote the relevant statements and outputs
inline, so each finding stands on the evidence reproduced in the text. Reference PDFs live
outside the repo in `~/abf26-refs/`; see
[`../../sources/README.md`](../../sources/README.md) for the source-access convention.
