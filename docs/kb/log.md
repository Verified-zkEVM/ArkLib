# Knowledge Base Log

This file is append-only.
Each entry records a notable KB event: initialization, ingest, audit creation, or major update.

## [2026-04-15] initialize | docs/kb

Created the initial knowledge-base subtree:

- `docs/kb/README.md`
- `docs/kb/index.md`
- `docs/kb/log.md`
- `docs/kb/papers/`
- `docs/kb/concepts/`
- `docs/kb/audits/`
- `docs/kb/queries/`
- `docs/kb/sources/`
- `docs/kb/_generated/`

## [2026-04-15] seed | initial paper pages

Seeded the first repository-local paper pages for currently active or already cited references:

- `ACFY24`
- `ACFY24stir`
- `BCIKS20`
- `BCS16`
- `BBS24`
- `DP24`

## [2026-04-15] seed | citation coverage stubs

Scaffolded paper pages and source metadata for the remaining citation keys currently used in
`ArkLib/**/*.lean`:

- `AHIV22`
- `BSS08`
- `FRI1216`
- `GWZC19`
- `JM24`
- `LFKN92`
- `LPS24`
- `PS94`
- `Poseidon2`
- `STIR2005`
- `Spi95`
- `codingtheory`
- `listdecoding`

## [2026-04-15] generate | bibliography and citation registries

Added initial generated outputs:

- `docs/kb/_generated/references.json`
- `docs/kb/_generated/lean-citations.json`

using the new scripts under `scripts/kb/`.

## [2026-04-15] migrate | list-decoding audit

Promoted the existing paper audit into:

- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`

and updated tracked wiki navigation to point to the KB copy rather than to a branch-local
untracked file.

## [2026-04-15] refine | high-value paper pages

Replaced initial stubs with ArkLib-specific summaries for:

- `AHIV22`
- `LFKN92`
- `GWZC19`
- `FRI1216`

These are now better landing pages for active review and protocol work in the `InterleavedCode`,
`Sumcheck`, `Plonk`, and `Fri` subtrees.

## [2026-04-15] automate | review context helper

Added:

- `scripts/kb/review_context.py`

to resolve citation keys, KB paper pages, source metadata, and public URLs from explicit keys or
changed Lean files, with output shaped for `.github/workflows/review.yml`.

## [2026-04-15] refine | second paper-page batch

Replaced initial stubs with ArkLib-specific summaries for:

- `JM24`
- `LPS24`
- `Poseidon2`
- `BSS08`
- `STIR2005`
- `listdecoding`
- `codingtheory`

This improves the KB coverage for the `AGM`, `Data/Hash`, `ProofSystem/Stir`, and
`JohnsonBound` areas.

## [2026-04-15] refine | final cited-paper stubs

Replaced the remaining cited-paper stubs with ArkLib-specific summaries for:

- `PS94`
- `Spi95`

and added a concept hub:

- `docs/kb/concepts/polishchuk-spielman-lineage.md`

for the corrected-vs-original Polishchuk-Spielman source lineage.

## [2026-05-03] audit | BCIKS20 Appendix A rational functions

Added:

- `docs/kb/audits/bciks20-appendix-a-rational-functions.md`

to track the rational-function and Hensel-lifting declarations supporting the BCIKS20
list-decoding branch.

## [2026-05-03] prove | BCIKS20 function-field regularity API

Updated `ArkLib/Data/Polynomial/RationalFunctions.lean` with an explicit function-field `T`
variable, regular-element closure lemmas, and a concrete low-degree `ξ` regularity helper.
The Appendix A rational-functions audit now records this as the next denominator-clearing layer
toward `RationalFunctions.HenselNumerators.xi_regular`.

## [2026-06-16] seed | MCA and interleaving references

Seeded paper pages and source metadata for:

- `BCGM25`
- `DG25`
- `Jo26`

and updated the Reed-Solomon proximity concept page to include the current MCA-generator and
interleaved-code reference lineage.

## [2026-06-16] refine | interleaving MCA audit target

Updated the list-decoding and correlated-agreement audit to record `Jo26` as the sharper follow-up
target for the missing interleaving-vs-MCA theorem once ArkLib has a general MCA error-function
interface.

## [2026-08-04] prove | BCIKS20 Claim A.2 restructure and Lean 4.31 migration

Merged `main` (Lean 4.31) into the rational-functions branch and reorganized Appendix A.4:
`exists_hensel_numerator_sequence` now states existence only, so `betaSeq`, `alpha`, `gamma` and the
list-decoding consumers in `BCIKS20/ListDecoding/Agreement.lean` are axiom-clean; the weight bounds
moved to `hensel_numerator_weight_sharp_le` / `hensel_numerator_weight_le`, with the paper's bundled
form kept as `claimA2_exists_numerators_with_weight_bounds`. The sharp bound
`Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)` is now exposed alongside the loose `(2t+1)dD`, because Claim 5.10
needs the sharp form to telescope over `t`.

Two findings recorded in the Appendix A audit: Claim A.2 presupposes `2 ≤ degY R` (now a hypothesis;
the unrestricted Lean statement was false), and the `(A.1)`-recursion route cannot prove the weight
bound because it is exactly tight — the remaining `sorry` is that single boundary summand.

Declaration names were also brought in line with the Mathlib style guide: `H_tilde`/`H_tilde'` →
`monicizeRatFunc`/`monicize`, `weight_Λ`/`weight_Λ_over_𝒪` → `weight`/`regularWeight`, `RWL_*` →
`regularWeightLe_*`, `S_β` → `rationalVanishingSet`, and Greek declaration names → `zeta`, `xi`,
`alpha`, `gamma`, `beta`, `piZ` (Greek is kept for variables and in prose).
