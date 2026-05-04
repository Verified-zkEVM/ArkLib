---
kind: paper
bibkey: LFKN92
title: "Algebraic methods for interactive proof systems"
year: 1992
bib_source: blueprint/src/references.bib
canonical_url: https://doi.org/10.1145/146585.146605
source_metadata: ../sources/LFKN92/metadata.yml
status: seeded
related_modules:
  - ArkLib/ProofSystem/Sumcheck/Spec/General.lean
---

# LFKN92

## At A Glance

`LFKN92` is the classical sum-check reference.
In ArkLib it serves as the main historical and mathematical reference point for the general
sum-check protocol formalization under `ProofSystem/Sumcheck`.

## What ArkLib Uses From This Paper

- The canonical protocol story behind the sum-check protocol formalized in
  [`ArkLib/ProofSystem/Sumcheck/Spec/General.lean`](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean).
- Background for the statement shape, round structure, and target-sum update pattern used by the
  current abstract oracle-reduction formalization.

## Main ArkLib Touchpoints

- [`ArkLib/ProofSystem/Sumcheck/Spec/General.lean`](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean)
  cites `LFKN92` directly in the module docstring as the classical reference.
- The sum-check development is layered as a composition of single-round oracle reductions, so this
  page is also relevant when reading the surrounding `Spec/SingleRound` implementation.

## Version Notes

- ArkLib currently cites both `LFKN92` and `BBS24` in the sum-check module docstring.
- `LFKN92` is the mathematical origin reference; `BBS24` is the closer formal-verification
  comparison point.

## Known Divergences From ArkLib

- ArkLib formalizes sum-check inside the general `OracleReduction` framework, not as a standalone
  interactive-proof object.
- The repo uses modern Lean abstractions for oracle statements and round composition rather than the
  original paper's presentation.

## Open Formalization Gaps

- This page is a landing page, not a theorem matrix.
- If reviewers need a line-by-line comparison between the original sum-check statement and ArkLib's
  current `Spec` layer, add a dedicated audit page under `docs/kb/audits/`.

## Source Access

- Source metadata: [`../sources/LFKN92/metadata.yml`](../sources/LFKN92/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
