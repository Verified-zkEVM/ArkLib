---
kind: paper
bibkey: KZG10TR
title: "Polynomial Commitments"
year: 2010
bib_source: blueprint/src/references.bib
canonical_url: https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf
source_metadata: ../sources/KZG10TR/metadata.yml
status: seeded
related_modules:
  - ArkLib/Commitments/Functional/KZG/EvaluationBinding.lean
---

# KZG10TR

## At A Glance

`KZG10TR` is the extended technical report version of the KZG paper. ArkLib cites it for the
evaluation-binding reduction because this version includes the security proofs.

## What ArkLib Uses From This Paper

- The evaluation-binding security argument for KZG polynomial commitments.
- The reduction from a successful two-opening adversary to the `t`-SDH assumption.

## Main ArkLib Touchpoints

- [`ArkLib/Commitments/Functional/KZG/EvaluationBinding.lean`](../../../ArkLib/Commitments/Functional/KZG/EvaluationBinding.lean)
  cites `KZG10TR` directly.

## Version Notes

- This page tracks CACR technical report 2010-10.
- The ASIACRYPT 2010 proceedings version is tracked separately as `KZG10`.

## Open Formalization Gaps

- The current page is a lightweight landing page. A fuller audit should map the proof lemmas in
  `EvaluationBinding.lean` to the extended-version proof structure.
- ArkLib proves the pointwise statement `KZG.evalBindingReduction_wins` and the game-level bound
  `KZG.evalBinding_le_tsdh` against VCVio's `TSDH.experiment`. The corollary
  `KZG.evalBinding_le_of_tsdh` assumes the t-SDH bound only over an explicit adversary class.

## Source Access

- Source metadata: [`../sources/KZG10TR/metadata.yml`](../sources/KZG10TR/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
