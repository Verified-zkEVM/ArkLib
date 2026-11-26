---
kind: paper
bibkey: CGKY25
title: "On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments"
year: 2025
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/902
source_metadata: ../sources/CGKY25/metadata.yml
status: seeded
related_modules:
  - ArkLib/Commitments/Functional/KZG/FunctionBinding/Reduction.lean
---

# CGKY25

## At A Glance

`CGKY25` is the reference used by ArkLib's KZG function-binding reduction. The relevant portion is
the ARSDH-style extraction argument for functional commitments.

## What ArkLib Uses From This Paper

- Function binding (Definition 3.17), which `KZG.functionBindingExperiment` states for KZG: every
  opening is accepted and no message fits all of them.
- The ARSDH assumption (Definition 9.6), which VCVio states as `ARSDH.experiment`.
- The reduction from KZG function binding to ARSDH. ArkLib's version,
  `KZG.FunctionBinding.functionBindingReduction`, treats three cases: two conflicting openings,
  the trapdoor among the queries, and interpolation through `n + 1` distinct openings.

## Main ArkLib Touchpoints

- [`ArkLib/Commitments/Functional/KZG/FunctionBinding/Reduction.lean`](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Reduction.lean)
  cites `CGKY25` directly.

## Version Notes

- This page tracks the ePrint version currently recorded in `references.bib`.

## Open Formalization Gaps

- The current page is a lightweight landing page. A fuller audit should record which steps of the
  paper reduction correspond to each major lemma in `FunctionBinding/Wins.lean`.
- ArkLib proves the pointwise statement `KZG.FunctionBinding.functionBindingReduction_wins` and the
  game-level bound `KZG.functionBinding_le_arsdh` against VCVio's `ARSDH.experiment`. The
  corollary `KZG.functionBinding_le_of_arsdh` assumes the ARSDH bound only over an explicit
  adversary class.

## Source Access

- Source metadata: [`../sources/CGKY25/metadata.yml`](../sources/CGKY25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
