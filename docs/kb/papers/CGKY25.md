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
  - ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean
---

# CGKY25

## At A Glance

`CGKY25` is the reference used by ArkLib's KZG function-binding reduction. The relevant portion is
the ARSDH-style extraction argument for functional commitments.

## What ArkLib Uses From This Paper

- The case split used by `mapFunctionBindingInstanceToArsdhInstAux`.
- The ARSDH target instance assembled by the KZG function-binding reduction.

## Main ArkLib Touchpoints

- [`ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean`](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean)
  cites `CGKY25` directly.

## Version Notes

- This page tracks the ePrint version currently recorded in `references.bib`.

## Open Formalization Gaps

- The current page is a lightweight landing page. A fuller audit should record which steps of the
  paper reduction correspond to each major lemma in `FunctionBinding/Basic.lean`.

## Source Access

- Source metadata: [`../sources/CGKY25/metadata.yml`](../sources/CGKY25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
