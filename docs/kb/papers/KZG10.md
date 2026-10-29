---
kind: paper
bibkey: KZG10
title: "Constant-Size Commitments to Polynomials and Their Applications"
year: 2010
bib_source: blueprint/src/references.bib
canonical_url: https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf
source_metadata: ../sources/KZG10/metadata.yml
status: seeded
related_modules:
  - ArkLib/Commitments/Functional/KZG/Basic.lean
---

# KZG10

## At A Glance

`KZG10` is the ASIACRYPT paper introducing the KZG polynomial commitment scheme used by ArkLib's
core KZG definitions.

## What ArkLib Uses From This Paper

- The constant-size polynomial commitment construction.
- The commit, open, and verify operations instantiated in `Basic.lean`.

## Main ArkLib Touchpoints

- [`ArkLib/Commitments/Functional/KZG/Basic.lean`](../../../ArkLib/Commitments/Functional/KZG/Basic.lean)
  cites `KZG10` directly.

## Version Notes

- This page tracks the ASIACRYPT 2010 proceedings version currently recorded in `references.bib`.
- The extended technical report is tracked separately as `KZG10TR`.

## Open Formalization Gaps

- The current page is a lightweight landing page. A fuller audit should record which paper notation
  corresponds to each concrete definition in `Basic.lean`.

## Source Access

- Source metadata: [`../sources/KZG10/metadata.yml`](../sources/KZG10/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
