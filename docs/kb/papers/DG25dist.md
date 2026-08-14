---
kind: paper
bibkey: DG25dist
title: "On the distribution of the distances of random words"
year: "2025"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/DG25dist/metadata.yml
status: stub
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# DG25dist

## At A Glance

`DG25dist` is Diamond–Gruen, *On the distribution of the distances of random words*, Cryptology ePrint
2025/2010 — a refinement of the Hamming-ball volume estimate.

## What ArkLib Uses From This Paper

Nothing yet. [ABF26] cites it in a footnote to Corollary 3.8 for "further analysis bounding this
value", i.e. refinements of the [MS77] estimate used by the proved theorem
`linear_lambda_ge_entropy_volume`.

## Main ArkLib Touchpoints

Mentioned in the reference list of [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean).

## Known Divergences From ArkLib

**Key collision, deliberately resolved.** ArkLib's pre-existing `DG25` is the *same authors'* *Proximity
Gaps in Interleaved Codes*, which has its own module directory. This is a different paper, so it is keyed
`DG25dist`, following the in-repo `ACFY24stir` precedent.

## Open Formalization Gaps

The refinements themselves, which would sharpen Corollary 3.8 rather than being needed for it.

## Source Access

- Source metadata: [`../sources/DG25dist/metadata.yml`](../sources/DG25dist/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
