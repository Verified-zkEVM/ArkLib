---
kind: paper
bibkey: ACFY24
title: "WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification"
year: 2024
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2024/1586
source_metadata: ../sources/ACFY24/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ReedSolomon.lean
  - ArkLib/Data/CodingTheory/ListDecodability.lean
  - ArkLib/Data/CodingTheory/ProximityGap/Folding.lean
  - ArkLib/Data/CodingTheory/ProximityGap/Errors.lean
---

# ACFY24

## At A Glance

`ACFY24` is the ePrint reference for WHIR. What the paper drives in ArkLib sits entirely in the
coding-theory layer — Reed-Solomon definitions, list-decodability notions, and the
folding/proximity-gap development; there is no WHIR protocol folder under `ArkLib/ProofSystem/`.

## What ArkLib Uses From This Paper

- WHIR-specific Reed-Solomon definitions in
  [`ArkLib/Data/CodingTheory/ReedSolomon.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean).
- The list-decoding notion `Λ (C, y, r)` in
  [`ListDecodability.lean`](../../../ArkLib/Data/CodingTheory/ListDecodability.lean).
- Folding and mutual-correlated-agreement material under
  [`ArkLib/Data/CodingTheory/ProximityGap/`](../../../ArkLib/Data/CodingTheory/ProximityGap/).
- The ePrint lineage for the published version's unique-decoding MCA consequence. The Lean
  declaration uses the `ACFY25` key and is described on that paper's KB page.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ReedSolomon.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)
  cites the paper directly for WHIR-specific definitions.
- [`ProximityGap/Folding.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Folding.lean)
  carries the folding lemmas the WHIR analysis needs.

## Version Notes

- `ACFY24` is the ePrint version currently cited in ArkLib.
- `ACFY25` and `WHIR` also exist in `references.bib` for published variants of the same paper
  lineage.
- Keep version distinctions explicit when a PR depends on theorem numbering or publication status.

## Known Divergences From ArkLib

- ArkLib frequently lifts paper notions into more reusable abstractions than the paper's original
  presentation.
- ArkLib carries the WHIR-related interfaces as general coding-theory abstractions under
  `ArkLib/Data/CodingTheory/`, not as a dedicated protocol layer.

## Open Formalization Gaps

- Clarify when the repo should cite `ACFY24`, `ACFY25`, or `WHIR` for new files.
- Record paper-version choices in audit pages if a PR depends on exact numbering or wording.

## Source Access

- Source metadata: [`../sources/ACFY24/metadata.yml`](../sources/ACFY24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
