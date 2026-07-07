---
kind: paper
bibkey: BCGM25
title: "All Polynomial Generators Preserve Distance with Mutual Correlated Agreement"
year: 2025
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/2051
source_metadata: ../sources/BCGM25/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean
  - ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean
---

# BCGM25

## At A Glance

`BCGM25` is the ePrint reference for ArkLib's current general proximity-generator and
MCA-generator definitions.
It proves that polynomial generators satisfy mutual correlated agreement for every linear code,
with Reed-Solomon refinements up to the Johnson bound.

## What ArkLib Uses From This Paper

- Generator definitions and zero-evading/MDS/polynomial-generator interfaces in
  [`ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean).
- MCA generator definitions and linear-transformation closure statements in
  [`ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean).
- The broader formalization target that polynomial-generator MCA bounds should become reusable
  coding-theory infrastructure rather than WHIR-only assumptions.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean)
- [`ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean)
- [`ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean`](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean)

## Version Notes

- `BCGM25` is currently tracked as ePrint 2025/2051.
- Keep theorem numbering tied to the ePrint version unless a later published version is added
  under a separate key.

## Known Divergences From ArkLib

- ArkLib currently splits proximity-generator infrastructure between a general coding-theory layer
  and WHIR-specific protocol files.
- Some paper statements are represented as reusable definitions before the corresponding complete
  theorem stack is present.

## Open Formalization Gaps

- Complete the main polynomial-generator MCA theorem stack.
- Reconcile general MCA-generator APIs with the WHIR-specific `hasMutualCorrAgreement` interface.
- Track interleaving stability results from `Jo26` as follow-up infrastructure for using BCGM25
  bounds on interleaved codes.

## Source Access

- Source metadata: [`../sources/BCGM25/metadata.yml`](../sources/BCGM25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
