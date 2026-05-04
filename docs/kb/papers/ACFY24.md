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
  - ArkLib/ProofSystem/Whir
---

# ACFY24

## At A Glance

`ACFY24` is the ePrint reference for WHIR and is the main paper currently cited by ArkLib's WHIR
development.
It influences both coding-theory definitions in `ReedSolomon.lean` and protocol-level files under
`ProofSystem/Whir/`.

## What ArkLib Uses From This Paper

- WHIR-specific Reed-Solomon definitions currently introduced in
  [`ArkLib/Data/CodingTheory/ReedSolomon.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean).
- Proximity-generator and mutual correlated-agreement notions in the
  [`ArkLib/ProofSystem/Whir/`](../../../ArkLib/ProofSystem/Whir) subtree.
- Protocol-level soundness and folding interfaces for the current WHIR formalization.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ReedSolomon.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)
  cites the paper directly for WHIR-specific definitions.
- [`ArkLib/ProofSystem/Whir/ProximityGen.lean`](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean)
  introduces proximity generators from Section 4.
- [`ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean`](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean)
  and
  [`ArkLib/ProofSystem/Whir/BlockRelDistance.lean`](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean)
  formalize WHIR-specific coding-theory/protocol notions.
- [`ArkLib/ProofSystem/Whir/RBRSoundness.lean`](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean)
  ties the protocol story back into the soundness framework.

## Version Notes

- `ACFY24` is the ePrint version currently cited in ArkLib.
- `ACFY25` and `WHIR` also exist in `references.bib` for published variants of the same paper
  lineage.
- Keep version distinctions explicit when a PR depends on theorem numbering or publication status.

## Known Divergences From ArkLib

- ArkLib frequently lifts paper notions into more reusable abstractions than the paper's original
  presentation.
- Some WHIR-related interfaces currently live at the protocol layer and may later move downward
  into more general coding-theory abstractions.

## Open Formalization Gaps

- Clarify when the repo should cite `ACFY24`, `ACFY25`, or `WHIR` for new files.
- Record paper-version choices in audit pages if a PR depends on exact numbering or wording.

## Source Access

- Source metadata: [`../sources/ACFY24/metadata.yml`](../sources/ACFY24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
