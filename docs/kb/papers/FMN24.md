---
kind: paper
bibkey: FMN24
title: "Lattice-Based Polynomial Commitments: Towards Asymptotic and Concrete Efficiency"
year: "2024"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2023/846
source_metadata: ../sources/FMN24/metadata.yml
status: seeded
related_modules:
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean
---

# FMN24

## At A Glance

`FMN24` is a lattice-based polynomial commitment scheme aiming at asymptotic and concrete
efficiency (Journal of Cryptology, 2024). For ArkLib its relevance is foundational: it **introduces
coordinate-wise special soundness** as the security notion underlying its extractor, and supplies
the combinatorial structure `SS(S, ℓ, k)` that ArkLib formalizes.

## What ArkLib Uses From This Paper

- **Definition 2.9 / 2.10.** The combinatorial family `SS(S, ℓ, k)` of coordinate-wise related
  challenge vectors, and the (single-/multi-round) coordinate-wise special-soundness notion. ArkLib
  renders these as `CoordinateWise.IsSpecialSoundFamily` and
  `Verifier.coordinateWiseSpecialSound`.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean)
  cites `FMN24` as the originating reference for coordinate-wise special soundness.

## Version Notes

- Journal of Cryptology 37(3):31, 2024 (DOI 10.1007/s00145-024-09511-8); ePrint 2023/846.
- Read together with [`NOZ26.md`](NOZ26.md), which states the multi-round form (Definition 3) that
  ArkLib targets for verification.

## Known Divergences From ArkLib

- ArkLib abstracts the notion away from the paper's specific lattice commitment, phrasing it over
  the generic IOR `ProtocolSpec` / `ChallengeTree` machinery.

## Open Formalization Gaps

- Protocol-specific uses of CWSS for lattice commitment schemes remain future work.

## Source Access

- Source metadata: [`../sources/FMN24/metadata.yml`](../sources/FMN24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
