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
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean
---

# FMN24

## At A Glance

`FMN24` is a lattice-based polynomial commitment scheme aiming at asymptotic and concrete
efficiency (Journal of Cryptology, 2024). For ArkLib its relevance is foundational: it **introduces
coordinate-wise special soundness** as the security notion underlying its extractor, and supplies
the combinatorial structure `SS(S, ℓ, k)` that ArkLib formalizes.

## What ArkLib Uses From This Paper

- **Section 2.9; Definitions 2.29--2.30.** The family `SS(S, ℓ, k)` precedes Definition 2.29's
  Sigma-protocol CWSS notion; Definition 2.30 gives the multi-round tree form. ArkLib renders the
  family as `CoordinateWise.IsSpecialSoundFamily` and the multi-round property as
  `Verifier.coordinateWiseSpecialSound`. The paper requires polynomial-time tree extraction;
  ArkLib's predicate imposes no cost bound.
- **Lemma 2.31.** The paper also derives a knowledge extractor with an expected prover-execution
  bound under an explicit growth hypothesis. ArkLib has no tree-acquisition/knowledge bridge
  implementing this result; processing a supplied tree alone would not prove it.

## Main ArkLib Touchpoints

-
  [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean)
  cites `FMN24` as the originating reference for coordinate-wise special soundness.

## Version Notes

- Journal of Cryptology 37(3):31, 2024 ([DOI](https://doi.org/10.1007/s00145-024-09511-8));
  [ePrint 2023/846](https://eprint.iacr.org/2023/846). Definition numbers here refer to the
  checked ePrint: Definitions 2.29--2.30 and Lemma 2.31. The journal citation is publication
  metadata; the journal-version PDF was not checked in this audit. Section 2.9 is not a definition
  number.
- A future knowledge bridge must bound the actual leaf/prover-run count `(ℓ(k−1)+1)^μ`.
  The printed growth condition uses `(ℓ(k−1))^μ`; that expression alone does not bound the
  former when `ℓ(k−1)=1`. Check all hypotheses and prove the actual polynomial bound, rather
  than inferring it from that isolated condition.
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
