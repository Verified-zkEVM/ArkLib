# Reed-Solomon Proximity

This page is the KB landing page for Reed-Solomon proximity, correlated agreement, and nearby
coding-theory machinery as formalized in ArkLib.

## Core References

- [`../papers/BCIKS20.md`](../papers/BCIKS20.md) - proximity gaps and correlated agreement.
- [`../papers/ACFY24.md`](../papers/ACFY24.md) - WHIR context built on Reed-Solomon proximity.
- [`../papers/ACFY24stir.md`](../papers/ACFY24stir.md) - STIR protocol context built on the same
  surrounding coding-theory ecosystem.
- [`../papers/DG25.md`](../papers/DG25.md) - proximity gaps in interleaved codes.
- [`../papers/BCGM25.md`](../papers/BCGM25.md) - polynomial-generator MCA and Reed-Solomon
  refinements.
- [`../papers/Jo26.md`](../papers/Jo26.md) - interleaving stability for generator MCA and curve
  decodability.

## Main ArkLib Touchpoints

- [`../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/DG25`](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean)
- [`../../../ArkLib/Data/CodingTheory/ReedSolomon.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)
- [`../../../ArkLib/ProofSystem/Whir`](../../../ArkLib/ProofSystem/Whir)
- [`../../../ArkLib/ProofSystem/Stir/ProximityGap.lean`](../../../ArkLib/ProofSystem/Stir/ProximityGap.lean)

## Notes

- This is the right starting point for many paper-driven PRs in coding theory and WHIR/STIR.
- Deep theorem-by-theorem comparisons should live in audit pages rather than in this overview.
- `Jo26` should be treated as follow-up infrastructure for existing MCA/interleaving formalization
  rather than as a top-level protocol reference.
