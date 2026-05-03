# Reed-Solomon Proximity

This page is the KB landing page for Reed-Solomon proximity, correlated agreement, and nearby
coding-theory machinery as formalized in ArkLib.

## Core References

- [`../papers/BCIKS20.md`](../papers/BCIKS20.md) - proximity gaps and correlated agreement.
- [`../papers/ACFY24.md`](../papers/ACFY24.md) - WHIR context built on Reed-Solomon proximity.
- [`../papers/ACFY24stir.md`](../papers/ACFY24stir.md) - STIR protocol context built on the same
  surrounding coding-theory ecosystem.

## Main ArkLib Touchpoints

- [`../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20)
- [`../../../ArkLib/Data/CodingTheory/ReedSolomon.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)
- [`../../../ArkLib/ProofSystem/Whir`](../../../ArkLib/ProofSystem/Whir)
- [`../../../ArkLib/ProofSystem/Stir/ProximityGap.lean`](../../../ArkLib/ProofSystem/Stir/ProximityGap.lean)

## Notes

- This is the right starting point for many paper-driven PRs in coding theory and WHIR/STIR.
- Deep theorem-by-theorem comparisons should live in audit pages rather than in this overview.
