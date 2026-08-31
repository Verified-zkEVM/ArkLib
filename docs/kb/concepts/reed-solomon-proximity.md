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
- [`../papers/ABF26.md`](../papers/ABF26.md) - the survey that drives the code-family and
  list-decoding layer: rates, Johnson radii, subspace designs, folded/interleaved/multiplicity
  Reed-Solomon, extension codes. Per-statement coverage is tracked in
  [`../audits/open-problems-list-decoding-and-correlated-agreement.md`](../audits/open-problems-list-decoding-and-correlated-agreement.md).
- [`../papers/Joh62.md`](../papers/Joh62.md) - the Johnson bound, and which of the three
  overlapping Johnson keys to cite.
- [`../papers/GR08.md`](../papers/GR08.md), [`../papers/GK16.md`](../papers/GK16.md),
  [`../papers/GX13.md`](../papers/GX13.md), [`../papers/GG25.md`](../papers/GG25.md) - folded
  Reed-Solomon and subspace designs.

## Main ArkLib Touchpoints

- [`../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/DG25`](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean)
- [`../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean)
- [`../../../ArkLib/Data/CodingTheory/ReedSolomon.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)
  and the code families beside it:
  [`ReedSolomon/Folded.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean),
  [`Interleaved.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean),
  [`Multiplicity.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean).
- [`../../../ArkLib/Data/CodingTheory/ListDecodability.lean`](../../../ArkLib/Data/CodingTheory/ListDecodability.lean)
  and [`JohnsonBound/`](../../../ArkLib/Data/CodingTheory/JohnsonBound)
  — point lists, `Lambda`, and the Johnson list-size bounds.
- [`../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean`](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean)
  and [`../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean`](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean)
- [`../../../ArkLib/ProofSystem/Stir/ProximityGap.lean`](../../../ArkLib/ProofSystem/Stir/ProximityGap.lean)

## Notes

- This is the right starting point for many paper-driven PRs in coding theory and WHIR/STIR.
- Deep theorem-by-theorem comparisons should live in audit pages rather than in this overview.
- `Jo26` should be treated as follow-up infrastructure for existing MCA/interleaving formalization
  rather than as a top-level protocol reference.
- The naming, notation and type conventions of this subtree are in
  [`../../wiki/coding-theory-conventions.md`](../../wiki/coding-theory-conventions.md).
