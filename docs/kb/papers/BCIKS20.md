---
kind: paper
bibkey: BCIKS20
title: "Proximity Gaps for Reed-Solomon Codes"
year: 2020
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2020/654
source_metadata: ../sources/BCIKS20/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ProximityGap/Basic.lean
  - ArkLib/Data/CodingTheory/ProximityGap/BCIKS20
  - ArkLib/Data/Polynomial/RationalFunctions.lean
  - ArkLib/Data/CodingTheory/GuruswamiSudan
---

# BCIKS20

## At A Glance

`BCIKS20` is the core reference for ArkLib's current Reed-Solomon proximity-gap development.
It is the central paper behind the `Data/CodingTheory/ProximityGap` subtree and also appears in
supporting formalizations around list decoding, Guruswami-Sudan ingredients, and rational-function
machinery.

## What ArkLib Uses From This Paper

- The main proximity-gap and correlated-agreement statements formalized under
  [`ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
  and the `BCIKS20/` subtree.
- Supporting list-decoding ingredients formalized under
  [`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding).
- Appendix-style rational-function infrastructure in
  [`ArkLib/Data/Polynomial/RationalFunctions.lean`](../../../ArkLib/Data/Polynomial/RationalFunctions.lean).

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
  defines the reusable proximity-gap and correlated-agreement interfaces.
- [`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ReedSolomonGap.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ReedSolomonGap.lean)
  contains the Reed-Solomon gap theorem layer.
- [`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean)
  and
  [`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces.lean)
  hold the main correlated-agreement directions.
- [`ArkLib/ProofSystem/Stir/ProximityGap.lean`](../../../ArkLib/ProofSystem/Stir/ProximityGap.lean)
  reuses this line of theory in protocol-level work.
- [`ArkLib/ProofSystem/BatchedFri/Security.lean`](../../../ArkLib/ProofSystem/BatchedFri/Security.lean)
  cites specific claims from the paper in a proof-system security context.

## Known Divergences From ArkLib

- ArkLib often packages the mathematics through reusable coding-theory abstractions rather than the
  exact paper statement shape.
- Some paper concepts are represented indirectly through general interfaces instead of a dedicated
  symbol matching the paper's notation.
- Some development branches tied to this paper still contain proof gaps or incomplete branches; see
  dedicated audit pages for exact status.

## Open Formalization Gaps

- Keep a persistent theorem/status matrix in an audit page rather than overloading this landing
  page.
- Record when paper-level statements are only represented through more abstract ArkLib interfaces.
- Revisit once the existing paper audit is migrated or mirrored under `docs/kb/audits/`.

## Source Access

- Source metadata: [`../sources/BCIKS20/metadata.yml`](../sources/BCIKS20/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
