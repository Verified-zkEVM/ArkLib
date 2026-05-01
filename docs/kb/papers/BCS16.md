---
kind: paper
bibkey: BCS16
title: "Interactive Oracle Proofs"
year: 2016
bib_source: blueprint/src/references.bib
source_metadata: ../sources/BCS16/metadata.yml
status: seeded
related_concepts:
  - interactive-oracle-proofs
related_modules:
  - ArkLib/OracleReduction/Basic.lean
  - ArkLib/OracleReduction/VectorIOR.lean
---

# BCS16

## At A Glance

`BCS16` is the current repository key used in the oracle-reduction layer for the original
interactive oracle proof reference.
It is foundational context for how ArkLib explains vector IOPs and related downstream
specializations.

## What ArkLib Uses From This Paper

- Historical grounding for the vector-IOP point of view mentioned in
  [`ArkLib/OracleReduction/Basic.lean`](../../../ArkLib/OracleReduction/Basic.lean).
- Terminology for IOPs and the relationship between general oracle-reduction abstractions and the
  original vector-IOP setting.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Basic.lean`](../../../ArkLib/OracleReduction/Basic.lean) cites `BCS16`
  when describing vector IOPs as the original IOP formulation.
- [`ArkLib/OracleReduction/VectorIOR.lean`](../../../ArkLib/OracleReduction/VectorIOR.lean)
  presents the corresponding specialization at the code level.

## Version Notes

- `references.bib` currently contains both `IOPs` and `BCS16`, and the titles appear related.
- Treat this page as a stable landing page for the key currently used in ArkLib source files.
- Revisit key normalization once the bibliography-cleanup policy is implemented.

## Known Divergences From ArkLib

- ArkLib's `OracleReduction` abstraction is broader than the original vector-IOP presentation.
- The repo uses this paper mainly as conceptual lineage, not as a line-by-line formalization
  target.

## Open Formalization Gaps

- Decide whether `BCS16` and `IOPs` should remain distinct keys or be documented as alternate
  versions of the same reference lineage.

## Source Access

- Source metadata: [`../sources/BCS16/metadata.yml`](../sources/BCS16/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
