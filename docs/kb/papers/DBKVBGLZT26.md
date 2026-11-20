---
kind: paper
bibkey: DBKVBGLZT26
title: "Akita: A High-Performance Lattice-Based Polynomial Commitment Scheme"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/1983
source_metadata: ../sources/DBKVBGLZT26/metadata.yml
status: seeded
related_modules:
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Heterogeneous.lean
---

# DBKVBGLZT26

## At A Glance

`DBKVBGLZT26` is Akita, a recursive lattice-based polynomial commitment scheme and the successor of
Hachi ([`NOZ26`](NOZ26.md)). It adds a recursion and a cheaper knowledge-extraction argument
(checkpoint extraction) to the non-recursive Hachi that ArkLib already formalizes. The formalization
is tracked in [#1378](https://github.com/Verified-zkEVM/ArkLib/issues/1378); the generic extraction
layer is milestone M0 ([#1472](https://github.com/Verified-zkEVM/ArkLib/issues/1472)).

## What ArkLib Uses From This Paper

- **Corollary 10.11 (heterogeneous-coordinate CWSS accounting).** A round samples a tuple over
  sets `X_{i,u}` and needs `k_{i,u}` distinct values at coordinate `u`. ArkLib renders the star
  condition as `CoordinateWise.IsHeteroSpecialSoundFamily`, the per-round data as
  `HeteroCWSSStructure` with its shape `HeteroCWSSStructure.toShape` (arity
  `1 + ∑ u, (k i u - 1)`), and the two quantities of the corollary as
  `HeteroCWSSStructure.treeSize` and `HeteroCWSSStructure.errorBound`.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Heterogeneous.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Heterogeneous.lean)
  is the heterogeneous variant of the coordinate-wise structure of [`FMN24`](FMN24.md). The
  homogeneous structure embeds as `CWSSStructure.toHetero` with the same shape.
- Tests: `ArkLibTest/OracleReduction/CoordinateWiseHeterogeneous.lean`.

## Version Notes

- Definition and theorem numbers refer to the 178-page PDF of ePrint 2026/1983 retrieved on
  2026-11-05. Issue #1378 cites the revision of 2026-10-11, in which checkpoint structure and
  checkpoint extraction are numbered Definition 10.15 and Theorem 10.16; in the retrieved PDF they
  are Definition 10.16 and Theorem 10.17, and Definition 10.15 is the extraction experiment.

## Known Divergences From ArkLib

- The heterogeneous structure is a sibling of `CWSSStructure`, not a generalization of it, because
  `CWSSStructure` is used in about thirty modules. The homogeneous structure is the special case
  (`CWSSStructure.toHetero_toShape`).
- A parameter `k i u` of `0` or `1` asks for no sibling at that coordinate. The paper requires
  `k ≥ 2`.

## Open Formalization Gaps

- The knowledge error and expected tree size of Corollary 10.11 as statements about an extractor.
  `errorBound` and `treeSize` are the quantities only; bounding a knowledge error by them needs
  the rewinding engine of [#1410](https://github.com/Verified-zkEVM/ArkLib/issues/1410).
- Nested interpolation trees with unequal arities per level (Definition 10.12, Lemma 10.13), mixed
  trees (Lemma 10.14), and checkpoint extraction (Definitions 10.15 and 10.16, Theorem 10.17).
  Everything after Corollary 10.11 is open.

## Source Access

- Source metadata: [`../sources/DBKVBGLZT26/metadata.yml`](../sources/DBKVBGLZT26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
