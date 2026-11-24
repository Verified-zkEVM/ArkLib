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
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Layout.lean
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/BlockStructure.lean
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/LayoutVecTree.lean
  - ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean
  - ArkLib/Data/MvPolynomial/VecTreeInterpolation.lean
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
  condition as `CoordinateWise.IsBlockSpecialSoundFamily`, one star with an alphabet and a
  threshold per coordinate as `CoordinateWise.Block`, and the two quantities of the corollary as
  `Block.arity` (`1 + ∑ u, (k u - 1)`) and `Block.error` (`∑ u, (k u - 1) / |X u|`).
- **Definition 10.12 and Lemma 10.14 (nested and mixed stages).** A round has a
  `CoordinateWise.Layout`, a sequence of blocks: a flat round is one block, a nested round is one
  coordinate per block (`Layout.nested`), and plain `k`-special soundness is one block with one
  coordinate (`Layout.single`). `Layout.IsTree` is the tree condition: the children of block `b`
  below every prefix form a star of that block. `BlockCWSSStructure` gives every challenge round a
  layout, with the tree shape `BlockCWSSStructure.toShape`, the leaf count `treeSize` and the
  error sum `knowledgeError`.
- **Lemma 10.13 (interpolation on a nested tree).** `MvPolynomial.NestedEvaluationTree` has an
  arity per level, and `Rewinding.VecTree.toNested` and `Rewinding.VecTree.eq_zero_of_vanishes`
  read the challenge tree of a VCVio rewinding finder as such a tree and give its zero test.
  `Layout.isTree_iff_vecTree` reads a tree of a layout as a structured `Rewinding.VecTree`.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Layout.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Layout.lean)
  defines blocks and layouts, with the special layouts and their arities.
- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/BlockStructure.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/BlockStructure.lean)
  defines the structure with a layout per round, and maps the homogeneous structure of
  [`FMN24`](FMN24.md) into it with the same tree shape (`CWSSStructure.toBlock_toShape`).
- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/LayoutVecTree.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/LayoutVecTree.lean)
  is the only file of the coordinate-wise special-soundness layer that imports the VCVio
  rewinding finder.
- [`ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean`](../../../ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean)
  and
  [`ArkLib/Data/MvPolynomial/VecTreeInterpolation.lean`](../../../ArkLib/Data/MvPolynomial/VecTreeInterpolation.lean)
  hold the interpolation lemma and its bridge to the finders.
- Tests: `ArkLibTest/OracleReduction/Security/CoordinateWiseSpecialSoundness/BlockStructure.lean`,
  `ArkLibTest/Data/MvPolynomial/VecTreeInterpolation.lean`.

## Version Notes

- Definition and theorem numbers refer to the revision of 22 November 2026 (179-page PDF of ePrint
  2026/1983). Definition 10.15 is the extraction experiment, Definition 10.16 the checkpoint
  structure and Theorem 10.17 checkpoint extraction. Issue #1378 cites the revision of 2026-10-11,
  in which the last two are numbered Definition 10.15 and Theorem 10.16.
- In this revision, Lemma 10.14 (ii) and Theorem 10.17 are stated for oracle keys that hold the
  statement and the prover messages only, which is what `fsChallengeOracle` does. The earlier
  hypothesis that the key encodes the earlier challenges is gone. Two facts replace it: the
  transcript prefix is reconstructed from the entries of earlier stages, and two runs on tables that
  differ at one address agree up to the first query to it.

## Known Divergences From ArkLib

- `BlockCWSSStructure` is a temporary name. It coexists with `CWSSStructure` while the consumers
  of the latter move over. Then it takes the name `CWSSStructure`, and today's structure becomes
  `HomogeneousCWSSStructure`. The star family carries the temporary name
  `IsBlockSpecialSoundFamily` for the same reason.
- A threshold `k u` of `0` or `1` asks for no sibling at that coordinate. The paper requires
  `k ≥ 2`. `Block.Admissible` states `1 ≤ k u ≤ |X u|`, the range in which a star can exist.
- `Block.error` and `BlockCWSSStructure.knowledgeError` are sums. They are the failure probability
  of the search for siblings in each coordinate fibre of a uniformly sampled center, not a
  collision probability of independent samples. They get that meaning from the block finder, which
  is not in ArkLib yet.

## Open Formalization Gaps

- The knowledge error and expected tree size of Corollary 10.11 and Lemma 10.14 (i) as statements
  about an extractor. This needs the block star step and the multi-round block finder in VCVio, and
  the legacy rewinding instance of
  [#1410](https://github.com/Verified-zkEVM/ArkLib/issues/1410).
- The bridge from `Layout.nested` to `Rewinding.VecTree.toNested`: the points of a nested layout
  are `Fin 1 → A b`, so the tree is transported along a round-wise equivalence first.
- Mixed trees with a Fiat–Shamir factor, and checkpoint extraction (Definitions 10.15 and 10.16,
  Theorem 10.17). Everything after the interpolation lemma is open; the design is tracked in
  [#1472](https://github.com/Verified-zkEVM/ArkLib/issues/1472).

## Source Access

- Source metadata: [`../sources/DBKVBGLZT26/metadata.yml`](../sources/DBKVBGLZT26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
