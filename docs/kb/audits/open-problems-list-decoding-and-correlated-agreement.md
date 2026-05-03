# Paper Audit: Open Problems in List Decoding and Correlated Agreement

This page records a paper-to-ArkLib audit for *Open Problems in List Decoding and Correlated
Agreement* (dated April 8, 2026).

The goal is to list the paper's named formal items and check whether each one is already present in
ArkLib, missing, or present in a materially different form.

## Status Legend

- `present`: there is a close match in ArkLib.
- `present-but-different`: the underlying concept exists, but the interface, statement shape, or
  abstraction level differs materially from the paper.
- `present-but-incomplete`: the relevant theorem/symbol exists, but the cited file still contains
  `sorry`.
- `missing`: no close formalization was found.

## Notes

- Rows follow the theorem-like items extracted from the PDF, plus named facts and remarks when they
  materially affect the comparison.
- Lean references are given as symbol names plus direct file links.
- In several places ArkLib has a more general or more reusable abstraction than the paper.
  Those are marked `present-but-different` rather than `missing`.

## Section 2: Preliminaries

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Lemma 2.1 Polynomial identity lemma | present-but-different | `prob_schwartz_zippel_mv_polynomial` in [ArkLib/Data/Probability/Instances.lean](../../../ArkLib/Data/Probability/Instances.lean); `schwartz_zippel_of_fintype` in [ArkLib/Data/MvPolynomial/Interpolation.lean](../../../ArkLib/Data/MvPolynomial/Interpolation.lean) | ArkLib has Schwartz-Zippel style lemmas, but not the exact paper statement over `F<d [X₁,...,Xₘ]` with bound `m(d-1)/|F|`. |
| Definition 2.2 q-entropy function | missing | none | No `H_q` or entropy helper matching the paper was found. |
| Definition 2.3 restricted Hamming distance | present-but-different | `Δ₀`, `δᵣ`, `distFromCode`, `relDistFromCode` in [ArkLib/Data/CodingTheory/Basic/Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean) | ArkLib has ordinary and relative Hamming distance, but not the paper's explicit restricted distance `Δ_T`. |
| Definition 2.4 Hamming-ball volume | present-but-different | `hammingBall`, `relHammingBall` in [ArkLib/Data/CodingTheory/ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | Hamming balls are present, but the explicit cardinality function `Vol_q(δ,n)` is not. |
| Definition 2.5 error-correcting code, minimum distance, rate | present-but-different | `Code.dist` in [ArkLib/Data/CodingTheory/Basic/Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean); `LinearCode.rate` in [ArkLib/Data/CodingTheory/Basic/LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | ArkLib models codes as sets or submodules over function spaces rather than the paper's subset notation `C ⊆ Σ^n`. |
| Lemma 2.6 Singleton bound | present | `singleton_bound`, `singleton_bound_linear` in [ArkLib/Data/CodingTheory/Basic/LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | Present for arbitrary and linear codes. |
| Definition 2.7 `F`-additive code | present-but-different | `ModuleCode`, `LinearCode` in [ArkLib/Data/CodingTheory/Basic/LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | Same mathematical idea, but expressed through submodules rather than a named `F`-additive predicate. |
| Definition 2.8 list around a word and global list size | present-but-different | `closeCodewordsRel`, `listDecodable`, `uniqueDecodable` in [ArkLib/Data/CodingTheory/ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | ArkLib has the underlying set and predicate notions, but not the paper's maximized function `|Λ(C,δ)|`. |
| Definition 2.9 interleaved code | present-but-different | `interleavedCodeSet`, `codewordStackSet` in [ArkLib/Data/CodingTheory/InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | Present, with a matrix-based API rather than the paper's tuple notation `C^{≡m}`. |
| Lemma 2.10 interleaved-code list-size bound | missing | none | No direct formalization of the GGR11 bound was found. |
| Definition 2.11 Reed-Solomon code | present-but-different | `ReedSolomon.code` in [ArkLib/Data/CodingTheory/ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | Present, but parameterized by an injective domain `ι ↪ F` rather than a literal subset `L ⊆ F`. |
| Definition 2.12 smooth domain | present-but-different | `ReedSolomon.Smooth` in [ArkLib/Data/CodingTheory/ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | Present as a typeclass on the domain embedding. |
| Definition 2.13 interleaved Reed-Solomon code | present-but-different | `ReedSolomon.code` with `interleavedCodeSet` in [ArkLib/Data/CodingTheory/ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) and [ArkLib/Data/CodingTheory/InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | The construction exists compositionally, but there is no dedicated `IRS[...]` alias or API. |
| Definition 2.14 admissible element for folded Reed-Solomon | missing | none | No matching folded Reed-Solomon infrastructure was found. |
| Definition 2.15 folded Reed-Solomon code | missing | none | No dedicated folded Reed-Solomon code formalization was found. |
| Definition 2.16 subspace-design code | missing | none | No `τ`-subspace-design definition was found. |
| Lemma 2.17 lower bound on `τ` | missing | none | Depends on missing subspace-design infrastructure. |
| Theorem 2.18 FRS/UM are subspace-design codes | missing | none | Folded RS and multiplicity codes are not yet formalized in this sense. |
| Definition 2.19 extension field presentation | missing | none | No matching record for `(B,F,e,ψ,φ)` was found. |
| Definition 2.20 extension code | missing | none | No extension-code construction was found. |
| Lemma 2.21 list size of extension code equals list size of interleaved base code | missing | none | Depends on missing extension-code infrastructure. |

## Section 3: List Decoding

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Definition 3.1 Johnson functions `J_{q,\ell}`, `J_q`, `J` | present-but-different | `J` in [ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) | ArkLib has the usual `q`-ary Johnson function, but not the paper's full three-function family. |
| Theorem 3.2 Johnson bound | present-but-different | `johnson_bound`, `johnson_bound_alphabet_free` in [ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) | Present as a condition-based list-size theorem rather than the exact paper packaging. |
| Corollary 3.3 MDS coarse Johnson corollary | missing | related ingredients in [ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) and [ArkLib/Data/CodingTheory/Basic/LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | Likely derivable, but not present as a named result. |
| Theorem 3.4 list decoding for subspace-design codes | missing | none | Depends on missing subspace-design infrastructure. |
| Corollary 3.5 folded RS up to capacity | missing | none | Depends on missing folded RS and subspace-design code infrastructure. |
| Theorem 3.6 random Reed-Solomon domains near capacity | missing | none | No random-domain RS list-decoding result was found. |
| Lemma 3.7 Elias lower bound | missing | none | No formalization of this lower bound was found. |
| Corollary 3.8 volume-based lower bound | missing | none | Depends on missing Elias/Hamming-volume formalization. |
| Theorem 3.9 generalized Singleton bound for list decoding | missing | related classical Singleton bounds in [ArkLib/Data/CodingTheory/Basic/LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | ArkLib has only the classical Singleton bound. |
| Theorem 3.10 large-alphabet lower bound near generalized Singleton | missing | none | No matching result was found. |
| Theorem 3.11 random linear-code lower bound | missing | none | No matching result was found. |
| Theorem 3.12 RS superpolynomial list size over extension fields | missing | none | No matching result was found. |
| Theorem 3.13 RS large list size over prime fields | missing | none | No matching result was found. |
| Theorem 3.14 large-rate RS lower bound | missing | none | No matching result was found. |
| Theorem 3.15 hardness barrier for algorithmic list decoding | missing | none | No discrete-log-based lower bound was found. |

## Section 4: Correlated Agreement Conjectures

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Definition 4.1 correlated agreement error `εca(C,δ_fld,δ_int)` | present-but-different | `δ_ε_correlatedAgreementAffineLines`, `δ_ε_correlatedAgreementCurves`, `δ_ε_correlatedAgreementAffineSpaces` in [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean) | ArkLib uses predicate-style CA notions, not the paper's maximized error-function interface. |
| Remark 4.2 discretization of proximity loss | missing | related distance granularity in [ArkLib/Data/CodingTheory/Basic/Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean) | The exact `εca`-specific remark is absent because `εca` is absent. |
| Definition 4.3 mutual correlated agreement error `εmca(C,δ)` | missing | related WHIR-specific `hasMutualCorrAgreement` in [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | ArkLib does not currently expose the paper's general code-level MCA error function. |
| Remark 4.4 MCA with proximity loss | missing | none | No matching notion was found. |
| Fact 4.5 `εpg ≤ εca ≤ εmca` | missing | related CA/proximity-gap predicates in [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean) | Not expressible in current ArkLib interfaces because `εca` and `εmca` are not defined as numeric errors. |
| Lemma 4.6 MCA equals CA below unique decoding radius | missing | none | No general theorem of this form was found. |
| Lemma 4.7 interleaving degrades MCA by at most `t` | missing | none | No general interleaving-vs-MCA theorem was found. |
| Theorem 4.8 AHIV17 general-code unique-decoding bound | missing | related but different [ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean) | AHIV22 is present, but not this general `εmca/εca` statement. |
| Theorem 4.9 RS unique-decoding results | present-but-different | `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` and `RS_correlatedAgreement_affineLines` in [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean) and [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean) | Item 1 is represented via predicate-style CA for RS. Item 2, the BCHKS25 proximity-loss refinement, is missing. The main file still has a `sorry` in the non-unique-decoding branch. |
| Remark 4.10 small proximity-loss simplification | missing | none | Depends on missing `εca` error-function interface. |
| Theorem 4.11 1.5-Johnson regime for general linear codes | missing | none | No matching theorem was found. |
| Theorem 4.12 Johnson-range RS MCA bound | missing | related conjectural WHIR-facing statements in [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | ArkLib does not yet contain the BCHKS25 theorem itself. |
| Theorem 4.13 MCA from subspace-design codes | missing | none | Depends on missing subspace-design code infrastructure. |
| Theorem 4.14 folded RS MCA up to capacity | missing | none | Depends on missing folded RS and subspace-design infrastructure. |
| Theorem 4.15 random RS MCA up to capacity | missing | none | No random-domain RS MCA result was found. |
| Theorem 4.16 lower bound on CA near capacity | missing | none | No matching result was found. |
| Theorem 4.17 complete CA breakdown theorem | missing | none | No matching result was found. |
| Theorem 4.18 CA jump at the Johnson bound | missing | none | No matching result was found. |
| Lemma 4.19 CA bounded below by sampling probability | missing | none | No matching result was found. |
| Definition 4.20 line-decoding | missing | none | No general line-decoding definition was found. |
| Theorem 4.21 line-decoding implies MCA | missing | none | Depends on missing line-decoding infrastructure. |

## Section 5: Connections Between List Decoding and Correlated Agreement

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Theorem 5.1 list decoding implies MCA | missing | only related WHIR-specific `mca_list_decoding` in [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | ArkLib does not contain the general GCXK25 theorem; the WHIR lemma is at a different abstraction layer and is still incomplete. |
| Theorem 5.2 small CA error implies list size `< |F|` | missing | none | No matching result was found. |
| Theorem 5.3 CA implies list decoding for a related RS code | missing | none | No matching result was found. |
| Theorem 5.4 separation between list decoding and CA | missing | none | No matching result was found. |

## Section 6: Toy Problem

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Definition 6.1 toy problem relation `R_C^ℓ` | missing | none | No matching relation was found. |
| Definition 6.3 relaxed toy relation `R̃_C,δ^ℓ` | missing | none | No matching relation was found. |
| Definition 6.4 erasure correction | missing | none | There is no code-level erasure-correction abstraction matching the paper. |
| Lemma 6.5 every additive code supports erasure correction | missing | none | No matching theorem was found. |
| Lemma 6.6 knowledge soundness of Construction 6.2 | missing | related general security framework in [ArkLib/OracleReduction/Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | The framework exists, but this protocol and its theorem are not formalized. |
| Remark 6.7 CA is insufficient for the proof of Lemma 6.6 | missing | none | No matching analysis was found. |
| Lemma 6.8 round-by-round knowledge soundness of Construction 6.2 | missing | related framework in [ArkLib/OracleReduction/Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | The framework exists, but this protocol and its theorem are not formalized. |
| Lemma 6.10 soundness of Construction 6.9 | missing | none | No matching protocol or theorem was found. |
| Definition 6.11 winning set `Ω` | missing | none | No matching definition was found. |
| Lemma 6.12 list-decoding lower-bound attack | missing | none | No matching theorem was found. |
| Lemma 6.13 CA lower-bound attack | missing | none | No matching theorem was found. |
| Remark 6.14 attack currently only reaches `εca`, not `εmca` | missing | none | No matching analysis was found. |

## Appendix A: Additional Preliminaries

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Definition A.1 completeness for IORs | present-but-different | `Reduction.completeness`, `Reduction.perfectCompleteness` in [ArkLib/OracleReduction/Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | Present in ArkLib's more general oracle-reduction framework rather than the paper's `(x,y,w)` relation presentation. |
| Remark A.2 IOP as IOR to trivial relation | present-but-different | same framework in [ArkLib/OracleReduction/Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | Conceptually supported by the framework, but not isolated as this exact remark. |
| Definition A.3 knowledge soundness for IORs | present-but-different | `Verifier.knowledgeSoundness` in [ArkLib/OracleReduction/Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | Present with a richer execution/log model. |
| Definition A.5 round-by-round knowledge soundness | present-but-different | `Verifier.rbrKnowledgeSoundnessOneShot`, `Verifier.rbrKnowledgeSoundness` in [ArkLib/OracleReduction/Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | Present in a more abstract transcript/state-function framework. |
| Definition A.6 formal derivative | present-but-different | uses Mathlib polynomial derivative machinery; see [ArkLib/Data/CodingTheory/ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) for nearby polynomial infrastructure | ArkLib relies on the underlying polynomial derivative API rather than introducing the paper's local definition. |
| Definition A.7 univariate multiplicity code | missing | none | No multiplicity-code formalization was found. |

## Appendix B

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Claim B.1 collision bound for random functions | missing | none | No matching standalone combinatorial claim was found. |

## Existing Inconsistencies

The largest mismatches between the paper and ArkLib are structural rather than mathematical.

1. Correlated agreement is formalized as predicates, not error functions.
   ArkLib currently exposes `δ_ε_correlatedAgreement...` predicates in
   [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean),
   while the paper is organized around numeric error functions `εpg`, `εca`, and `εmca`.

2. General MCA is not yet a first-class coding-theory notion in ArkLib.
   The TODO at the top of
   [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
   still lists mutual correlated agreement as missing. The existing
   [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean)
   file is WHIR/proximity-generator specific and is not a drop-in formalization of Section 4.

3. Some core BCIKS20 interfaces are present, but the list-decoding regime branch is incomplete.
   In particular,
   [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean)
   still leaves the non-unique-decoding branch as `sorry`.

4. Several "present" proximity-gap and MCA files are still proof-incomplete.
   This is true in
   [ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean),
   multiple files under
   [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20),
   and
   [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean).

5. Several code families used centrally by the paper are absent.
   Folded Reed-Solomon, univariate multiplicity codes, subspace-design codes, and extension-field
   codes are not yet represented directly in ArkLib.

## Roadmap

### Phase 1: Align the Core Interfaces

1. Add numeric error-function wrappers for proximity gap, CA, and MCA in
   `ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`.
   These should coexist with the current predicate-style APIs rather than replace them.

2. Add a general code-level MCA definition there as well.
   The WHIR-specific notion in
   [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean)
   should then be re-expressed as a specialization of the general MCA layer.

3. Add a general line-decoding definition next to CA/MCA.
   Section 4 and Section 5 are much cleaner to formalize once this interface exists.

4. Add a maximized list-size function `listSize` or `Lambda` on top of the current
   `closeCodewordsRel` and `listDecodable` interfaces in
   [ArkLib/Data/CodingTheory/ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean).

### Phase 2: Close Existing Gaps in the Current Theory

1. Finish the non-unique-decoding branch of
   `RS_correlatedAgreement_affineLines` in
   [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean).

2. Remove `sorry` from the already-declared proximity-gap files:
   [ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean),
   [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ReedSolomonGap.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ReedSolomonGap.lean),
   [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean),
   [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces.lean),
   and the BCIKS20 list-decoding support files.

3. Finish the declared Guruswami-Sudan decoder results in
   [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean),
   since later list-decoding and CA/MCA comparisons depend on them.

4. Finish the remaining `sorry` in the security framework files
   [ArkLib/OracleReduction/Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean)
   and
   [ArkLib/OracleReduction/Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean),
   because Section 6 depends heavily on these abstractions.

### Phase 3: Add the Missing Code Families

1. Add a dedicated interleaved Reed-Solomon alias/API in
   [ArkLib/Data/CodingTheory/ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)
   or a sibling file, built on top of the existing interleaving machinery.

2. Add folded Reed-Solomon codes, including admissibility conditions.

3. Add univariate multiplicity codes and their formal-derivative packaging.

4. Add extension-field presentations and extension codes.

5. Add subspace-design codes as a reusable abstraction layer.

### Phase 4: Rebuild Section 3 and Section 4 on the New Interfaces

1. Formalize the missing list-size bounds that are prerequisites for the paper's later sections:
   Elias lower bounds, generalized Singleton, interleaved-code list-size comparison, and the
   missing Johnson corollaries.

2. Add the general CA/MCA theorems in the unique-decoding regime first.
   This includes the paper's Fact 4.5, Lemma 4.6, Lemma 4.7, and the AHIV17/BCHKS25 style results.

3. Add line-decoding and its implication to MCA before attempting the most recent capacity-level
   theorems.

4. Only after the above is stable, add the 2025-2026 results for subspace-design codes,
   folded RS, and random-domain RS.

### Phase 5: Formalize Section 5 Connections

1. Add the general theorem "list decoding implies MCA" at the code-theory layer.

2. Add the converse-obstruction theorems that bound CA using list size or sampling probability.

3. Keep these results in coding-theory modules rather than protocol-specific files, so they can be
   reused by WHIR, STIR, and later proof-system developments.

### Phase 6: Formalize Section 6 as a Worked Oracle-Reduction Case Study

1. Add the toy relation and relaxed toy relation as a small standalone module, likely under
   `ArkLib/ProofSystem/` rather than under `OracleReduction/`.

2. Add an erasure-correction abstraction at the coding-theory layer, with the generic additive-code
   existence theorem.

3. Formalize Construction 6.2 and Construction 6.9 as oracle reductions using the existing
   security framework.

4. Then prove the Section 6 knowledge-soundness, round-by-round soundness, and lower-bound attack
   lemmas against those concrete reductions.

### Recommended Order

1. Phase 1
2. Phase 2
3. Phase 3
4. Unique-decoding parts of Phase 4
5. Phase 6
6. Remaining parts of Phase 4 and Phase 5

That order minimizes rework: it first stabilizes the interfaces, then completes already-started
theory, then adds the code families the later theorems depend on.
