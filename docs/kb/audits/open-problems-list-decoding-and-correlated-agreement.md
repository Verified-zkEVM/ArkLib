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

## Section 2 — Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `L2.1` | Polynomial identity lemma | present | `prob_polynomial_identity_le`, `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`, `MvPolynomial.totalDegree_le_of_degreeOf_lt` in [Instances.lean](../../../ArkLib/Data/Probability/Instances.lean); `schwartz_zippel_of_fintype` in [Interpolation.lean](../../../ArkLib/Data/MvPolynomial/Interpolation.lean) | `prob_polynomial_identity_le` | Paper bound `m·(d-1)/|F|` for individual-degree-`<d` polynomials, realised as `prob_polynomial_identity_le`. Derived from the generalised Schwartz-Zippel wrapper `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le` (which takes any `d ≥ totalDegree P`) via the `MvPolynomial.totalDegree_le_of_degreeOf_lt` helper. The legacy specialisation `prob_schwartz_zippel_mv_polynomial` (bound `≤ n / \|F\|` when `totalDegree ≤ n`) is preserved as a one-line wrapper. |
| `D2.2` | q-entropy function `H_q` | present | `CodingTheory.qEntropy` in [Entropy.lean](../../../ArkLib/Data/CodingTheory/Basic/Entropy.lean) | existing | `noncomputable def`; uses Mathlib's `Real.logb`. Boundary case `qEntropy q 0 = 0` is a `@[simp]` lemma. |
| `D2.3` | Restricted Hamming distance `Δ_T` | present-but-different | existing full-domain `Δ₀`/`δᵣ` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean) and [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) | `restrictedRelHammingDist` | The explicit `Δ_T` (`ℝ≥0`-valued restricted fractional distance) ships with the proximity-gap split, next to its first consumers (`ε_mca`/`ε_ca` statements); this layer keeps only the full-domain notions. |
| `D2.4` | Hamming-ball volume `Vol_q(δ,n)` | present | `CodingTheory.hammingBallVolume` in [HammingBallVolume.lean](../../../ArkLib/Data/CodingTheory/HammingBallVolume.lean); supporting `hammingBall`/`relHammingBall` sets in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | `noncomputable def` (depends on `Nat.floor` over `ℝ`). Boundary case `Vol_q(0, n) = 1` is a `@[simp]` lemma. |
| `D2.5` | ECC, `δ_min`, rate | present-but-different | `Code.dist`, `Code.minDist` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean); `LinearCode.rate` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean); bridge `minDist_div_card_eq_minRelHammingDistCode` and supporting `minRelHammingDistCode` in [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) linking the raw `Code.minDist C / n` form to `δᵣ C` (proved, via `Set.Finite.toFinset` refactor of `minRelHammingDistCode`) | existing | Paper uses `C ⊆ Σ^n`; ArkLib uses function spaces. Mathematically equivalent. Paper-style `δ_min` / `ρ` scoped-notation file was once planned but never materialised — call sites use `Code.minDist C / Fintype.card ι` and `LinearCode.rate` directly. |
| `L2.6` | Singleton bound | present | `singleton_bound`, `singleton_bound_linear`, `IsMDS` predicate (from PR #430), and `IsMDS_iff_rate_distance` bridge in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | existing | `IsMDS LC` encodes the additive Nat Singleton-tight condition `Code.dist LC.carrier = length LC - dim LC + 1`; the bridge `IsMDS_iff_rate_distance` connects it to the rate-distance form `δ_min(LC)/n = 1 - dim/n + 1/n` used by ABF26 §2-§3. |
| `D2.7` | F-additive code | present-but-different | `ModuleCode`, `LinearCode` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | use `ModuleCode ι F (Fin s → F)` directly | `ModuleCode` / `LinearCode` *bake in* F-linear subspace structure — the paper's "F-additive" notion is realised by these existing types. Theorems quantifying over a paper-style "F-additive `Set`-coded code `C`" can write `∃ MC : Submodule F (ι → A), (MC : Set _) = C` inline rather than via a dedicated paper-shape predicate; ArkLib convention avoids alias-style wrappers for items already realised by existing types. |
| `D2.8` | `Λ(C,δ,f)` and `\|Λ(C,δ)\|` | present | `ListDecodable.closeCodewordsRel` (= point list `Λ(C,δ,f)`), `ListDecodable.Lambda`, `Lambda_le_iff_listDecodable`, `closeCodewordsRel_subset_of_le`, `Lambda_mono`, `Lambda_le_ncard` in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | The point list `Λ(C,δ,f)` is the pre-existing `closeCodewordsRel C f δ` (no paper-shape alias: the `Lambda_at` abbrev was removed 2026-05-31). `Lambda` is the new `ℕ∞`-valued maximised list size `\|Λ(C,δ)\|`; `Lambda_le_iff_listDecodable` bridges it to the pre-existing ∀-form `listDecodable` consumed by the STIR development, so the two are one notion, not a fork. |
| `D2.9` | `m`-interleaved code `C^≡m` | present-but-different | `interleavedCodeSet`, `codewordStackSet` in [InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | existing + `scoped notation "_^≡_"` | Matrix-based API; paper uses tuple notation. |
| `L2.10` | `\|Λ(C^≡m,δ)\| ≤ binom(b+r,r)·\|Λ\|^r` | missing | none | `InterleavedCode.lambda_le_ggr11` | Lands with the proximity-gap split (`ListDecoding/Interleaved.lean`) as an external admit `[GGR11]`. |
| `D2.11` | Reed-Solomon code `RS[F,L,k]` | present-but-different | `ReedSolomon.code` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing + `scoped notation "RS[" F ", " L ", " k "]"` | Parameterised by injection `ι ↪ F` rather than `L ⊆ F`. Strictly more general. |
| `D2.12` | Smooth domain | present | `ReedSolomon.Smooth` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing | Verified: typeclass requires multiplicative coset of a subgroup with order a power of two. The companion directory [FftDomain/](../../../ArkLib/Data/Domain/FftDomain) (5 modules) provides FFT-domain machinery; not a paper-item match but noted here for completeness. |
| `D2.13` | s-interleaved RS `IRS[F,L,k,s]` | present | [ReedSolomon/Interleaved.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean) | `ReedSolomon.Interleaved.irsCode`, plus `dim_irsCode` (proved) | Defined as `interleavedCodeSet (RS[F, L, ⌊k/s⌋])`. Dimension formula `dim(IRS) = s · (k/s)` proved via injective F-linear `(Fin s → ↥RS) → (ι → Fin s → F)` + `finrank_pi_fintype`. |
| `D2.14` | `(L,s)`-admissible field element | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.Admissible` | Required by D2.15. |
| `D2.15` | Folded RS `FRS[F,L,k,s,ω]` | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.frsCode` | Used pervasively in §3, §4, §6.3.2. **Track B bridges (2026-06-23), all `sorry`-free + axiom-clean (`[propext, Classical.choice, Quot.sound]`):** `admissible_foldedPoints_injective` (`Admissible ∧ ω≠0 ⇒` the `s·\|ι\|` folded points pairwise distinct), `frsEvalOnPoints_domRestrict_injective` (`Admissible ∧ ω≠0 ∧ k ≤ s·\|ι\| ⇒` encoder injective — the `Admissible → injective` bridge `dim_frsCode`'s `h_encoder_inj` awaited), and `minDist_frsCode` (block-metric MDS distance `Code.minDist (frsCode …) = \|ι\| − ⌊(k-1)/s⌋`, both directions: root-counting + explicit minimal-weight product-polynomial codeword). These are the shared structural witnesses the §6 toy-problem instantiations consume (next splits). |
| `D2.16` | τ-subspace-design code | present | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.IsSubspaceDesign` | GX13 definition; uses `LinearMap.proj` for `A_i`. |
| `L2.17` | `min τ(r) ≥ ρ − 1/n` | present (**PROVEN**) | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.subspaceDesign_tau_lower` | GG25 lemma, **proved in-tree 2026-08-07** (sorry-free, axiom-clean): design inequality at the span of a distance-attaining codeword + the new module-alphabet Singleton bound `LinearCode.singleton_bound_module` (`k ≤ s(n−d+1)`). Statement corrected 2026-06-10: rate is `finrank/(s·n)` (D2.5 alphabet `F^s`), not `finrank/n` — previous form was false (C = ⊤ counterexample). **Re-review fix (2026-06-10b):** added `∀ r, 0 ≤ τ r` (negative profiles falsified the bound at `C = ⊥`; still required — it carries the degenerate `C = ⊥` branch). |
| `T2.18` | FRS and UM are subspace-design | stated (external admit; FRS half only) | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.frs_is_subspaceDesign_gk16` | GK16 theorem; tagged sorry. UM half deferred pending D2.19. Statement corrected 2026-06-10: with `ρ = k/(s·n)` the profile is `τ(r) = s·ρ/(s−r+1) = (k/n)/(s−r+1)`; previous spelling was `s`-fold too large. Statement corrected 2026-07-21: restored GK16's ω-generator hypothesis `orderOf ω = \|F\|−1` (unguarded form false, counterexample ω=−1 over 𝔽₁₀₁; PAPER_REVS #13). |
| `D2.19` | Extension field presentation `(B,F,e,ψ,φ)` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.ExtensionFieldPresentation` (structure wrapping `[Algebra B F]` + `Basis (Fin e) B F`), plus `IsSystematic` for the systematic variant. | Refactored to wrap Mathlib's `Algebra B F` + `Basis (Fin e) B F` directly (no parallel implementation of the field embedding / coordinate iso). `ψ := algebraMap B F`, `φ := basis.equivFun`, `coord j := proj j ∘ φ`. Univariate-multiplicity code (paper's namesake `DA.7`) is a *different* item, despite sharing a number. |
| `D2.20` | Extension code `C_F` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.extensionCode` (Set form) + `CodingTheory.extensionCodeSubmodule` (Submodule form, mirroring `ReedSolomon.code`'s shape in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)) | Set-level definition; uses coordinate-projections `P.coord j` of D2.19. **All closure laws proven**: `extensionCode_add_mem` (addition), `extensionCode_psi_smul_mem` (B-side scalar via `ψ`), and `extensionCode_smul_mem` (F-scalar closure, paper's D2.20 F-linearity claim, closed via basis-expansion through `Basis.sum_equivFun` + `Finset.sum_induction`). The Submodule packaging `extensionCodeSubmodule` bundles all three into a `Submodule F (ι → F)` (consumed by downstream code that wants a linear-code type; `coe_extensionCodeSubmodule` is the carrier bridge). Distance equality `δ_min(C_F) = δ_min(C_B)` from DP25 not formalised — separate paper item. |
| `L2.21` | `\|Λ(C_F,δ)\| = \|Λ(C_B^e,δ)\|` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` | BCFW25 Lemma D.3; PROVEN in-tree (coordinate Hamming isometry), sorry-free. |


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
| Remark 4.4 MCA with proximity loss | missing | none | No matching notion was found. |
| Fact 4.5 `εpg ≤ εca ≤ εmca` | missing | related CA/proximity-gap predicates in [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean) | Not expressible in current ArkLib interfaces because `εca` and `εmca` are not defined as numeric errors. |
| Lemma 4.6 MCA equals CA below unique decoding radius | missing | none | No general theorem of this form was found. |
| Lemma 4.7 interleaving degrades MCA by at most `t` | missing | none; see [`Jo26`](../papers/Jo26.md) | No general interleaving-vs-MCA theorem was found. Jo26 gives a sharper interleaving-stability target for generator MCA: no linear interleaving-width loss, exact transfer when the seed-set size is at most the field size, and a field-size weighted factor otherwise. |
| Theorem 4.8 AHIV17 general-code unique-decoding bound | missing | related but different [ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean) | AHIV22 is present, but not this general `εmca/εca` statement. |
| Theorem 4.9 RS unique-decoding results | present-but-different | `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` and `RS_correlatedAgreement_affineLines` in [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean) and [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean) | Item 1 is represented via predicate-style CA for RS. Item 2, the BCHKS25 proximity-loss refinement, is missing. The main file still has a `sorry` in the non-unique-decoding branch. |
| Remark 4.10 small proximity-loss simplification | missing | none | Depends on missing `εca` error-function interface. |
| Theorem 4.11 1.5-Johnson regime for general linear codes | missing | none | No matching theorem was found. |
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
| Theorem 5.2 small CA error implies list size `< |F|` | missing | none | No matching result was found. |
| Theorem 5.3 CA implies list decoding for a related RS code | missing | none | No matching result was found. |
| Theorem 5.4 separation between list decoding and CA | missing | none | No matching result was found. |

## Section 6: Toy Problem

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Definition 6.1 toy problem relation `R_C^ℓ` | missing | none | No matching relation was found. |
| Definition 6.3 relaxed toy relation `R̃_C,δ^ℓ` | missing | none | No matching relation was found. |
| Definition 6.4 erasure correction | present | `CodingTheory.SupportsErasureCorrection`, `eq_of_consistent_with_erased` in [ArkLib/Data/CodingTheory/Erasure.lean](../../../ArkLib/Data/CodingTheory/Erasure.lean) | Generic code-level predicate (lives under `CodingTheory/`, not a `ToyProblem` alias). Both clauses encoded: (i) recovery when erasures `< δ_min·n` with a matching codeword, (ii) `E f = none` otherwise. The paper's correction-time parameter `ecor` is not carried — ArkLib's extractors are uniformly cost-free. |
| Lemma 6.5 every additive code supports erasure correction | present | `CodingTheory.additive_code_supports_erasure_correction_grs12` in [ArkLib/Data/CodingTheory/Erasure.lean](../../../ArkLib/Data/CodingTheory/Erasure.lean) | Proven sorry-free and axiom-clean. Corrector built classically: below `minDist C` erasures the consistent codeword is unique (`eq_of_consistent_with_erased`), so classical choice yields the decoder. The paper's `O((s·n)³)` operation bound is outside ArkLib's cost-free model; only existence is formalized. |
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
| Definition A.5 round-by-round knowledge soundness | present-but-different | `Verifier.rbrKnowledgeSoundnessWorstCase` in [ArkLib/OracleReduction/Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | Matches the paper's probability and quantifier shape: the bad-transition probability is bounded at every *fixed* transcript prefix, quantified before the challenge draw. It remains materially different because ArkLib's current extensional security interface does not track the paper's extractor running-time bounds and permits noncomputable extractors. The averaged variants `Verifier.rbrKnowledgeSoundness` / `rbrKnowledgeSoundnessOneShot` in the same file instead bound the mixture over prover-sampled prefixes; `rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness` derives the averaged form from the paper-shaped probability bound with the same error constants. |
| Definition A.6 formal derivative | present-but-different | uses Mathlib polynomial derivative machinery; see [ArkLib/Data/CodingTheory/ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) for nearby polynomial infrastructure | ArkLib relies on the underlying polynomial derivative API rather than introducing the paper's local definition. |
| Definition A.7 univariate multiplicity code | present | `ReedSolomon.Multiplicity.umEvalOnPoints`, `umCode`, `mem_umCode_one_iff_mem_rsCode` in [ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean) | Submodule form `(Polynomial.degreeLT F k).map (umEvalOnPoints domain s)`, mirroring `ReedSolomon.code` and `ReedSolomon.Folded.frsCode`; encoder packages `s` formal-derivative evaluations per domain point; `s = 1` collapse to plain RS proven. Paper requirement `char(F) ≥ k` is documented but not baked into the bare definition. |

## Appendix B

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Claim B.1 collision bound for random functions | present | `Probability.exists_large_image_of_pairwise_collision_bound` in [ArkLib/Data/Probability/Combinatorial.lean](../../../ArkLib/Data/Probability/Combinatorial.lean) | Proven sorry-free. Route: `sum_fiber_sq_eq` (fiber partition + diagonal decomposition) and `cauchy_schwarz_fiber` (Mathlib's `sq_sum_le_card_mul_sum_sq` over `ℝ`); main theorem by contradiction via `ENNReal.tsum_lt_tsum` strict averaging. |

## Existing Inconsistencies

The largest mismatches between the paper and ArkLib are structural rather than mathematical.

1. Correlated agreement is formalized as predicates, not error functions.
   ArkLib currently exposes `δ_ε_correlatedAgreement...` predicates in
   [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean),
   while the paper is organized around numeric error functions `εpg`, `εca`, and `εmca`.

2. General MCA is not yet a first-class coding-theory notion in ArkLib.
   The TODO at the top of
   [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
   still lists mutual correlated agreement as missing. 
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

5. Several code families used centrally by the paper are absent.
   Folded Reed-Solomon, univariate multiplicity codes, subspace-design codes, and extension-field
   codes are not yet represented directly in ArkLib.

## Roadmap

### Phase 1: Align the Core Interfaces

1. Add numeric error-function wrappers for proximity gap, CA, and MCA in
   `ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`.
   These should coexist with the current predicate-style APIs rather than replace them.

2. Add a general code-level MCA definition there as well.

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
   This includes the paper's Fact 4.5 and Lemma 4.6, and the AHIV17/BCHKS25 style results.
   Treat Lemma 4.7's interleaving-loss statement as a baseline target sharpened by the newer
   generator-MCA interleaving-stability results in [`Jo26`](../papers/Jo26.md).

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
