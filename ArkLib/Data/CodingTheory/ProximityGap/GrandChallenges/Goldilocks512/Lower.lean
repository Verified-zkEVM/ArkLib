/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.CertificateWitnesses
public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.Goldilocks512.Arithmetic

/-!
# Safe-side witnesses for `RS[512, 128]` at `ε* = 2⁻¹²⁸`

This file instantiates `GrandChallenges.CertificateWitnesses` for the Reed--Solomon code
`RS[F, domain, 128]` of length `512` (rate `1/4`) on any evaluation domain, at threshold
`ε* = 2⁻¹²⁸` and radius `δ = 273/512` (agreement `239`, beyond the Johnson agreement `256`):

* `mcaLowerWitness`: a `McaLowerWitness`, when `ringChar F` is `0` or exceeds `280` and
  `968 363 869 378 722 615 · 2 ¹²⁸ ≤ |F|`;
* `listLowerWitness`: a `ListLowerWitness` for every interleaving `m`, when `ringChar F` is `0`
  or exceeds `260` and `399 224 017 · 2 ¹²⁸ ≤ |F|`.

Both hold for a field with `p ^ 3` elements, `p = 2 ^ 64 - 2 ^ 32 + 1` (the Goldilocks prime).

The certificate parameters are `(m, M, μ, h) = (609, 280, 1148, 271081)` for mutual correlated
agreement and `(546, 260, 1020, 10 ^ 9)` for list decoding; their slot inequalities are checked
in `Goldilocks512.Arithmetic`. The contribution here is the choice of parameters; the mathematics
is that of the cited papers as already formalized in ArkLib.

## References

* [DKT26] for first-order hidden-derivative certificates and the squarefree bounds;
* [ABF26] for the grand-challenge formulation.
-/

@[expose] public section

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative
open scoped NNReal

namespace ProximityGap.GrandChallenges.Goldilocks512

/-- Safe-side witness for the mutual-correlated-agreement grand challenge: on any `512`-point
domain, `RS[F, domain, 128]` has affine-line MCA error at most `2⁻¹²⁸` at `δ = 273/512`, when
`ringChar F` is `0` or exceeds `280` and `968 363 869 378 722 615 · 2 ¹²⁸ ≤ |F|`.

It is `noncomputable` because the witness carries real-valued error bounds. -/
noncomputable def mcaLowerWitness {F : Type} [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] (hchar : ringChar F = 0 ∨ 280 < ringChar F)
    (hcard : 968363869378722615 * 2 ^ 128 ≤ Fintype.card F) (domain : Fin 512 ↪ F) :
    McaLowerWitness (ReedSolomon.code domain 128) (1 / 2 ^ 128) := by
  refine McaLowerWitness.ofLineExactAgreement (δ := 273 / 512) domain
    (lineExactAgreementBound_of_heightSlotCount (m := 609) domain (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      Arithmetic.mca_rowSlotBound_lt_heightSlotCount (by simpa using hchar))
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    (by simp only [Fintype.card_fin]; norm_num) ?_
  have hc : ((968363869378722615 * 2 ^ 128 : ℕ) : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast hcard
  simp only [FirstOrder.Squarefree.retainedSquarefreeLineAgreementEnvelope,
    FirstOrder.Squarefree.retainedOrdinaryCurveAgreementCharge, agreementIncidenceRatio]
  push_cast at hc ⊢
  norm_num
  linarith

/-- For every `t`, the `t`-fold interleaving of `RS[F, domain, 128]` has list size at most
`399 224 017` at `δ = 273/512`, when `ringChar F` is `0` or exceeds `260`. -/
theorem lambda_interleaved_le {F : Type} [Field F] (hchar : ringChar F = 0 ∨ 260 < ringChar F)
    (domain : Fin 512 ↪ F) (t : ℕ) :
    Code.Lambda ((ReedSolomon.code domain 128 : Set (Fin 512 → F)) ^⋈ (Fin t)) (273 / 512) ≤
      ((399224017 : ℕ) : ℕ∞) := by
  have hthr : capacityAgreementThreshold (111 / 512) 512 128 = 239 := by
    simp only [capacityAgreementThreshold]; norm_num
  have hrad : capacityRadius (111 / 512) 512 128 = 273 / 512 := by
    simp only [capacityRadius]; norm_num
  rw [← hrad]
  refine lambda_interleaved_le_of_heightSlotCount (m := 546) (M := 260) (μ := 1020)
    (h := 1000000000) (111 / 512) (by norm_num) (by norm_num) domain t 399224017 (by norm_num)
    (by rw [hthr]; norm_num) (by rw [hthr]; norm_num) (by norm_num) (by rw [hthr]; norm_num)
    (by rw [hthr]; exact Arithmetic.lst_rowSlotBound_lt_heightSlotCount) (by simpa using hchar) ?_
  rw [hthr]
  have h1 : firstOrderCurveFiberStageOne 128 1020 260 (regularTaylorExponent (128 - 1)) =
      116003560 := by decide
  have h2 : FirstOrder.Squarefree.ordinaryDegreeEnvelope 1020 260 = 461780 := by decide
  rw [h1, h2]
  norm_num

/-- Safe-side witness for the list-decoding grand challenge: for every `m`, the `m`-fold
interleaving of `RS[F, domain, 128]` has list size at most `2⁻¹²⁸ · |F|` at `δ = 273/512`, when
`ringChar F` is `0` or exceeds `260` and `399 224 017 · 2 ¹²⁸ ≤ |F|`.

It is `noncomputable` because the witness carries real-valued error bounds. -/
noncomputable def listLowerWitness {F : Type} [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] (hchar : ringChar F = 0 ∨ 260 < ringChar F)
    (hcard : 399224017 * 2 ^ 128 ≤ Fintype.card F) (domain : Fin 512 ↪ F) (m : ℕ) :
    ListLowerWitness (ReedSolomon.code domain 128 : Set (Fin 512 → F)) m (1 / 2 ^ 128) :=
  ListLowerWitness.ofLe (δ := 273 / 512) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by
    have hδ : ((273 / 512 : ℝ≥0) : ℝ) = 273 / 512 := by push_cast; ring
    rw [hδ]
    have hI := lambda_interleaved_le hchar domain m
    calc ((Code.Lambda ((ReedSolomon.code domain 128 : Set (Fin 512 → F)) ^⋈ (Fin m))
            (273 / 512) : ℕ∞) : ENNReal)
        ≤ (((399224017 : ℕ) : ℕ∞) : ENNReal) := by exact_mod_cast hI
      _ = ((399224017 : ℕ) : ENNReal) := by simp
      _ ≤ ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) * ((Fintype.card F : ℕ) : ENNReal) := by
        rw [← ENNReal.coe_natCast, ← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_mul,
          ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
        have h := (Nat.cast_le (α := ℝ)).mpr hcard
        push_cast at h ⊢
        linarith)

end ProximityGap.GrandChallenges.Goldilocks512
