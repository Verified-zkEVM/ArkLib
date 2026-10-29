/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonBridge
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonComparison

/-!
# Correlated agreement over Reed–Solomon affine lines

The unique-decoding bound and the proved Johnson exact-agreement bound give the BCIKS20
error estimate throughout the open Johnson radius. Constant messages use the collision bound.
-/

@[expose] public section

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Finset Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]

omit [DecidableEq ι] in
/-- Theorem 1.4 of [BCIKS20], correlated agreement over lines. For a positive message
dimension and a radius strictly below `1 - sqrtRate`, if the probability that `u₀ + z • u₁`
is `δ`-close to the code is greater than `errorBound δ deg domain`, then the two words
have correlated agreement on at least a `1 - δ` fraction of coordinates. -/
theorem RS_correlatedAgreement_affineLines {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg) (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  -- Full codes have square-root rate one, so the strict radius hypothesis excludes them.
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hproper : deg < Fintype.card ι := by
    by_contra h
    have hfull : Fintype.card ι ≤ deg := by omega
    have hrate : LinearCode.rate (ReedSolomon.code domain deg) = 1 := by
      rw [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_right hfull]
      exact div_self (by exact_mod_cast hn.ne')
    simp [ReedSolomon.sqrtRate, hrate] at hδ
  let : NeZero deg := ⟨hdeg.ne'⟩
  by_cases hUD : δ ≤ Code.relativeUniqueDecodingRadius
      (C := (ReedSolomon.code domain deg : Set (ι → F)))
  · exact RS_correlatedAgreement_affineLines_uniqueDecodingRegime hUD
  have hrate : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) =
      (deg : ℝ≥0) / Fintype.card ι := by
    rw [ReedSolomon.rateOfLinearCode_eq_div hproper.le]
    simp [NNRat.cast_div, NNRat.cast_natCast]
  have hJ : δ ∈ Set.Ioo
      ((1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
      (1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) := by
    refine ⟨?_, hδ⟩
    rw [hrate]
    rwa [ReedSolomon.relativeUniqueDecodingRadius_RS_eq hproper.le, not_le] at hUD
  let s : ℝ := ReedSolomon.sqrtRate deg domain
  have hs0 : 0 < s := ReedSolomon.sqrtRate_pos hdeg
  have hs1 : s ≤ 1 := ReedSolomon.sqrtRate_le_one' deg domain
  have hs : s = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
    simp only [s, hrate, Real.coe_sqrt, NNReal.coe_div,
      NNReal.coe_natCast]
  have hδR : (δ : ℝ) < 1 - s := by
    have h := (NNReal.coe_lt_coe).mpr hδ
    rwa [NNReal.coe_sub (ReedSolomon.sqrtRate_le_one deg domain), NNReal.coe_one] at h
  let b : ℝ := min (1 - s - δ) (s / 20)
  have hb : 0 < b := lt_min (by linarith) (by positivity)
  have hbRate : b ≤ Real.sqrt ((deg : ℝ) / Fintype.card ι) / 20 := by
    rw [← hs]
    exact min_le_right _ _
  have herr : (errorBound δ deg domain : ℝ) =
      (deg : ℝ) ^ 2 / ((2 * b) ^ 7 * Fintype.card F) := by
    rw [errorBound_eq_johnson hJ]
    change ((deg ^ 2 : ℝ≥0) : ℝ) / _ = _
    simp [b, s, NNReal.coe_sub hδ.le,
      NNReal.coe_sub (ReedSolomon.sqrtRate_le_one deg domain)]
  have hline : ReedSolomon.LineExactAgreementBound domain deg
      ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ ((deg : ℝ) ^ 2 / (2 * b) ^ 7) := by
    obtain ⟨D, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdeg.ne'
    by_cases hD : D = 0
    · subst D
      simpa using (lineExactAgreementBound_constantCode domain
        ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊).mono
        (ReedSolomon.HiddenDerivative.choose_two_le_bciks hn hb (by simpa using hbRate))
    · let eta : ℝ := 1 - δ - Real.sqrt
        (ReedSolomon.HiddenDerivative.johnsonRhoMinus (Fintype.card ι) D)
      have hDpos : 1 ≤ D := by omega
      have hDn : D ≤ Fintype.card ι - 2 := by omega
      have hsmall : Real.sqrt
          (ReedSolomon.HiddenDerivative.johnsonRhoMinus (Fintype.card ι) D) ≤ s := by
        rw [hs]
        apply Real.sqrt_le_sqrt
        unfold ReedSolomon.HiddenDerivative.johnsonRhoMinus
        gcongr
        exact_mod_cast Nat.le_succ D
      have hbeta : b ≤ eta := by
        have := min_le_left (1 - s - (δ : ℝ)) (s / 20)
        dsimp only [b, eta] at *
        linarith
      have heta : 0 < eta := hb.trans_le hbeta
      have ha : ReedSolomon.HiddenDerivative.johnsonAgreement (Fintype.card ι) D eta =
          1 - δ := by
        unfold ReedSolomon.HiddenDerivative.johnsonAgreement eta
        ring
      have hl := lineExactAgreementBound_johnson domain hDpos hDn heta
        (by rw [ha]; exact sub_le_self _ δ.coe_nonneg)
      rw [ha, mul_comm] at hl
      apply hl.mono
      have hc := ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_bciks
        hDpos hDn heta (A := ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊)
        (by rw [ha, mul_comm]; exact Nat.le_ceil _) hb hbeta (by simpa using hbRate)
      simpa using hc
  apply (δ_ε_correlatedAgreementAffineLines_iff_epsCa_le _ _ _).mpr
  apply (epsCa_le_mcaError_affineLine (ReedSolomon.code domain deg) δ).trans
  apply (ReedSolomon.mcaError_affineLine_le_of_exactAgreement domain _ hline (δ : ℝ)
    le_rfl).trans
  rw [← ENNReal.ofReal_coe_nnreal, herr]
  apply ENNReal.ofReal_le_ofReal
  rw [div_div]


end CoreResults

end ProximityGap
