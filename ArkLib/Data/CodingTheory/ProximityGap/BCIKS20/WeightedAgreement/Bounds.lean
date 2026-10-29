/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonBridge
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonComparison
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.LegacyComparison

/-!
# Explicit multiplicity budgets for weighted affine agreement

The exact line theorem uses the degree ratio `(deg - 1) / n`. The legacy weighted hypotheses
use the larger code-rate square root. This comparison retains enough budget for affine sampling.
-/

@[expose] public section

namespace ProximityGap.WeightedAgreement

open ReedSolomon ReedSolomon.HiddenDerivative

variable {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [DecidableEq F]

/-- The explicit weighted Johnson threshold supplies an exact line bound with twice its
exception count below the paper's budget. -/
theorem exists_lineExactAgreementBound_explicit {deg m : ℕ} (domain : ι ↪ F)
    (hdeg : 0 < deg) (hm : 3 ≤ m) {α : ℝ}
    (hα : (sqrtRate deg domain : ℝ) * (1 + 1 / (2 * (m : ℝ))) ≤ α)
    (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      LineExactAgreementBound domain deg ⌈(Fintype.card ι : ℝ) * α⌉₊ B ∧
      2 * B ≤ ((m : ℝ) + 1 / 2) ^ 7 * (Fintype.card ι : ℝ) ^ 2 /
        (3 * (sqrtRate deg domain : ℝ) ^ 3) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hfactor : 1 < 1 + 1 / (2 * (m : ℝ)) := by
    have : 0 < 1 / (2 * (m : ℝ)) := by positivity
    linarith
  have hspos : 0 < (sqrtRate deg domain : ℝ) := sqrtRate_pos hdeg
  have hslt : (sqrtRate deg domain : ℝ) < 1 := by nlinarith
  have hproper : deg < Fintype.card ι := by
    by_contra h
    have hfull : Fintype.card ι ≤ deg := by omega
    have hrate : LinearCode.rate (code domain deg) = 1 := by
      rw [rateOfLinearCode_eq_min_div, min_eq_right hfull]
      exact div_self (by exact_mod_cast hn.ne')
    simp [sqrtRate, hrate] at hslt
  have hs : (sqrtRate deg domain : ℝ) = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
    simp only [sqrtRate, rateOfLinearCode_eq_div hproper.le, NNRat.cast_div,
      NNRat.cast_natCast, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_natCast]
  obtain ⟨D, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdeg.ne'
  simp only [Nat.cast_succ] at hs
  by_cases hD : D = 0
  · subst D
    refine ⟨(Fintype.card ι).choose 2, by positivity,
      lineExactAgreementBound_constantCode domain _, ?_⟩
    have h := two_mul_choose_two_le_explicit_budget hn hm
    simpa only [hs, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add,
      ← sqrt_cube_eq_rpow_three_halves (by positivity : 0 ≤ 1 / (Fintype.card ι : ℝ))] using h
  · have hDpos : 1 ≤ D := by omega
    have hDn : D ≤ Fintype.card ι - 2 := by omega
    let eta : ℝ := α - Real.sqrt (johnsonRhoMinus (Fintype.card ι) D)
    have hroot : Real.sqrt (johnsonRhoMinus (Fintype.card ι) D) ≤
        (sqrtRate (D + 1) domain : ℝ) := by
      rw [hs]
      apply Real.sqrt_le_sqrt
      unfold johnsonRhoMinus
      gcongr
      exact_mod_cast Nat.le_succ D
    have heta : 0 < eta := by dsimp only [eta]; nlinarith
    have ha : johnsonAgreement (Fintype.card ι) D eta = α := by
      unfold johnsonAgreement eta
      ring
    refine ⟨johnsonExceptionCount (Fintype.card ι) D
      ⌈(Fintype.card ι : ℝ) * α⌉₊ eta, ?_, ?_, ?_⟩
    · unfold johnsonExceptionCount johnsonTheta
      positivity
    · have hline := lineExactAgreementBound_johnson domain hDpos hDn heta (by rwa [ha])
      simpa only [ha, mul_comm α] using hline
    · have h := two_mul_johnsonExceptionCount_le_explicit_budget hDpos hDn hm heta
        (A := ⌈(Fintype.card ι : ℝ) * α⌉₊)
        (by rw [ha, mul_comm]; exact Nat.le_ceil _)
        (by rw [ha, ← hs]; simpa only [mul_comm] using hα)
      rw [← sqrt_cube_eq_rpow_three_halves (by positivity)] at h
      simpa only [hs] using h

/-- The seventh-power budget also absorbs the affine sampling loss throughout the open
Johnson interval. -/
theorem exists_lineExactAgreementBound_seventh {deg : ℕ} (domain : ι ↪ F)
    (hdeg : 0 < deg) {α : ℝ}
    (hα : (sqrtRate deg domain : ℝ) < α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      LineExactAgreementBound domain deg ⌈(Fintype.card ι : ℝ) * α⌉₊ B ∧
      2 * B ≤ (deg : ℝ) ^ 2 /
        (2 * min (α - (sqrtRate deg domain : ℝ)) ((sqrtRate deg domain : ℝ) / 20)) ^ 7 := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hspos : 0 < (sqrtRate deg domain : ℝ) := sqrtRate_pos hdeg
  have hslt : (sqrtRate deg domain : ℝ) < 1 := hα.trans_le hα1
  have hproper : deg < Fintype.card ι := by
    by_contra h
    have hfull : Fintype.card ι ≤ deg := by omega
    have hrate : LinearCode.rate (code domain deg) = 1 := by
      rw [rateOfLinearCode_eq_min_div, min_eq_right hfull]
      exact div_self (by exact_mod_cast hn.ne')
    simp [sqrtRate, hrate] at hslt
  have hs : (sqrtRate deg domain : ℝ) = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
    simp only [sqrtRate, rateOfLinearCode_eq_div hproper.le, NNRat.cast_div,
      NNRat.cast_natCast, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_natCast]
  let b := min (α - (sqrtRate deg domain : ℝ)) ((sqrtRate deg domain : ℝ) / 20)
  have hb : 0 < b := lt_min (sub_pos.mpr hα) (by positivity)
  have hbrate : b ≤ Real.sqrt ((deg : ℝ) / Fintype.card ι) / 20 := by
    rw [← hs]
    exact min_le_right _ _
  obtain ⟨D, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdeg.ne'
  simp only [Nat.cast_succ] at hs hbrate ⊢
  by_cases hD : D = 0
  · subst D
    refine ⟨(Fintype.card ι).choose 2, by positivity,
      lineExactAgreementBound_constantCode domain _, ?_⟩
    have h := two_mul_choose_two_le_bciks hn hb (by simpa using hbrate)
    simpa only [Nat.cast_zero, zero_add, one_pow] using h
  · have hDpos : 1 ≤ D := by omega
    have hDn : D ≤ Fintype.card ι - 2 := by omega
    let eta : ℝ := α - Real.sqrt (johnsonRhoMinus (Fintype.card ι) D)
    have hroot : Real.sqrt (johnsonRhoMinus (Fintype.card ι) D) ≤
        (sqrtRate (D + 1) domain : ℝ) := by
      rw [hs]
      apply Real.sqrt_le_sqrt
      unfold johnsonRhoMinus
      gcongr
      linarith
    have hbeta : b ≤ eta := by
      have hh := min_le_left (α - (sqrtRate (D + 1) domain : ℝ))
        ((sqrtRate (D + 1) domain : ℝ) / 20)
      dsimp only [b, eta] at *
      linarith
    have heta : 0 < eta := hb.trans_le hbeta
    have ha : johnsonAgreement (Fintype.card ι) D eta = α := by
      unfold johnsonAgreement eta
      ring
    refine ⟨johnsonExceptionCount (Fintype.card ι) D
      ⌈(Fintype.card ι : ℝ) * α⌉₊ eta, ?_, ?_, ?_⟩
    · unfold johnsonExceptionCount johnsonTheta
      positivity
    · have hline := lineExactAgreementBound_johnson domain hDpos hDn heta (by rwa [ha])
      simpa only [ha, mul_comm α] using hline
    · exact two_mul_johnsonExceptionCount_le_bciks hDpos hDn heta
        (by rw [ha, mul_comm]; exact Nat.le_ceil _) hb hbeta hbrate

end ProximityGap.WeightedAgreement
