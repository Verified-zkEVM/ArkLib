/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CurveBridge
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.LegacyComparison

/-!
# Exact curve agreement with the explicit BCIKS20 budget

The finite Johnson count, and the pair-collision count for constant codes, fit the
seventh-power budget used by BCIKS20 and BCGM25. One exceptional set covers all candidates.
-/

@[expose] public section

namespace ProximityGap

open NNReal

/-- The explicit legacy multiplicity budget controls exact power agreement for every received
curve. The exceptional set is chosen before both the challenge and the candidate polynomial. -/
theorem exists_curve_exactPowerAgreement_explicit_budget
    {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]
    (k : ℕ) (D : ι ↪ F) (d m : ℕ) (δ : ℝ)
    (hkpos : 0 < k) (hproper : k < Fintype.card ι) (hm : 3 ≤ m)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 - (1 + 1 / (2 * (m : ℝ))) * (ReedSolomon.sqrtRate k D : ℝ)) :
    ∀ U : Fin (d + 1) → ι → F, ∃ E : Finset F,
      (E.card : ℝ) ≤ d * ((m + 1 / 2 : ℝ) ^ 7 * (Fintype.card ι : ℝ) ^ 2 /
        (3 * (ReedSolomon.sqrtRate k D : ℝ) ^ 3)) ∧
      ∀ z ∉ E, ∀ P : Polynomial F, P.degree < k →
        ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ ≤
          (ReedSolomon.polynomialAgreementSet D (ReedSolomon.powerBatchedWord U z) P).card →
        ReedSolomon.HasExactPowerAgreement D U (RingHom.id F) k z P := by
  classical
  have hn : 0 < Fintype.card ι := by omega
  let : Nonempty ι := Fintype.card_pos_iff.mp hn
  let s : ℝ := ReedSolomon.sqrtRate k D
  have hs : s = Real.sqrt ((k : ℝ) / Fintype.card ι) := by
    have hrate : (LinearCode.rate (ReedSolomon.code D k) : ℝ≥0) =
        (k : ℝ≥0) / Fintype.card ι := by
      rw [ReedSolomon.rateOfLinearCode_eq_div hproper.le]
      simp [NNRat.cast_div, NNRat.cast_natCast]
    simp only [s, hrate, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_natCast]
  have hs0 : 0 < s := ReedSolomon.sqrtRate_pos hkpos
  let A : ℕ := ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊
  let B : ℝ := (m + 1 / 2 : ℝ) ^ 7 * (Fintype.card ι : ℝ) ^ 2 / (3 * s ^ 3)
  have hA : A ≤ Fintype.card ι := by
    apply Nat.ceil_le.mpr
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (sub_le_self _ hδ_nonneg)
  intro U
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
  by_cases hK : K = 0
  · subst K
    obtain ⟨E, hE, hgood⟩ := ReedSolomon.uniformExactPowerAgreement_constantCode D U A
    refine ⟨E, ?_, hgood⟩
    have hcount : E.card ≤ d * (Fintype.card ι).choose 2 := hE.trans (Nat.div_le_self _ _)
    have hbudget := ReedSolomon.HiddenDerivative.two_mul_choose_two_le_explicit_budget hn hm
    have hb : ((Fintype.card ι).choose 2 : ℝ) ≤ B := by
      dsimp [B]
      rw [hs, ReedSolomon.HiddenDerivative.sqrt_cube_eq_rpow_three_halves (by positivity)]
      simp only [Nat.cast_one] at *
      have hnonneg : (0 : ℝ) ≤ (Fintype.card ι).choose 2 := Nat.cast_nonneg _
      linarith
    exact (show (E.card : ℝ) ≤ d * (Fintype.card ι).choose 2 by
      exact_mod_cast hcount).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d))
  · let eta : ℝ := 1 - δ - Real.sqrt
        (ReedSolomon.HiddenDerivative.johnsonRhoMinus (Fintype.card ι) K)
    have hKpos : 1 ≤ K := by omega
    have hKn : K ≤ Fintype.card ι - 2 := by omega
    have hsmall : Real.sqrt (ReedSolomon.HiddenDerivative.johnsonRhoMinus
        (Fintype.card ι) K) ≤ s := by
      rw [hs]
      apply Real.sqrt_le_sqrt
      unfold ReedSolomon.HiddenDerivative.johnsonRhoMinus
      gcongr
      exact_mod_cast Nat.le_succ K
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hgap : 0 < 1 - δ - s := by
      have hmfrac : 0 < 1 / (2 * (m : ℝ)) := by positivity
      have hδ' : δ ≤ 1 - (1 + 1 / (2 * (m : ℝ))) * s := hδ
      nlinarith [mul_pos hmfrac hs0]
    have heta : 0 < eta := by dsimp [eta]; linarith
    have ha : ReedSolomon.HiddenDerivative.johnsonAgreement (Fintype.card ι) K eta =
        1 - δ := by
      unfold ReedSolomon.HiddenDerivative.johnsonAgreement eta
      ring
    have hthreshold : ReedSolomon.HiddenDerivative.johnsonAgreement
        (Fintype.card ι) K eta * Fintype.card ι ≤ A := by
      rw [ha, mul_comm]
      exact Nat.le_ceil _
    obtain ⟨E, hE, hgood⟩ := ProximityGap.exists_johnson_curve_exactPowerAgreement_of_fintype
      D U hKpos hKn heta hthreshold hA
    refine ⟨E, ?_, hgood⟩
    have hb := ReedSolomon.HiddenDerivative.two_mul_johnsonExceptionCount_le_explicit_budget
      hKpos hKn hm heta hthreshold (by
        rw [ha]
        have hδ' : δ ≤ 1 - (1 + 1 / (2 * (m : ℝ))) * s := hδ
        rw [hs] at hδ'
        push_cast at hδ'
        linarith)
    have hb' : 2 * ReedSolomon.HiddenDerivative.johnsonExceptionCount
        (Fintype.card ι) K A eta ≤ B := by
      dsimp only [B]
      rw [hs, ReedSolomon.HiddenDerivative.sqrt_cube_eq_rpow_three_halves (by positivity)]
      simpa only [Nat.cast_succ] using hb
    calc
      (E.card : ℝ) ≤ 2 * d * ReedSolomon.HiddenDerivative.johnsonExceptionCount
          (Fintype.card ι) K A eta := hE
      _ = d * (2 * ReedSolomon.HiddenDerivative.johnsonExceptionCount
          (Fintype.card ι) K A eta) := by ring
      _ ≤ d * B := mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg d)


end ProximityGap
