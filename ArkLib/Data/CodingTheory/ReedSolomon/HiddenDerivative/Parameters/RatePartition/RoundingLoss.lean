/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Convergence

/-!
# Quantitative loss for the closed partition multiplicity

The floor error, simplex enlargement, and rounded contact factor together cost
less than one thousandth in the logarithm of the dimension/rank ratio.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- Three explicit scalar error bounds imply the required strict logarithmic loss. -/
theorem ratePartition_rounding_loss_lt {d L m lam lam0 : ℝ}
    (hd : 500 ≤ d) (hL : 0 < L) (hLupper : L ≤ 6 * d)
    (hm : 1000 * d ^ 2 * L ≤ m) (hlam : 0 ≤ lam) (hlamupper : lam ≤ (3 / 2) * L)
    (herror : lam - lam0 ≤ 2 * L / (1000 * d ^ 3)) :
    lam - lam0 + lam * (d * (d + 1) / 2) / m + Real.log (1 + (d + 1) * lam / m) <
      1 / 1000 := by
  have hdpos : 0 < d := by linarith
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hratio : lam / m ≤ 3 / (2000 * d ^ 2) := by
    apply (div_le_iff₀ hmpos).mpr
    have h := mul_le_mul_of_nonneg_left hm
      (by positivity : 0 ≤ 3 / (2000 * d ^ 2))
    have heq : 3 / (2000 * d ^ 2) * (1000 * d ^ 2 * L) = (3 / 2) * L := by field_simp; ring
    rw [heq] at h
    exact hlamupper.trans h
  have hfirst : lam - lam0 ≤ 1 / 100000 := by
    apply herror.trans
    apply (div_le_iff₀ (by positivity : 0 < 1000 * d ^ 3)).mpr
    have hd2 : 500 ^ 2 ≤ d ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hd2 hdpos.le
    nlinarith
  have hsecond : lam * (d * (d + 1) / 2) / m ≤ 4 / 5000 := by
    have h := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ d * (d + 1) / 2)
    have heq : 3 / (2000 * d ^ 2) * (d * (d + 1) / 2) = 3 * (d + 1) / (4000 * d) := by
      field_simp
      ring
    rw [heq] at h
    have hbound : 3 * (d + 1) / (4000 * d) ≤ 4 / 5000 := by
      apply (div_le_iff₀ (by positivity : 0 < 4000 * d)).mpr
      linarith
    simpa only [div_mul_eq_mul_div] using h.trans hbound
  have hthird : Real.log (1 + (d + 1) * lam / m) ≤ 1 / 100000 := by
    have hx : 0 ≤ (d + 1) * lam / m := by positivity
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + (d + 1) * lam / m)
    have h := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ d + 1)
    have hbound : (d + 1) * (3 / (2000 * d ^ 2)) ≤ 1 / 100000 := by
      field_simp
      nlinarith [sq_nonneg (d - 500)]
    have hsmall : (d + 1) * lam / m ≤ 1 / 100000 := by
      simpa only [mul_div_assoc] using h.trans hbound
    linarith
  linarith

/-- The closed multiplicity gives positive integer weight and controls its inverse floor error. -/
theorem ratePartition_closed_floor_bounds {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (hd : 500 ≤ d) :
    let L := Real.log (6 * d)
    let m := ratePartitionClosedMultiplicity d
    let W := ratePartitionWeight R a d m
    0 < m ∧ 0 < W ∧
      (d : ℝ) * m / W ≤ (3 / 2) * L ∧
      (d : ℝ) * m / W - R * L / a ≤ 2 * L / (1000 * (d : ℝ) ^ 3) := by
  let L := Real.log (6 * d)
  let m := ratePartitionClosedMultiplicity d
  let X := (m : ℝ) * a * d / (R * L)
  let W := ratePartitionWeight R a d m
  have hd' : (500 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have ha : 0 < a := hR.trans hRa
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hm : 1000 * (d : ℝ) ^ 2 * L ≤ m := Nat.le_ceil _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hXlower : 1000 * (d : ℝ) ^ 3 ≤ X := by
    have hmul := mul_le_mul_of_nonneg_right hm hdpos.le
    have hRa' := mul_le_mul_of_nonneg_left hRa.le (by positivity : 0 ≤ (m : ℝ) * d)
    dsimp [X]
    apply (le_div_iff₀ (mul_pos hR hL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmul hR.le]
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hXlower
  have hfloor : (W : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hfloor' : X < (W : ℝ) + 1 := Nat.lt_floor_add_one X
  have hcube : (1 : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hWpos : (0 : ℝ) < W := by nlinarith
  have hWtwo : (2 / 3 : ℝ) * X ≤ W := by nlinarith
  have hWhalf : 500 * (d : ℝ) ^ 3 ≤ W := by nlinarith
  let lam0 := R * L / a
  have hlam0 : 0 < lam0 := by dsimp [lam0]; positivity
  have hlam0L : lam0 ≤ L := by
    dsimp [lam0]
    apply (div_le_iff₀ ha).mpr
    nlinarith
  have hcancel : lam0 * X = (d : ℝ) * m := by
    dsimp [lam0, X]
    field_simp
  have hlam : (d : ℝ) * m / W ≤ (3 / 2) * lam0 := by
    apply (div_le_iff₀ hWpos).mpr
    have hh := mul_le_mul_of_nonneg_left hWtwo hlam0.le
    rw [← hcancel]
    nlinarith only [hh]
  have herror : (d : ℝ) * m / W - lam0 ≤ lam0 / W := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hWpos).mpr
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hWpos)]
    have hh := mul_le_mul_of_nonneg_left hfloor'.le hlam0.le
    rw [← hcancel]
    nlinarith only [hh]
  have herr' : lam0 / W ≤ 2 * L / (1000 * (d : ℝ) ^ 3) := by
    apply (div_le_div_iff₀ hWpos (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hWhalf (by positivity : 0 ≤ 2 * L)
    have hl := mul_le_mul_of_nonneg_right hlam0L (by positivity : 0 ≤ 1000 * (d : ℝ) ^ 3)
    nlinarith only [hh, hl]
  exact ⟨by exact_mod_cast hmpos, by exact_mod_cast hWpos,
    hlam.trans (mul_le_mul_of_nonneg_left hlam0L (by norm_num)), herror.trans herr'⟩

end ReedSolomon.HiddenDerivative
