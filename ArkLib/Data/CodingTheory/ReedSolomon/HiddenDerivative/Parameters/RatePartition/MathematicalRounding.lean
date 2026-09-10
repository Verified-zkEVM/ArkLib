/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Convergence

/-!
# The 300-based mathematical rate-partition multiplicity

This file proves the revised finite rounding chain without changing
`ratePartitionClosedMultiplicity`, the legacy 1000-based selector used by the executable
`UniformRateExecution`. The mathematical selector loses less than `1677 / 10^6` in the
logarithm of the finite source-to-rank ratio once `d ≥ 519`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- The revised mathematical multiplicity. The executable selector remains separate. -/
def ratePartitionMathematicalMultiplicity (d : ℕ) : ℕ :=
  ⌈300 * (d : ℝ) ^ 2 * Real.log (6 * d)⌉₊

private theorem mathematical_rounding_numeric {d : ℝ} (hd : 519 ≤ d) :
    2 / (300 * d ^ 2) +
        ((1 + 1 / d) / 600) / (1 - 1 / (300 * d ^ 3)) +
        ((1 + 1 / d) / (300 * d)) / (1 - 1 / (300 * d ^ 3)) <
      1677 / 1000000 := by
  have hdpos : 0 < d := by linarith
  have hd519 : (519 : ℝ) ≤ d := hd
  have hsq : (519 : ℝ) ^ 2 ≤ d ^ 2 := by nlinarith
  have hcube : (519 : ℝ) ^ 3 ≤ d ^ 3 := by nlinarith
  have hrecip : 1 / d ≤ (1 / 519 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hd
  have heps : 1 / (300 * d ^ 3) ≤ (1 / (300 * 519 ^ 3) : ℝ) := by
    gcongr
  have hdenpos : 0 < 1 - 1 / (300 * d ^ 3) := by
    have : 1 / (300 * d ^ 3) ≤ (1 / (300 * 519 ^ 3) : ℝ) := heps
    norm_num at this ⊢
    linarith
  have hdenmono :
      1 / (1 - 1 / (300 * d ^ 3)) ≤
        (1 / (1 - 1 / (300 * 519 ^ 3)) : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) (sub_le_sub_left heps 1)
  have hfirst : 2 / (300 * d ^ 2) ≤ (2 / (300 * 519 ^ 2) : ℝ) := by
    gcongr
  have hsecond :
      ((1 + 1 / d) / 600) / (1 - 1 / (300 * d ^ 3)) ≤
        (((1 + 1 / 519) / 600) /
          (1 - 1 / (300 * 519 ^ 3)) : ℝ) := by
    have hnum : (1 + 1 / d) / 600 ≤ ((1 + 1 / 519) / 600 : ℝ) := by
      gcongr
    calc
      ((1 + 1 / d) / 600) / (1 - 1 / (300 * d ^ 3)) =
          ((1 + 1 / d) / 600) * (1 / (1 - 1 / (300 * d ^ 3))) := by ring
      _ ≤ ((1 + 1 / 519) / 600) *
          (1 / (1 - 1 / (300 * 519 ^ 3))) :=
        mul_le_mul hnum hdenmono (by positivity) (by positivity)
      _ = ((1 + 1 / 519) / 600) /
          (1 - 1 / (300 * 519 ^ 3)) := by ring
  have hthird :
      ((1 + 1 / d) / (300 * d)) / (1 - 1 / (300 * d ^ 3)) ≤
        (((1 + 1 / 519) / (300 * 519)) /
          (1 - 1 / (300 * 519 ^ 3)) : ℝ) := by
    have hnum : (1 + 1 / d) / (300 * d) ≤
        ((1 + 1 / 519) / (300 * 519) : ℝ) := by
      apply div_le_div₀ (by positivity)
      · simpa [add_comm] using add_le_add_left hrecip 1
      · norm_num
      · nlinarith
    calc
      ((1 + 1 / d) / (300 * d)) / (1 - 1 / (300 * d ^ 3)) =
          ((1 + 1 / d) / (300 * d)) * (1 / (1 - 1 / (300 * d ^ 3))) := by ring
      _ ≤ ((1 + 1 / 519) / (300 * 519)) *
          (1 / (1 - 1 / (300 * 519 ^ 3))) :=
        mul_le_mul hnum hdenmono (by positivity) (by positivity)
      _ = ((1 + 1 / 519) / (300 * 519)) /
          (1 - 1 / (300 * 519 ^ 3)) := by ring
  calc
    _ ≤ 2 / (300 * (519 : ℝ) ^ 2) +
          ((1 + 1 / 519) / 600) / (1 - 1 / (300 * 519 ^ 3)) +
          ((1 + 1 / 519) / (300 * 519)) / (1 - 1 / (300 * 519 ^ 3)) := by
      linarith
    _ < 1677 / 1000000 := by norm_num

/-- The three rounding terms are below the revised exact logarithmic loss. -/
theorem ratePartition_rounding_loss_lt_300 {d L m lam lam0 : ℝ}
    (hd : 519 ≤ d) (hL : 0 < L) (hLupper : L ≤ d)
    (hm : 300 * d ^ 2 * L ≤ m) (hlam : 0 ≤ lam)
    (hlamupper : lam ≤ L / (1 - 1 / (300 * d ^ 3)))
    (herror : lam - lam0 ≤ 2 * L / (300 * d ^ 3)) :
    lam - lam0 + lam * (d * (d + 1) / 2) / m +
        Real.log (1 + (d + 1) * lam / m) <
      1677 / 1000000 := by
  have hdpos : 0 < d := by linarith
  have hepspos : 0 < 1 - 1 / (300 * d ^ 3) := by
    have hcube : (519 : ℝ) ^ 3 ≤ d ^ 3 := by nlinarith
    have heps : 1 / (300 * d ^ 3) ≤ (1 / (300 * 519 ^ 3) : ℝ) := by gcongr
    norm_num at heps ⊢
    linarith
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hfirst : lam - lam0 ≤ 2 / (300 * d ^ 2) := by
    calc
      lam - lam0 ≤ 2 * L / (300 * d ^ 3) := herror
      _ ≤ 2 * d / (300 * d ^ 3) := by gcongr
      _ = 2 / (300 * d ^ 2) := by field_simp
  have hratio : lam / m ≤
      1 / (300 * d ^ 2 * (1 - 1 / (300 * d ^ 3))) := by
    apply (div_le_iff₀ hmpos).2
    have hscale := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 1 / (300 * d ^ 2 * (1 - 1 / (300 * d ^ 3))) by positivity)
    have heq :
        1 / (300 * d ^ 2 * (1 - 1 / (300 * d ^ 3))) *
            (300 * d ^ 2 * L) =
          L / (1 - 1 / (300 * d ^ 3)) := by field_simp
    rw [heq] at hscale
    exact hlamupper.trans hscale
  have hsecond : lam * (d * (d + 1) / 2) / m ≤
      ((1 + 1 / d) / 600) / (1 - 1 / (300 * d ^ 3)) := by
    have h := mul_le_mul_of_nonneg_right hratio (show 0 ≤ d * (d + 1) / 2 by positivity)
    calc
      lam * (d * (d + 1) / 2) / m =
          (lam / m) * (d * (d + 1) / 2) := by ring
      _ ≤ (1 / (300 * d ^ 2 * (1 - 1 / (300 * d ^ 3)))) *
          (d * (d + 1) / 2) := h
      _ = ((1 + 1 / d) / 600) /
          (1 - 1 / (300 * d ^ 3)) := by field_simp; norm_num
  have hx : 0 ≤ (d + 1) * lam / m := by positivity
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 1 + (d + 1) * lam / m by positivity)
  have hthird : Real.log (1 + (d + 1) * lam / m) ≤
      ((1 + 1 / d) / (300 * d)) / (1 - 1 / (300 * d ^ 3)) := by
    apply hlog.trans
    have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ d + 1 by positivity)
    calc
      1 + (d + 1) * lam / m - 1 = (d + 1) * (lam / m) := by ring
      _ ≤ (d + 1) *
          (1 / (300 * d ^ 2 * (1 - 1 / (300 * d ^ 3)))) := h
      _ = ((1 + 1 / d) / (300 * d)) /
          (1 - 1 / (300 * d ^ 3)) := by field_simp
  have hnumeric := mathematical_rounding_numeric hd
  linarith

/-- The revised closed multiplicity controls the inverse floor loss without changing the
legacy executable selector. -/
theorem ratePartition_mathematical_floor_bounds {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (hd : 519 ≤ d) :
    let L := Real.log (6 * d)
    let m := ratePartitionMathematicalMultiplicity d
    let W := ratePartitionWeight R a d m
    0 < m ∧ 0 < W ∧
      (d : ℝ) * m / W ≤ L / (1 - 1 / (300 * (d : ℝ) ^ 3)) ∧
      (d : ℝ) * m / W - R * L / a ≤
        2 * L / (300 * (d : ℝ) ^ 3) := by
  let L := Real.log (6 * d)
  let m := ratePartitionMathematicalMultiplicity d
  let X := (m : ℝ) * a * d / (R * L)
  let W := ratePartitionWeight R a d m
  let eps : ℝ := 1 / (300 * (d : ℝ) ^ 3)
  let lam0 := R * L / a
  have hd' : (519 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have ha : 0 < a := hR.trans hRa
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hm : 300 * (d : ℝ) ^ 2 * L ≤ m := Nat.le_ceil _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hXlower : 300 * (d : ℝ) ^ 3 ≤ X := by
    have hmul := mul_le_mul_of_nonneg_right hm hdpos.le
    have hRa' := mul_le_mul_of_nonneg_left hRa.le (show 0 ≤ (m : ℝ) * d by positivity)
    dsimp [X]
    apply (le_div_iff₀ (mul_pos hR hL)).2
    nlinarith [mul_le_mul_of_nonneg_left hmul hR.le]
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hXlower
  have hepspos : 0 < 1 - eps := by
    dsimp [eps]
    have heps : 1 / (300 * (d : ℝ) ^ 3) ≤
        (1 / (300 * 519 ^ 3) : ℝ) := by gcongr
    norm_num at heps ⊢
    linarith
  have hepsX : 1 ≤ eps * X := by
    dsimp [eps]
    calc
      1 ≤ X / (300 * (d : ℝ) ^ 3) :=
        (le_div_iff₀ (show 0 < 300 * (d : ℝ) ^ 3 by positivity)).2
          (by simpa only [one_mul] using hXlower)
      _ = 1 / (300 * (d : ℝ) ^ 3) * X := by ring
  have hfloor : (W : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hfloor' : X < (W : ℝ) + 1 := Nat.lt_floor_add_one X
  have hWlower : (1 - eps) * X ≤ W := by
    nlinarith [hepsX]
  have hWpos : (0 : ℝ) < W := by
    have : 0 < (1 - eps) * X := mul_pos hepspos hXpos
    exact this.trans_le hWlower
  have hlam0 : 0 < lam0 := by dsimp [lam0]; positivity
  have hlam0L : lam0 ≤ L := by
    dsimp [lam0]
    apply (div_le_iff₀ ha).2
    nlinarith
  have hcancel : lam0 * X = (d : ℝ) * m := by
    dsimp [lam0, X]
    field_simp
  have hlam : (d : ℝ) * m / W ≤ lam0 / (1 - eps) := by
    rw [div_le_div_iff₀ hWpos hepspos]
    rw [← hcancel]
    calc
      lam0 * X * (1 - eps) = lam0 * ((1 - eps) * X) := by ring
      _ ≤ lam0 * W := mul_le_mul_of_nonneg_left hWlower hlam0.le
  have hlamL : (d : ℝ) * m / W ≤ L / (1 - eps) := by
    exact hlam.trans (div_le_div_of_nonneg_right hlam0L hepspos.le)
  have hepshalf : eps ≤ 1 / 2 := by
    dsimp [eps]
    have heps : 1 / (300 * (d : ℝ) ^ 3) ≤
        (1 / (300 * 519 ^ 3) : ℝ) := by gcongr
    norm_num at heps ⊢
    linarith
  have hinv : 1 / (1 - eps) ≤ 2 := by
    rw [div_le_iff₀ hepspos]
    linarith
  have herror : (d : ℝ) * m / W - lam0 ≤ 2 * L * eps := by
    calc
      (d : ℝ) * m / W - lam0 ≤ lam0 / (1 - eps) - lam0 := sub_le_sub_right hlam _
      _ = lam0 * eps / (1 - eps) := by field_simp; ring
      _ ≤ L * eps / (1 - eps) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlam0L (by dsimp [eps]; positivity)) hepspos.le
      _ ≤ L * eps * 2 := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinv)
          (mul_nonneg hL.le (by dsimp [eps]; positivity))
      _ = 2 * L * eps := by ring
  refine ⟨by exact_mod_cast hmpos, by exact_mod_cast hWpos,
    by simpa only [eps] using hlamL, ?_⟩
  calc
    (d : ℝ) * m / W - R * L / a ≤ 2 * L * eps := herror
    _ = 2 * L / (300 * (d : ℝ) ^ 3) := by dsimp only [eps]; ring

/-- The revised finite ratio is within the exact logarithmic loss of its limiting value. -/
theorem ratePartition_mathematical_ratio_gt {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (hd : 519 ≤ d) :
    ratePartitionGamma R a d * Real.exp (-(1677 / 1000000 : ℝ)) <
      ratePartitionFiniteRatio R a d (ratePartitionMathematicalMultiplicity d) := by
  obtain ⟨hm, hW, hlam, herror⟩ := ratePartition_mathematical_floor_bounds hR hRa hd
  let m := ratePartitionMathematicalMultiplicity d
  let W := ratePartitionWeight R a d m
  let L := Real.log (6 * d)
  let lam := (d : ℝ) * m / W
  let lam0 := R * L / a
  have hd' : (519 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hLupper : L ≤ d := by
    have hquad : (d : ℝ) ^ 2 / 2 ≤ Real.exp d := by
      simpa using Real.pow_div_factorial_le_exp (x := (d : ℝ)) hdpos.le 2
    have hexp : 6 * (d : ℝ) < Real.exp d := by
      calc
        6 * (d : ℝ) < d ^ 2 / 2 := by nlinarith
        _ ≤ Real.exp d := hquad
    exact (Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 6 * d)).2 hexp |>.le
  have hden : 0 < 1 + ((d : ℝ) + 1) * lam / m := by dsimp [lam]; positivity
  let loss := lam - lam0 + lam * ((d : ℝ) * (d + 1) / 2) / m +
    Real.log (1 + ((d : ℝ) + 1) * lam / m)
  have hloss : loss < 1677 / 1000000 :=
    ratePartition_rounding_loss_lt_300 hd' hL hLupper (Nat.le_ceil _)
      (by dsimp [lam]; positivity) (by simpa only [lam, L] using hlam)
      (by simpa only [lam, lam0, L] using herror)
  have hGamma : ratePartitionGamma R a d = (27 / 20) * R * (d + 1) *
      Real.exp (-lam0) := by
    dsimp [ratePartitionGamma, lam0, L]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 6 * d)]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  have heq : ratePartitionFiniteRatio R a d m =
      ratePartitionGamma R a d * Real.exp (-loss) := by
    rw [hGamma, mul_assoc, ← Real.exp_add]
    dsimp [ratePartitionFiniteRatio]
    have hlameq : (d : ℝ) / ((W : ℝ) / m) = lam := by dsimp [lam]; field_simp
    change (27 / 20) * R * (d + 1) *
      Real.exp (-((d : ℝ) / ((W : ℝ) / m)) * (1 + (d * (d + 1) / 2) / m)) /
      (1 + (d + 1) * ((d : ℝ) / ((W : ℝ) / m)) / m) = _
    rw [hlameq, div_eq_mul_inv]
    have hinv : (1 + ((d : ℝ) + 1) * lam / m)⁻¹ =
        Real.exp (-Real.log (1 + ((d : ℝ) + 1) * lam / m)) := by
      rw [Real.exp_neg, Real.exp_log hden]
    rw [hinv, mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [loss]
    ring
  rw [heq]
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (neg_lt_neg hloss))
  rw [hGamma]
  positivity

end ReedSolomon.HiddenDerivative
