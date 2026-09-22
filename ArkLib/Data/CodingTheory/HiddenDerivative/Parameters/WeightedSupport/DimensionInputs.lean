/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Rounding
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RankRounding

/-!
# The rounding inputs of the weighted dimension estimate

The explicit lower bound on the dimension of the weighted support space
(`weighted_dimension_lower`) and the multiplicative margin (`multiplicative_margin_from_bounds`)
need five facts about the prescribed multiplicity `m = ⌈100 d ^ 2 H⌉₊` and radius
`W = ⌊a d m / H⌋₊` with `a = 1 + θ g`: `m` and `W` are positive, the mean
`W H / d ≤ (1 + 3 g / 8) m`, the normalized radius `W / (d (g m)) ≤ 10 / 27`, and the retention
`(999 / 1000) (a / (g H)) ^ 2 ≤ (W / (d (g m))) ^ 2`. This file derives them from the scalar
hypotheses on `δ`, `ρ` and `H`.

## Main statements

* `prescribed_dimension_inputs`
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The prescribed rounding inputs of the dimension estimate. Let `0 < δ ≤ 1 / 4`,
`0 < ρ ≤ 1 - δ`, `3 ≤ d` and `ξ / δ ≤ H`, and put `g = rateGap δ ρ`, `a = 1 + θ g`,
`m = ⌈100 d ^ 2 H⌉₊` and `W = ⌊a d m / H⌋₊`. Then `0 < m`, `0 < W`,
`W H / d ≤ (1 + 3 g / 8) m`, `W / (d (g m)) ≤ 10 / 27` and
`(999 / 1000) (a / (g H)) ^ 2 ≤ (W / (d (g m))) ^ 2`.

The mean is `floorRadius_mul_div_le`, the radius bound combines `floorRadius_normalized_le` with
`normalizedRadius_le_ten_twentySeven` (which needs the bounds on `δ` and `ρ`), and the retention is
`floorRadius_sq_ge` with `N = 2000`, where `(1999 / 2000) ^ 2 ≥ 999 / 1000`. The hypothesis `3 ≤ d`
makes the unrounded radius `a d m / H ≥ 100 d ^ 3` at least `2000`. -/
theorem prescribed_dimension_inputs (δ ρ H : ℝ) (d : ℕ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ)
    (hd : 3 ≤ d) (hHlo : xi / δ ≤ H) :
    let g := rateGap δ ρ
    let a := 1 + theta * g
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let W := ⌊a * d * m / H⌋₊
    0 < m ∧ 0 < W ∧
      (W : ℝ) * H / d ≤ (1 + 3 * g / 8) * m ∧
      (W : ℝ) / ((d : ℝ) * (g * m)) ≤ 10 / 27 ∧
      (999 / 1000) * (a / (g * H)) ^ 2 ≤ ((W : ℝ) / ((d : ℝ) * (g * m))) ^ 2 := by
  intro g a m W
  have hg : 0 < g := rateGap_pos hδ hρ
  have hH : 0 < H := (div_pos xi_pos hδ).trans_le hHlo
  have ha : 1 ≤ a := le_add_of_nonneg_right (mul_nonneg theta_pos.le hg.le)
  have hd0 : 0 < d := by omega
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hsize
  have hm : 0 < m := Nat.cast_pos.mp hmp
  have hR : 2000 ≤ a * d * m / H := by
    have hraw := InterpolationRounding.radius_lower 100 a H d m ha hH hsize
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hcube : (27 : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith
    linarith
  have hW : 0 < W := Nat.floor_pos.mpr (by linarith)
  have hden : (d : ℝ) * (g * m) = d * g * m := by ring
  refine ⟨hm, hW, ?_, ?_, ?_⟩
  · have h := floorRadius_mul_div_le a H d m (by linarith)
    have e : a = 1 + 3 * g / 8 := by simp only [a, theta]; ring
    rwa [← e]
  · rw [hden]
    exact normalizedRadius_le_ten_twentySeven hδ hδmax hρ hρmax hHlo
      (floorRadius_normalized_le a g H d m (by linarith) hg hH)
  · rw [hden]
    have h := floorRadius_sq_ge 2000 a g H d m (by norm_num) hg hH hd0 hm hR
    have hc : (999 / 1000 : ℝ) ≤ (1 - 1 / 2000) ^ 2 := by norm_num
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans h

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
