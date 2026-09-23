/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Endpoints
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Rounding
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Surplus

/-!
# Acceptance cases for weighted-support parameters

Concrete instances exercise the block, capacity, rounding, scalar, dimension and endpoint bounds.
-/

open ReedSolomon ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-! ### Block parameters -/

/-- At `δ = 1 / 4`, `n = 48`, `k = 10` the hypotheses hold with equality in `12 ≤ δ n`
(`⌈δ n⌉₊ = 12` and `10 + 12 ≤ 48`); here `K = max 10 6 = 10` and `D = 9`. -/
example :
    let K := max 10 ⌊(1 / 4 : ℝ) * (48 : ℕ) / 2⌋₊
    let D := K - 1
    (1 / 4 : ℝ) / 3 ≤ (D : ℝ) / (48 : ℕ) ∧ (D : ℝ) / (48 : ℕ) ≤ 1 - 1 / 4 ∧
      (K : ℝ) ≤ (1 - 1 / 4) * (48 : ℕ) := by
  have hc : ⌈(1 / 4 : ℝ) * (48 : ℕ)⌉₊ = 12 := by norm_num
  have h := blockDegree_bounds (δ := 1 / 4) (n := 48) (k := 10) (by norm_num) (by norm_num)
    (by rw [hc]; norm_num)
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The cutoff bound at `δ = 1 / 2`, `n = 10`, `k = 3`: `D = max 3 2 - 1 = 2`,
`g = min 1 ((1 / 2) / (2 / 10)) = 1`, and `D (1 + g) = 4 ≤ 3 + ⌈5⌉₊ = 8`. -/
example : (2 : ℝ) * (1 + rateGap (1 / 2) ((2 : ℝ) / 10)) ≤ 3 + 5 := by
  have hf : ⌊(1 / 2 : ℝ) * (10 : ℕ) / 2⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have hc : ⌈(1 / 2 : ℝ) * (10 : ℕ)⌉₊ = 5 := by norm_num
  have h := blockDegree_mul_one_add_rateGap_le (1 / 2) 10 3
  dsimp only at h
  rw [hf, hc] at h
  norm_num at h ⊢
  exact h

/-! ### Capacity parameters -/

/-- At `δ = 1 / 8` the order is at least `48000`. -/
example : 48000 ≤ capacityDerivativeOrder (1 / 8) :=
  (capacityDerivativeOrder_lower (by norm_num) (by norm_num)).1

example : 0 < weightedSupportMultiplicity 2 :=
  weightedSupportMultiplicity_pos_iff.mpr (by norm_num)

/-! ### Dimension inputs -/

/-- At `d = 3`, `δ = 1 / 4`, `ρ = 1 / 2` and `H = ξ / δ = 54 / 5`: here `g = 1 / 2`,
`a = 19 / 16`, `m = ⌈9720⌉₊`, and the five rounding inputs hold. -/
example :
    let g := rateGap (1 / 4) (1 / 2)
    let a := 1 + theta * g
    let m := ⌈100 * ((3 : ℕ) : ℝ) ^ 2 * (54 / 5)⌉₊
    let W := ⌊a * (3 : ℕ) * m / (54 / 5)⌋₊
    0 < m ∧ 0 < W ∧
      (W : ℝ) * (54 / 5) / (3 : ℕ) ≤ (1 + 3 * g / 8) * m ∧
      (W : ℝ) / (((3 : ℕ) : ℝ) * (g * m)) ≤ 10 / 27 ∧
      (999 / 1000) * (a / (g * (54 / 5))) ^ 2 ≤ ((W : ℝ) / (((3 : ℕ) : ℝ) * (g * m))) ^ 2 :=
  prescribed_dimension_inputs (1 / 4) (1 / 2) (54 / 5) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl (by norm_num [xi])

/-! ### Endpoint comparison -/

example :
    (543 / 500 : ℝ) < normalizedDimensionRankSurplus (1 / 4) (1 / 4) (54 / 5) (54 / 5) :=
  normalizedDimensionRankSurplus_gt (1 / 4) (1 / 4) (54 / 5) (54 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [xi]) (by norm_num [xi])

/-! ### Rounding parameters -/

example : (⌊(2 : ℝ) * 2 * 3 / 2⌋₊ : ℝ) * 2 / 2 ≤ 2 * 3 :=
  floorRadius_mul_div_le 2 2 2 3 (by norm_num)

example : (⌊(2 : ℝ) * 2 * 3 / 2⌋₊ : ℝ) / (2 * 1 * 3) ≤ 2 / (1 * 2) :=
  floorRadius_normalized_le 2 1 2 2 3 (by norm_num) (by norm_num) (by norm_num)

example :
    (1 - 1 / 2 : ℝ) ^ 2 * (2 / (1 * 2)) ^ 2 ≤
      ((⌊(2 : ℝ) * 2 * 3 / 2⌋₊ : ℝ) / (2 * 1 * 3)) ^ 2 :=
  floorRadius_sq_ge 2 2 1 2 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example :
  (1 - theta) * 1 * 3 * (1 - 3) ≤
      (3 : ℝ) * (1 + 1) + (2 - 1 : ℕ) - (4 + 0 + Nat.choose 2 2 : ℕ) * 2 / 2 :=
  remainingDegree_lower theta 3 1 2 2 3 0 4 (by omega) (by norm_num [theta]) (by norm_num)
    (by
      symm
      rw [Nat.floor_eq_iff (by norm_num [theta])]
      norm_num [theta]) (by norm_num [theta])

example :
    (3 : ℝ) * (1 + 1) + (2 - 1 : ℕ) - (4 + 0 + Nat.choose 2 2 : ℕ) * 2 / 2 ≤
      (1 - theta) * 1 * 3 * (1 + 2) :=
  remainingDegree_upper theta 2 1 2 2 3 0 4 (by omega) (by norm_num) (by
      symm
      rw [Nat.floor_eq_iff (by norm_num [theta])]
      norm_num [theta]) (by norm_num [theta])

example : ((4 + 0 + Nat.choose 2 2 : ℕ) : ℝ) / 2 ≤ ((1 + theta * 1) * 3 / 2) * (1 + 1) :=
  enlargedRadius_upper theta 1 1 2 2 3 0 4 (by omega) (by omega) (by norm_num [theta]) (by norm_num)
    (by
      symm
      rw [Nat.floor_eq_iff (by norm_num [theta])]
      norm_num [theta]) (by norm_num [theta])

/-! ### Scalar parameters -/

/-- At `δ = 1 / 4`, `ρ = 1 / 2`, `θ = 3 / 8` the closed form gives
`(1 + θ g) / g = (1 / 2 + 3 / 32) / (1 / 4) = 19 / 8 ≤ 4 = 1 / δ`. -/
example : (1 + theta * rateGap (1 / 4) (1 / 2)) / rateGap (1 / 4) (1 / 2) = 19 / 8 := by
  rw [one_add_mul_rateGap_div theta (by norm_num) (by norm_num)]
  norm_num [theta]

example : (1 : ℝ) ≤ rateGap (1 / 2) (1 / 2) * 2 :=
  le_rateGap_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! ### Multiplicative margin identity -/

example :
    let g := rateGap (1 : ℝ) 1
    let a := 1 + theta * g
    let B := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / 1 ^ 2 * 1 ^ (1 / a) / 1
    B * normalizedDimensionRankSurplus 1 1 1 (Real.log 1) =
      1 * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (999 / 1000) * (a / (g * 1)) ^ 2) :=
  normalized_surplus_product 1 1 1 1 (by norm_num) (by norm_num [rateGap]) (by norm_num)
