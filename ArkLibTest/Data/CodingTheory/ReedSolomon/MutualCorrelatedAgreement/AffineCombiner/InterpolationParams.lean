/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterpolationParams

/-!
# Acceptance cases for the interpolation parameters

A Reed–Solomon case at `e = 1` checks the exact finite budgets.
A Reed–Muller case checks the constants of Theorem 7.1 in [CWYZ26].
It has `q₀ = 2⁸`, `k = 2`, `n = q₀^k = 2¹⁶`, `e = q₀^(k-1) = 2⁸`, Reed–Muller degree `64`,
so `ρ = 1/4` and the univariate degree is `ρ n = 2¹⁴`, and `η = 1/4`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon

private theorem sqrt_rs : √((16 : ℕ) / ((100 : ℕ) : ℝ)) = 2 / 5 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

-- The standing hypotheses hold at `d = 16`, `n = 100`, `e = 1`, `η = 1/2`.
example : AffineParams 16 100 1 (1 / 2) := by
  refine ⟨by norm_num, by norm_num, le_rfl, by norm_num, ?_, ?_⟩
  · rw [sqrt_rs]; norm_num
  · norm_num

-- At `e = 1` the parameter choice has these exact finite budgets.
example : affineMultiplicity (1 / 2) = 4 ∧ affineYZBudget 16 100 (1 / 2) = 42 ∧
    affineThreshold 16 100 (1 / 2) = 90 ∧ affinePersistenceThreshold 16 100 1 (1 / 2) = 64 ∧
    affineRootBudget 16 100 1 (1 / 2) = 19 := by
  unfold affineRootBudget affineYZBudget affineThreshold affinePersistenceThreshold
    affineMultiplicity
  have hceil : ⌈(675 : ℝ) / 16⌉₊ = 43 := (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  rw [sqrt_rs]
  norm_num [hceil]

private theorem sqrt_rm : √((16384 : ℕ) / ((65536 : ℕ) : ℝ)) = 1 / 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

/-- The Reed–Muller case satisfies the standing hypotheses, with `q₀ η² = 16 = 4 / ρ`. -/
private theorem rmParams : AffineParams 16384 65536 256 (1 / 4) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [sqrt_rm]; norm_num
  · norm_num

-- The Reed–Muller constants: `m = 8`, `D = 96`, `A = 49152`, `B = 40704` and `M = 22`.
private theorem rm_values : affineMultiplicity (1 / 4) = 8 ∧
    affineYZBudget 16384 65536 (1 / 4) = 96 ∧ affineThreshold 16384 65536 (1 / 4) = 49152 ∧
    affinePersistenceThreshold 16384 65536 256 (1 / 4) = 40704 ∧
    affineRootBudget 16384 65536 256 (1 / 4) = 22 := by
  unfold affineRootBudget affineYZBudget affineThreshold affinePersistenceThreshold
    affineMultiplicity
  have hceil : ⌈(289 : ℝ) / 3⌉₊ = 97 := (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  rw [sqrt_rm]
  norm_num [hceil]

-- The surplus condition `U + e D ≤ m A` holds with `U = ⌈d (m + 1/2) / √ρ⌉ = 278528`.
example : ⌈((16384 : ℕ) : ℝ) * ((((8 : ℕ) : ℝ) + 1 / 2) / (1 / 2))⌉₊ = 278528 ∧
    278528 + 256 * affineYZBudget 16384 65536 (1 / 4) ≤
      8 * affineThreshold 16384 65536 (1 / 4) := by
  have hU : ⌈((16384 : ℕ) : ℝ) * ((((8 : ℕ) : ℝ) + 1 / 2) / (1 / 2))⌉₊ = 278528 := by
    norm_num
  refine ⟨hU, ?_⟩
  have h := rmParams.ceil_add_mul_yzBudget_le
  rw [rm_values.1, sqrt_rm, hU] at h
  exact h

-- The interpolation surplus holds at these budgets.
open Polynomial.SymbolicInterpolation in
example : 65536 * (constraintSupport 8 (96 + 1)).card <
    (monomialSupport 16384 (8 * 49152 - 256 * 96) (22 + 1) (96 + 1)).card := by
  obtain ⟨hm, hD, hA, -, hM⟩ := rm_values
  have h := rmParams.surplus
  rw [hm, hD, hA, hM] at h
  exact h

-- The gap `v = n / (A - B - e + 1) = 65536 / 8193` is below `8 = 2 / η`.
example : (65536 : ℝ) / (affineThreshold 16384 65536 (1 / 4) -
    affinePersistenceThreshold 16384 65536 256 (1 / 4) - 256 + 1 : ℕ) = 65536 / 8193 ∧
    (65536 : ℝ) / 8193 < 8 := by
  obtain ⟨-, -, hA, hB, -⟩ := rm_values
  rw [hA, hB]
  norm_num

-- The side conditions `(d₀ + 1) e < B` and `n (d₀ + 1) e < B²` with `d₀ = 64`.
example : (64 + 1) * 256 < affinePersistenceThreshold 16384 65536 256 (1 / 4) ∧
    65536 * ((64 + 1) * 256) < affinePersistenceThreshold 16384 65536 256 (1 / 4) ^ 2 := by
  have h1 := rmParams.add_lt_persistenceThreshold
  have h2 := rmParams.card_mul_add_lt_sq
  exact ⟨by simpa using h1, by simpa using h2⟩

-- The Johnson factor `ℓ = n (B - (d₀ + 1) e) / (B² - n (d₀ + 1) e)` is about `2.78 < 3`,
-- within the general estimate `ℓ ≤ 4 / η = 16`.
example : (65536 : ℝ) * ((affinePersistenceThreshold 16384 65536 256 (1 / 4) : ℝ) - 16384 - 256) /
      ((affinePersistenceThreshold 16384 65536 256 (1 / 4) : ℝ) ^ 2 - 65536 * (16384 + 256)) < 3 ∧
    (65536 : ℝ) * ((affinePersistenceThreshold 16384 65536 256 (1 / 4) : ℝ) - 16384 - 256) /
      ((affinePersistenceThreshold 16384 65536 256 (1 / 4) : ℝ) ^ 2 - 65536 * (16384 + 256)) ≤
      4 / (1 / 4) := by
  refine ⟨?_, by exact_mod_cast rmParams.card_mul_sub_div_sq_sub_le⟩
  rw [rm_values.2.2.2.1]
  norm_num

-- The estimate `D ≤ 9 / (2 ρ η²) = 288`, here at `D = 96`.
example : affineYZBudget 16384 65536 (1 / 4) = 96 ∧
    (affineYZBudget 16384 65536 (1 / 4) : ℝ) ≤ 288 := by
  refine ⟨rm_values.2.1, ?_⟩
  have h := rmParams.yzBudget_le_nine_div
  norm_num at h
  exact_mod_cast h

-- The estimate `ρ n M ≤ 3 n / η = 786432` at `ρ n = 16384` and `M = 22`.
example : ((16384 * 22 : ℕ) : ℝ) ≤ 3 * 65536 / (1 / 4) := by
  have h := rmParams.mul_rootBudget_le
  rwa [rm_values.2.2.2.2] at h

-- The estimate `q₀ = n / e > 64`.
example : 64 * 256 < 65536 := rmParams.sixty_four_mul_lt

-- Every parameter tuple satisfying the hypotheses has `d + e < B < A ≤ n`.
example {d n e : ℕ} {η : ℝ} (h : AffineParams d n e η) :
    d + e < affinePersistenceThreshold d n e η ∧
      affinePersistenceThreshold d n e η < affineThreshold d n η ∧ affineThreshold d n η ≤ n :=
  ⟨h.add_lt_persistenceThreshold, h.persistenceThreshold_lt, h.threshold_le⟩

/-- info: 'ReedSolomon.sub_le_affinePersistenceThreshold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.sub_le_affinePersistenceThreshold

/-- info: 'ReedSolomon.AffineParams.four_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.four_mul_le

/-- info: 'ReedSolomon.AffineParams.sixty_four_mul_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.sixty_four_mul_lt

/-- info: 'ReedSolomon.AffineParams.ceil_add_mul_yzBudget_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.ceil_add_mul_yzBudget_le

/-- info: 'ReedSolomon.AffineParams.surplus' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.surplus

/-- info: 'ReedSolomon.AffineParams.mul_yzBudget_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.mul_yzBudget_le

/-- info: 'ReedSolomon.AffineParams.persistenceThreshold_add_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.persistenceThreshold_add_lt

/-- info: 'ReedSolomon.AffineParams.persistenceThreshold_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.persistenceThreshold_lt

/-- info: 'ReedSolomon.AffineParams.card_div_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.card_div_sub_le

/-- info: 'ReedSolomon.AffineParams.add_lt_persistenceThreshold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.add_lt_persistenceThreshold

/-- info: 'ReedSolomon.AffineParams.card_mul_add_lt_sq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.card_mul_add_lt_sq

/-- info: 'ReedSolomon.AffineParams.card_mul_sub_div_sq_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.card_mul_sub_div_sq_sub_le

/-- info: 'ReedSolomon.AffineParams.yzBudget_le_nine_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.yzBudget_le_nine_div

/-- info: 'ReedSolomon.AffineParams.mul_rootBudget_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.mul_rootBudget_le

/-- info: 'ReedSolomon.AffineParams.bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.AffineParams.bounds
