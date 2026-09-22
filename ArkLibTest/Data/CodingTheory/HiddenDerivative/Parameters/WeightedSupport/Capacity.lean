/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity

/-!
# Acceptance cases for the weighted-support capacity parameters

* The two branches of `capacityDerivativeOrder`, including the boundary `δ = 1 / 4`, where the
  order is `0` and the lower bound `48000 ≤ d` fails; so `δ < 1 / 4` is needed in
  `capacityDerivativeOrder_lower`.
* Small values of `weightedSupportMultiplicity`: `0`, `0`, `400`, `1350` at `d = 0, 1, 2, 3`.
* Concrete ambient dimensions and the larger-field condition at its boundary.
* Unfolded forms of the definitions: the order with the literal `27 / 10`, the sum
  `∑ i ∈ range r, 1 / (i + 1)` as `harmonic r`, and the multiplicity as a function of `δ`.
-/

open ReedSolomon ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-! ### The derivative order -/

/-- At the boundary `δ = 1 / 4` the order is `0`. -/
example : capacityDerivativeOrder (1 / 4) = 0 := by simp

/-- Above the boundary the order is `0`. -/
example : capacityDerivativeOrder (1 / 2) = 0 := capacityDerivativeOrder_eq_zero (by norm_num)

/-- `capacityDerivativeOrder_lower` fails at `δ = 1 / 4`: the order is `0`, not `≥ 48000`. -/
example : ¬ 48000 ≤ capacityDerivativeOrder (1 / 4) := by simp

/-- At `δ = 1 / 8` the order is at least `48000`. -/
example : 48000 ≤ capacityDerivativeOrder (1 / 8) :=
  (capacityDerivativeOrder_lower (by norm_num) (by norm_num)).1

/-- The order written with the literal `27 / 10`. -/
example {δ : ℝ} (hδ : δ < 1 / 4) :
    capacityDerivativeOrder δ = Nat.ceil (Real.exp (((27 : ℝ) / 10) / δ)) := by
  rw [capacityDerivativeOrder_eq_ceil hδ, xi]

/-! ### The harmonic number -/

/-- `∑ i ∈ range r, 1 / (i + 1)` in `ℝ` is the real cast of Mathlib's `harmonic r`. -/
example (r : ℕ) : ∑ i ∈ Finset.range r, (1 : ℝ) / (i + 1) = (harmonic r : ℝ) := by
  simp [harmonic]

/-! ### The multiplicity -/

example : weightedSupportMultiplicity 0 = 0 := by simp [weightedSupportMultiplicity]

/-- At `d = 1` the harmonic factor `harmonic 0` vanishes. -/
example : weightedSupportMultiplicity 1 = 0 := by simp [weightedSupportMultiplicity]

/-- `2 ≤ d` is the exact positivity boundary. -/
example : ¬ 0 < weightedSupportMultiplicity 1 := by
  rw [weightedSupportMultiplicity_pos_iff]; decide

/-- `m = ⌈100 · 4 · 1⌉₊ = 400` at `d = 2`. -/
example : weightedSupportMultiplicity 2 = 400 := by
  have h : harmonic 1 = 1 := by simp [harmonic]
  rw [weightedSupportMultiplicity, show (2 - 1 : ℕ) = 1 from rfl, h]
  norm_num

/-- `m = ⌈100 · 9 · (3 / 2)⌉₊ = 1350` at `d = 3`. -/
example : weightedSupportMultiplicity 3 = 1350 := by
  have h : harmonic 2 = 3 / 2 := by norm_num [harmonic, Finset.sum_range_succ]
  rw [weightedSupportMultiplicity, show (3 - 1 : ℕ) = 2 from rfl, h]
  norm_num

/-- The multiplicity at the order `capacityDerivativeOrder δ`, with the harmonic sum written out. -/
example (δ : ℝ) :
    let d := capacityDerivativeOrder δ
    weightedSupportMultiplicity d =
      Nat.ceil (100 * (d : ℝ) ^ 2 * ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)) := by
  simp [weightedSupportMultiplicity, harmonic]

/-! ### Ambient dimension and the larger-field condition -/

private theorem floor_quarter_48 : ⌊(1 / 4 : ℝ) * (48 : ℕ) / 2⌋₊ = 6 := by norm_num
private theorem ceil_quarter_48 : ⌈(1 / 4 : ℝ) * (48 : ℕ)⌉₊ = 12 := by norm_num

/-- At `δ = 1 / 4`, `n = 48`: `K = max 10 6 = 10` for `k = 10`, and `K = 6` for `k = 3`. -/
example : weightedSupportAmbientDimension (1 / 4) 48 10 = 10 ∧
    weightedSupportAmbientDimension (1 / 4) 48 3 = 6 := by
  simp only [weightedSupportAmbientDimension, floor_quarter_48]
  decide

/-- At `δ = 1 / 4`, `n = 48`, `k = 10`, `d = 0`, `m = 1`: `A = 22`, `K = 10`, and the condition
is `2 (22 - 10) = 24 ≤ q`, which holds at `q = 24` and fails at `q = 23`. -/
example :
    LargeFieldCondition (1 / 4) 48 10 24 0 1 ∧ ¬ LargeFieldCondition (1 / 4) 48 10 23 0 1 := by
  simp only [LargeFieldCondition, weightedSupportAmbientDimension, floor_quarter_48,
    ceil_quarter_48]
  decide

/-- The truncated subtraction: with `m = 0` the condition holds for every `q`. -/
example (q : ℕ) : LargeFieldCondition (1 / 4) 48 10 q 0 0 := by
  simp only [LargeFieldCondition, weightedSupportAmbientDimension, floor_quarter_48]
  omega

/-! ### Block bounds -/

/-- The conclusions of `prescribedBlockBounds` used by the construction targets, stated with the
capacity definitions. -/
example {δ : ℝ} {n k : ℕ} (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock : 8 * weightedSupportMultiplicity (capacityDerivativeOrder δ) ≤ n)
    (hA : k + ⌈δ * n⌉₊ ≤ n) :
    capacityDerivativeOrder δ + 1 < weightedSupportAmbientDimension δ n k ∧
      weightedSupportAmbientDimension δ n k ≤ n := by
  obtain ⟨-, hd, -, hK⟩ := capacity_block_bounds hδ hδmax hblock hA
  exact ⟨by omega, hK⟩
