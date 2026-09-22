/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity

/-!
# Integer parameters depending only on the gap

For a gap `δ` the rate-partition recipe can fix its integer parameters without looking at the
code rate: the derivative order `d = ⌈exp(3/(2δ))⌉₊`, the multiplicity
`m = closedMultiplicity 1000 d`, the block threshold `⌈2m/δ²⌉₊` and the total-jet cap
`⌈m/δ²⌉₊ - 1`. This file proves the integer guards these choices satisfy once the block length
`n` reaches the threshold, and the guards on the interpolation ambient degree in the high-rate
branch (ambient degree `k`) and the low-rate branch (ambient degree `⌊2δ²n⌋₊`), each from a
single multiplicity-sized unit `m ≤ δ² n` of room.

## Main definitions

* `uniformDerivativeOrder`, `uniformMultiplicity`, `uniformBlockThreshold`, `uniformJetCap`.

## Main statements

* `add_two_le_uniformMultiplicity`: `d + 2 ≤ m`.
* `uniformBlockThreshold_guards`: for `0 < δ ≤ 1` and `n` at least the threshold,
  `2m ≤ δ² n`, `m ≤ n` and `0 < ⌈m/δ²⌉₊ - 1 < n`.
* `high_rate_ambient_guards`: if `d + 2 ≤ m ≤ δ² n ≤ k` and `k + δ n ≤ A ≤ n`, then
  `d + 1 ≤ k` and `k + 1 ≤ n`.
* `low_rate_padded_ambient_guards`: if `0 ≤ δ ≤ 1/2` and `d + 2 ≤ m ≤ δ² n`, then
  `D = ⌊2δ²n⌋₊` satisfies `d + 1 ≤ D`, `δ² n ≤ D` and `D + 1 ≤ n`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The derivative order `⌈exp(3/(2δ))⌉₊` attached to the gap `δ`. -/
def uniformDerivativeOrder (δ : ℝ) : ℕ := ⌈Real.exp ((3 / 2) / δ)⌉₊

/-- The multiplicity `⌈1000 d² log(6d)⌉₊` at the derivative order `uniformDerivativeOrder δ`. -/
def uniformMultiplicity (δ : ℝ) : ℕ := closedMultiplicity 1000 (uniformDerivativeOrder δ)

/-- The block-length threshold `⌈2m/δ²⌉₊` at the multiplicity `uniformMultiplicity δ`. -/
def uniformBlockThreshold (δ : ℝ) : ℕ := ⌈2 * (uniformMultiplicity δ : ℝ) / δ ^ 2⌉₊

/-- The total-jet cap `⌈m/δ²⌉₊ - 1` at the multiplicity `uniformMultiplicity δ`. -/
def uniformJetCap (δ : ℝ) : ℕ := ⌈(uniformMultiplicity δ : ℝ) / δ ^ 2⌉₊ - 1

/-- The derivative order `⌈exp(3/(2δ))⌉₊` is positive. -/
theorem uniformDerivativeOrder_pos (δ : ℝ) : 0 < uniformDerivativeOrder δ :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

/-- The multiplicity exceeds the derivative order by at least two. -/
theorem add_two_le_uniformMultiplicity (δ : ℝ) :
    uniformDerivativeOrder δ + 2 ≤ uniformMultiplicity δ :=
  add_two_le_closedMultiplicity (by norm_num) (uniformDerivativeOrder_pos δ)

/-- For `0 < δ ≤ 1` and a block length `n` at least `uniformBlockThreshold δ`, the multiplicity
`m` satisfies `2m ≤ δ² n` and `m ≤ n`, and the total-jet cap lies strictly between `0` and `n`. -/
theorem uniformBlockThreshold_guards {δ : ℝ} {n : ℕ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hn : uniformBlockThreshold δ ≤ n) :
    2 * (uniformMultiplicity δ : ℝ) ≤ δ ^ 2 * n ∧ uniformMultiplicity δ ≤ n ∧
      0 < uniformJetCap δ ∧ uniformJetCap δ < n := by
  set m := uniformMultiplicity δ
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hδ2one : δ ^ 2 ≤ 1 := by nlinarith
  have hmTwo : (2 : ℝ) ≤ m := by
    have := add_two_le_uniformMultiplicity δ
    exact_mod_cast (show 2 ≤ m by omega)
  have hbound : 2 * (m : ℝ) / δ ^ 2 ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hsize : 2 * (m : ℝ) ≤ δ ^ 2 * n := by
    rw [div_le_iff₀ hδ2] at hbound
    linarith
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hcap : 1 < ⌈(m : ℝ) / δ ^ 2⌉₊ := by
    apply Nat.lt_ceil.mpr
    rw [Nat.cast_one, lt_div_iff₀ hδ2]
    linarith
  have hcapn : ⌈(m : ℝ) / δ ^ 2⌉₊ ≤ n := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hδ2]
    linarith
  refine ⟨hsize, hmn, ?_, ?_⟩
  · change 0 < ⌈(m : ℝ) / δ ^ 2⌉₊ - 1
    omega
  · change ⌈(m : ℝ) / δ ^ 2⌉₊ - 1 < n
    omega

/-- High-rate ambient guards: if `d + 2 ≤ m ≤ δ² n ≤ k` and `k + δ n ≤ A ≤ n` with `0 ≤ δ`, then
the ambient degree `k` satisfies `d + 1 ≤ k` and `k + 1 ≤ n`. -/
theorem high_rate_ambient_guards {δ : ℝ} {d m n k A : ℕ} (hδ : 0 ≤ δ) (hm : d + 2 ≤ m)
    (hsize : (m : ℝ) ≤ δ ^ 2 * n) (hhigh : δ ^ 2 * n ≤ k) (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n) :
    d + 1 ≤ k ∧ k + 1 ≤ n := by
  have hm' : (d : ℝ) + 2 ≤ m := by exact_mod_cast hm
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
  constructor
  · have : (d : ℝ) + 1 ≤ k := by linarith
    exact_mod_cast this
  · have : (k : ℝ) + 1 ≤ n := by
      rcases le_or_gt δ 1 with hδone | hδone
      · have hδ2 : δ ^ 2 * n ≤ δ * n :=
          mul_le_mul_of_nonneg_right (by nlinarith) hn'
        linarith
      · have : (n : ℝ) ≤ δ * n := le_mul_of_one_le_left hn' hδone.le
        linarith
    exact_mod_cast this

/-- Low-rate padded ambient guards: if `0 ≤ δ ≤ 1/2` and `d + 2 ≤ m ≤ δ² n`, then the padded
ambient degree `D = ⌊2δ²n⌋₊` satisfies `d + 1 ≤ D`, `δ² n ≤ D` and `D + 1 ≤ n`. -/
theorem low_rate_padded_ambient_guards {δ : ℝ} {d m n : ℕ} (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hm : d + 2 ≤ m) (hsize : (m : ℝ) ≤ δ ^ 2 * n) :
    d + 1 ≤ ⌊2 * δ ^ 2 * n⌋₊ ∧ δ ^ 2 * n ≤ ⌊2 * δ ^ 2 * n⌋₊ ∧ ⌊2 * δ ^ 2 * n⌋₊ + 1 ≤ n := by
  have hm' : (d : ℝ) + 2 ≤ m := by exact_mod_cast hm
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hfloor : (⌊2 * δ ^ 2 * n⌋₊ : ℝ) ≤ 2 * δ ^ 2 * n := Nat.floor_le (by positivity)
  have hfloor' : 2 * δ ^ 2 * n < (⌊2 * δ ^ 2 * n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hquarter : δ ^ 2 * n ≤ n / 4 := by nlinarith
  refine ⟨?_, by linarith, ?_⟩
  · have : (d : ℝ) + 1 ≤ ⌊2 * δ ^ 2 * n⌋₊ := by linarith
    exact_mod_cast this
  · have : (⌊2 * δ ^ 2 * n⌋₊ : ℝ) + 1 ≤ n := by linarith
    exact_mod_cast this

end ReedSolomon.HiddenDerivative.RatePartition
