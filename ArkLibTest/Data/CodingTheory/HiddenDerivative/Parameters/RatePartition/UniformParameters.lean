/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformParameters

/-!
# Gap-only parameter acceptance tests

The lower bound `3 ≤ m`; cases showing that `δ ≤ 1`, `0 ≤ δ` and `δ ≤ 1/2` are needed in the
three guard theorems; the guards under the stronger size hypothesis `2m ≤ δ² n` with
`δ < 6/25`; and the high-rate guards at the gap-only parameters for block lengths above the
threshold.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The multiplicity is at least `3` for every gap. -/
example (δ : ℝ) : 3 ≤ uniformMultiplicity δ := by
  have h₁ := uniformDerivativeOrder_pos δ
  have h₂ := add_two_le_uniformMultiplicity δ
  omega

/-! ### Boundary hypotheses -/

/-- `uniformBlockThreshold_guards` needs `δ ≤ 1`: at `δ = 2` the threshold `⌈2m/4⌉₊` is below
`m`. -/
example : ¬ uniformMultiplicity 2 ≤ uniformBlockThreshold 2 := by
  have h₁ := uniformDerivativeOrder_pos 2
  have h₂ := add_two_le_uniformMultiplicity 2
  have hthreshold : uniformBlockThreshold 2 ≤ uniformMultiplicity 2 - 1 := by
    apply Nat.ceil_le.mpr
    have hm : (3 : ℝ) ≤ uniformMultiplicity 2 := by exact_mod_cast (by omega : 3 ≤ _)
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  omega

/-- `high_rate_ambient_guards` needs `0 ≤ δ`: at `δ = -1`, `d = 0`, `m = n = k = A = 2` the
hypotheses hold and `k + 1 ≤ n` fails. -/
example : (((2 : ℕ) : ℝ) ≤ (-1) ^ 2 * ((2 : ℕ) : ℝ) ∧ (-1) ^ 2 * ((2 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ) ∧
    ((2 : ℕ) : ℝ) + (-1) * ((2 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) ∧ ¬ (2 + 1 ≤ 2) := by
  norm_num

/-- `low_rate_padded_ambient_guards` needs `δ ≤ 1/2`: at `δ = 1`, `d = 0`, `m = n = 2` the size
hypothesis holds and `⌊2δ²n⌋₊ + 1 = 5 > n`. -/
example : ((2 : ℕ) : ℝ) ≤ 1 ^ 2 * ((2 : ℕ) : ℝ) ∧
    ¬ (⌊2 * (1 : ℝ) ^ 2 * ((2 : ℕ) : ℝ)⌋₊ + 1 ≤ 2) := by
  norm_num

/-! ### Guards under the stronger size hypothesis `2m ≤ δ² n` -/

/-- For `0 < δ < 1`, a positive multiplicity and a block length above the threshold: `2m ≤ δ² n`,
`m ≤ n` and `0 < ⌈m/δ²⌉₊ - 1 < n`. -/
example {δ : ℝ} {n : ℕ} (hδ : 0 < δ) (hδone : δ < 1) (_hm : 0 < uniformMultiplicity δ)
    (hn : uniformBlockThreshold δ ≤ n) :
    2 * (uniformMultiplicity δ : ℝ) ≤ δ ^ 2 * n ∧ uniformMultiplicity δ ≤ n ∧
      0 < uniformJetCap δ ∧ uniformJetCap δ < n :=
  uniformBlockThreshold_guards hδ hδone.le hn

/-- High-rate guards for `0 < δ < 1` from two multiplicity-sized units `2m ≤ δ² n`. -/
example {δ : ℝ} {d m n k A : ℕ} (hδ : 0 < δ) (_hδone : δ < 1) (hm : d + 2 ≤ m)
    (hsize : 2 * (m : ℝ) ≤ δ ^ 2 * n) (hhigh : δ ^ 2 * n ≤ k) (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n) :
    d + 1 ≤ k ∧ k + 1 ≤ n :=
  high_rate_ambient_guards hδ.le hm (by linarith [Nat.cast_nonneg (α := ℝ) m]) hhigh hgap hAn

/-- Low-rate padded guards for `0 < δ < 6/25` from two multiplicity-sized units `2m ≤ δ² n`. -/
example {δ : ℝ} {d m n : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25) (hm : d + 2 ≤ m)
    (hsize : 2 * (m : ℝ) ≤ δ ^ 2 * n) :
    d + 1 ≤ ⌊2 * δ ^ 2 * n⌋₊ ∧ δ ^ 2 * n ≤ ⌊2 * δ ^ 2 * n⌋₊ ∧ ⌊2 * δ ^ 2 * n⌋₊ + 1 ≤ n :=
  low_rate_padded_ambient_guards hδ.le (by linarith) hm
    (by linarith [Nat.cast_nonneg (α := ℝ) m])

/-! ### The gap-only parameters in the high-rate branch -/

/-- For `0 < δ ≤ 1`, a block length above the threshold and a high-rate message dimension
`δ² n ≤ k` with `k + δ n ≤ A ≤ n`, the derivative order `d` satisfies `d + 1 ≤ k`, and
`k + 1 ≤ n`. -/
example {δ : ℝ} {n k A : ℕ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : uniformBlockThreshold δ ≤ n)
    (hhigh : δ ^ 2 * n ≤ k) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    uniformDerivativeOrder δ + 1 ≤ k ∧ k + 1 ≤ n := by
  obtain ⟨hsize, -, -, -⟩ := uniformBlockThreshold_guards hδ hδone hn
  exact high_rate_ambient_guards hδ.le (add_two_le_uniformMultiplicity δ)
    (by linarith [Nat.cast_nonneg (α := ℝ) (uniformMultiplicity δ)]) hhigh hgap hAn

end ReedSolomon.HiddenDerivative.RatePartition
