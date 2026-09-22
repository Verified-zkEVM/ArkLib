/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block

/-!
# Acceptance cases for the weighted-support block parameters

A concrete instance of `blockDegree_bounds` and of the cutoff bound; the cases showing that
`12 ≤ δ n` and `δ ≤ 2 / 3` are needed in `blockDegree_bounds`; and
`prescribedBlockBounds` written with `min 1 (δ / (D / n))`, `δ < 1 / 4` and `0 < k`, derived from
the general statement.
-/

open ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-! ### Concrete instances -/

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

/-! ### The hypotheses of `blockDegree_bounds` are needed -/

/-- `12 ≤ δ n` is needed for `δ / 3 ≤ D / n`. At `δ = 99 / 400`, `n = 40`, `k = 1` all other
hypotheses hold (`δ ≤ 2 / 3`, `1 + ⌈9.9⌉₊ = 11 ≤ 40`), but `δ n = 9.9`, `K = ⌊4.95⌋₊ = 4`,
`D = 3`, and `D / n = 3 / 40 < 33 / 400 = δ / 3`. -/
example : ¬ ((99 / 400 : ℝ) / 3 ≤
    ((max 1 ⌊(99 / 400 : ℝ) * (40 : ℕ) / 2⌋₊ - 1 : ℕ) : ℝ) / (40 : ℕ)) := by
  have hf : ⌊(99 / 400 : ℝ) * (40 : ℕ) / 2⌋₊ = 4 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [hf]
  norm_num

/-- `δ ≤ 2 / 3` is needed for `D / n ≤ 1 - δ`. At `δ = 9 / 10`, `n = 100`, `k = 10` the other
hypotheses hold (`δ n = 90 ≥ 12`, `10 + 90 ≤ 100`), but `K = 45`, `D = 44`, and
`D / n = 11 / 25 > 1 / 10 = 1 - δ`. -/
example : ¬ (((max 10 ⌊(9 / 10 : ℝ) * (100 : ℕ) / 2⌋₊ - 1 : ℕ) : ℝ) / (100 : ℕ) ≤
    1 - 9 / 10) := by
  have hf : ⌊(9 / 10 : ℝ) * (100 : ℕ) / 2⌋₊ = 45 := by norm_num
  rw [hf]
  norm_num

/-! ### Specialization with `min 1 (δ / (D / n))` -/

/-- `prescribedBlockBounds` with `δ < 1 / 4`, an unused hypothesis `0 < k`, and the gap written
as `min 1 (δ / (D / n))`. -/
example (δ : ℝ) (n k : ℕ)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4) (_hk : 0 < k)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hA : k + Nat.ceil (δ * n) ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let K := max k (Nat.floor (δ * n / 2))
    let D := K - 1
    let A := k + Nat.ceil (δ * n)
    let g := min 1 (δ / ((D : ℝ) / n))
    0 < n ∧ 0 < D ∧ d < D ∧
      δ / 3 ≤ (D : ℝ) / n ∧ (D : ℝ) / n ≤ 1 - δ ∧
      K ≤ n ∧ (D : ℝ) * (1 + g) ≤ A :=
  prescribedBlockBounds δ n k hδ hδmax.le hblock hA
