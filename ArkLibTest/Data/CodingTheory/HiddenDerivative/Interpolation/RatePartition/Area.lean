/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.RatePartition.Area

/-!
# Acceptance tests for the quadratic bounds at a real cutoff

The source form of `ratePartition_dimension_ge_quadratic_sum`, a concrete instance at the cutoff
`5 / 2` where the real bound exceeds the natural bound at `⌊5 / 2⌋`, and a failure of the rate
form when `level * n ≤ L` is dropped.
-/

open Finset PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Source shape `ratePartition_dimension_ge_quadratic_sum`, stated for the number of eligible
exponents at a real cutoff. -/
example {D d W : ℕ} {L : ℝ} (hD : 0 < D) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max (L / D - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (#(partitionSupportExponents D d W L hD) : ℝ) := by
  rw [← finrank_partitionSupportSpace_eq_card (F := ℚ)]
  exact partitionSupport_dimension_ge_quadratic_sum_real ℚ hD L

/-- With no visible jets the only tuple is empty. -/
private theorem natWeightedSimplex_fin_zero (W : ℕ) :
    natWeightedSimplex (fun i : Fin 0 => i.val + 1) W = {0} := by
  ext c
  simp [mem_natWeightedSimplex, Subsingleton.elim c 0]

/-- At `D = 1`, `d = 0`, `W = 0` and the cutoff `5 / 2`, the bound is `(5 / 2) ^ 2 / 2 = 25 / 8`.
The natural-cutoff bound at `⌊5 / 2⌋ = 2` gives only `2`. The dimension itself is `3 + 2 + 1`. -/
example : (25 / 8 : ℝ) ≤ Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (5 / 2 : ℝ) one_pos) ∧
    Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (5 / 2 : ℝ) one_pos) = 6 := by
  constructor
  · have h := partitionSupport_dimension_ge_quadratic_sum_real ℚ (d := 0) (W := 0) one_pos
      (5 / 2 : ℝ)
    rw [natWeightedSimplex_fin_zero, sum_singleton] at h
    norm_num at h
    exact h
  · rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
      show ⌈(5 / 2 : ℝ)⌉₊ = 3 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num]
    decide

/-- The rate form needs `level * n ≤ L`: at `D = n = rate = 1`, `d = W = 0`, the level `10` and
the cutoff `1 / 2`, the left side is `1 / 2 * 10 ^ 2 = 50`, while the space contains only the
constant monomial. -/
example : (Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (1 / 2 : ℝ) one_pos) : ℝ) <
    ((1 : ℕ) : ℝ) / (2 * 1) * ∑ c ∈ natWeightedSimplex (fun i : Fin 0 => i.val + 1) 0,
      (max ((10 : ℝ) - 1 * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
    show ⌈(1 / 2 : ℝ)⌉₊ = 1 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num,
    natWeightedSimplex_fin_zero, sum_singleton,
    show partitionSourceCount 1 0 0 1 = 1 by decide]
  norm_num
