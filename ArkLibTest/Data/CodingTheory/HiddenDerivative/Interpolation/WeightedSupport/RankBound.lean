/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankBound
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Acceptance cases for the weighted positive-part rank count

Both sides of the positive-part bound at `d = 1`, `m = 2`, `W = 0`, `T = 21 / 10`, where the
ceiling costs `1 / 10` per exponent; the geometric bound at the same parameters; and
`finrank_weightedSupportLocalConstraint_le_positivePart_sum` with the contact ceiling written
`(m - r) ⌈/⌉ (d + 1)`.
-/

open Finset ReedSolomon.HiddenDerivative

/-- For `d = 1` there are no higher jets, so the only exponent is the empty one. -/
private theorem natWeightedSimplex_fin_zero (W : ℕ) :
    natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) W = {fun _ => 0} := by
  ext c
  have hc : c = fun _ => 0 := funext fun i => Fin.elim0 i
  subst hc
  simp only [mem_singleton, iff_true]
  exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => Fin.elim0 i, by simp⟩

private theorem ceil_twentyOne_div_ten : ⌈(21 / 10 : ℝ)⌉₊ = 3 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- `d = 1`, `m = 2`, `W = 0`, `T = 21 / 10`: the budget is `2 · 1 · ⌈21 / 10⌉₊ = 6`, and the
positive-part sum is `2 · (21 / 10 + 1) = 31 / 5`. -/
example : (localResidualCoordinateBudget 1 2 0 ⌈(21 / 10 : ℝ)⌉₊ : ℝ) = 6 ∧
    ∑ r ∈ range 2, (contactThreshold (1 + 1) 2 r : ℝ) *
        ∑ z ∈ natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) (0 + r),
          (max ((21 / 10 : ℝ) - ((∑ i, z i : ℕ) : ℝ)) 0 + 1) = 31 / 5 ∧
    (6 : ℝ) ≤ 31 / 5 := by
  have hb : localResidualCoordinateBudget 1 2 0 3 = 6 := by decide
  have h := localResidualCoordinateBudget_le_positivePart_sum 1 2 0 (21 / 10)
  have hc0 : contactThreshold 2 2 0 = 1 := by decide
  have hc1 : contactThreshold 2 2 1 = 1 := by decide
  simp only [ceil_twentyOne_div_ten, hb, natWeightedSimplex_fin_zero, sum_range_succ,
    range_zero, sum_empty, sum_singleton, Nat.reduceAdd, hc0, hc1] at h ⊢
  norm_num at h ⊢

/-- The geometric bound at the same parameters with `B = 31 / 10`, `V = 1`, `x = 1` and offset
`0`: every inner sum is `31 / 10 ≤ 31 / 10 · exp r`, so the budget `6` is at most
`31 / 10 · exp 2 · (1 + 1)`. -/
example : (6 : ℝ) ≤ 31 / 10 * Real.exp 2 * 2 := by
  have hb : localResidualCoordinateBudget 1 2 0 3 = 6 := by decide
  have h := localResidualCoordinateBudget_le_geometric 1 2 0 (21 / 10) (31 / 10) 1 1 0
    one_pos one_pos (by norm_num) zero_le_one fun r _ => by
      rw [natWeightedSimplex_fin_zero, sum_singleton]
      have : (1 : ℝ) ≤ Real.exp (1 * (r + 0)) := Real.one_le_exp (by positivity)
      norm_num at this ⊢
  rw [ceil_twentyOne_div_ten, hb] at h
  norm_num at h
  exact h

/-- `finrank_weightedSupportLocalConstraint_le_positivePart_sum`, with the contact
ceiling `(m - r) ⌈/⌉ (d + 1)` written out. -/
example {F : Type*} [Field F] {d D m W : ℕ} {L : ℝ} (hd : 0 < d) (hD : 0 < D)
    (center received : F) :
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) ≤
      ∑ r ∈ range m, (((m - r) ⌈/⌉ (d + 1) : ℕ) : ℝ) *
        ∑ z ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r),
          (max (L / D - ((∑ i, z i : ℕ) : ℝ)) 0 + 1) :=
  finrank_weightedSupportLocalConstraint_le_positivePart_sum hd hD center received
