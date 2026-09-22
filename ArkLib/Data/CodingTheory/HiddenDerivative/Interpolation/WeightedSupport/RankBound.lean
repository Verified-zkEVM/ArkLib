/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RankBudget
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
public import ArkLib.ToMathlib.Algebra.Order.Floor.Ratio

/-!
# The weighted positive-part local rank count

The rank of the local constraint map on the weighted support space is at most the residual budget
`localResidualCoordinateBudget d m W ⌈T⌉₊` with `T = L / D`
(`finrank_weightedSupportLocalConstraint_le`). For each contact residual `r < m` the budget counts
`⌈T⌉₊ - ∑ i, z i` first-derivative degrees for every higher-jet exponent `z` of weight at most
`W + r`. This file bounds that natural count by the real positive part
`max (T - ∑ i, z i) 0 + 1`: the ceiling costs at most one per exponent. Keeping the dependence on
the remaining degree `T - ∑ i, z i`, instead of bounding every count by `⌈T⌉₊`, is what lets the
mean and variance of `∑ i, z i` on the enlarged simplex control the sum.

Given any bound `B V exp (x (r + offset))` for the inner sum of residual `r`, the contact sum of
`Local/RankBudget.lean` then bounds the whole budget by
`B V exp (x (m + offset)) (1 / (d x ^ 2) + 1 / x)`.

## Main statements

* `localResidualCoordinateBudget_le_positivePart_sum` and its specialization to the actual map,
  `finrank_weightedSupportLocalConstraint_le_positivePart_sum`.
* `localResidualCoordinateBudget_le_geometric`: the geometric sum over contact residuals.
-/

@[expose] public section

open Finset

namespace ReedSolomon.HiddenDerivative

/-- The residual budget with the natural cutoff `⌈T⌉₊` is at most the real positive-part sum:
`localResidualCoordinateBudget d m W ⌈T⌉₊ ≤
  ∑_{r<m} ⌈(m - r) / (d + 1)⌉ ∑_z (max (T - ∑ i, z i) 0 + 1)`, the inner sum over the higher-jet
exponents `z` of weight at most `W + r`. Each natural count `⌈T⌉₊ - ∑ i, z i` exceeds the
positive part by at most one. No hypothesis is needed. -/
theorem localResidualCoordinateBudget_le_positivePart_sum (d m W : ℕ) (T : ℝ) :
    (localResidualCoordinateBudget d m W ⌈T⌉₊ : ℝ) ≤
      ∑ r ∈ range m, (contactThreshold (d + 1) m r : ℝ) *
        ∑ z ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r),
          (max (T - ((∑ i, z i : ℕ) : ℝ)) 0 + 1) := by
  rw [localResidualCoordinateBudget, Nat.cast_sum]
  refine sum_le_sum fun r _ => ?_
  rw [Nat.cast_mul, Nat.cast_sum]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => ?_) (Nat.cast_nonneg _)
  exact Nat.cast_ceil_sub_le_max_sub_add_one T _

/-- For `0 < d` and `0 < D`, the rank of the local constraint map on the weighted support space
`weightedSupportSpace F D d W L hD` is at most the positive-part sum of
`localResidualCoordinateBudget_le_positivePart_sum` at `T = L / D`. The hypotheses are those of
`finrank_weightedSupportLocalConstraint_le`. -/
theorem finrank_weightedSupportLocalConstraint_le_positivePart_sum
    {F : Type*} [Field F] {d D m W : ℕ} {L : ℝ}
    (hd : 0 < d) (hD : 0 < D) (center received : F) :
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) ≤
      ∑ r ∈ range m, (contactThreshold (d + 1) m r : ℝ) *
        ∑ z ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r),
          (max (L / D - ((∑ i, z i : ℕ) : ℝ)) 0 + 1) := by
  have h := finrank_weightedSupportLocalConstraint_le
    (d := d) (m := m) (W := W) (L := L) hd hD center received
  exact (show (Module.finrank F _ : ℝ) ≤
    (localResidualCoordinateBudget d m W ⌈L / D⌉₊ : ℝ) by exact_mod_cast h).trans
      (localResidualCoordinateBudget_le_positivePart_sum d m W (L / D))

/-- If the inner positive-part sum of every contact residual `r < m` is at most
`B V exp (x (r + offset))`, then
`localResidualCoordinateBudget d m W ⌈T⌉₊ ≤ B V exp (x (m + offset)) (1 / (d x ^ 2) + 1 / x)`.
The contact weights `⌈(m - r) / (d + 1)⌉` are summed against the exponentials by
`sum_contactThreshold_mul_exp_le`, which needs `0 < d` and `0 < x`; the hypothesis
`0 ≤ B V` keeps the fiber bounds in the right direction after multiplying by the contact
weights. -/
theorem localResidualCoordinateBudget_le_geometric (d m W : ℕ) (T B V x offset : ℝ)
    (hd : 0 < d) (hx : 0 < x) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hfiber : ∀ r ∈ range m,
      ∑ z ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r),
          (max (T - ((∑ i, z i : ℕ) : ℝ)) 0 + 1) ≤
        B * V * Real.exp (x * (r + offset))) :
    (localResidualCoordinateBudget d m W ⌈T⌉₊ : ℝ) ≤
      B * V * Real.exp (x * (m + offset)) * (1 / ((d : ℝ) * x ^ 2) + 1 / x) := by
  refine (localResidualCoordinateBudget_le_positivePart_sum d m W T).trans ?_
  have hs : (∑ r ∈ range m, (contactThreshold (d + 1) m r : ℝ) *
      ∑ z ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r),
        (max (T - ((∑ i, z i : ℕ) : ℝ)) 0 + 1)) ≤
      B * V * ∑ r ∈ range m, (contactThreshold (d + 1) m r : ℝ) *
        Real.exp (x * (r + offset)) := by
    rw [mul_sum]
    refine sum_le_sum fun r hr => ?_
    have ht := mul_le_mul_of_nonneg_left (hfiber r hr)
      (Nat.cast_nonneg (contactThreshold (d + 1) m r))
    calc _ ≤ _ := ht
      _ = _ := by ring
  refine hs.trans ((mul_le_mul_of_nonneg_left
    (sum_contactThreshold_mul_exp_le d m hd (B := offset) hx) (mul_nonneg hB hV)).trans_eq ?_)
  ring

end ReedSolomon.HiddenDerivative
