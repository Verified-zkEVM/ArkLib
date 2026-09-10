/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.LocalRank

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.RankBudget

/-!
# The weighted positive-part local rank count

For each contact residual, the first-derivative slot count depends on the remaining degree
of its higher-jet tuple. Rounding costs one per tuple. Keeping this dependence is what permits
the mean/variance bound on the enlarged simplex to replace the old uniform degree cap.
-/

@[expose] public section

open scoped BigOperators
namespace ReedSolomon.HiddenDerivative

/-- The integer residual slot count costs at most one above its positive part. -/
theorem ceil_residual_le (t : ℝ) : (⌈t⌉₊ : ℝ) ≤ max t 0 + 1 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
    exact (Nat.ceil_lt_add_one ht).le
  · rw [Nat.ceil_eq_zero.mpr (le_of_not_ge ht), Nat.cast_zero]
    positivity

/-- The local budget retains the weighted remaining-degree sum. -/
theorem localResidualCoordinateBudget_le_positivePart_sum (d m W : ℕ) (T : ℝ) :
    (localResidualCoordinateBudget d m W T : ℝ) ≤
      ∑ r ∈ Finset.range m, (((m-r) ⌈/⌉ (d+1) : ℕ) : ℝ) *
        ∑ z ∈ weightedHigherJetTuples d (W+r),
          (max (T - higherJetTupleDegree z) 0 + 1) := by
  unfold localResidualCoordinateBudget
  push_cast
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun z hz ↦ ceil_residual_le _

/-- The actual local rank is bounded by the positive-part sum over higher-jet tuples.
The next geometric step averages this same residual over enlarged simplex cubes. -/
theorem finrank_weightedSupportLocalConstraint_le_positivePart_sum
    {F : Type*} [Field F] {d D m W : ℕ} {L : ℝ}
    (hd : 0 < d) (hD : 0 < D) (center received : F) :
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) ≤
      ∑ r ∈ Finset.range m, (((m-r) ⌈/⌉ (d+1) : ℕ) : ℝ) *
        ∑ z ∈ weightedHigherJetTuples d (W+r),
          (max (L / D - higherJetTupleDegree z) 0 + 1) := by
  have h := finrank_weightedSupportLocalConstraint_le
    (d := d) (m := m) (W := W) (L := L) hd hD center received
  exact (show (Module.finrank F _ : ℝ) ≤
    (localResidualCoordinateBudget d m W (L / D) : ℝ) by exact_mod_cast h).trans
      (localResidualCoordinateBudget_le_positivePart_sum d m W (L / D))

/-- Sum the weighted fiber estimates with the exact contact-dependent geometric tail. -/
theorem localResidualCoordinateBudget_le_geometric (d m W : ℕ) (T B V x offset : ℝ)
    (hd : 0 < d) (hx : 0 < x) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hfiber : ∀ r ∈ Finset.range m,
      (∑ z ∈ weightedHigherJetTuples d (W + r), (max (T - higherJetTupleDegree z) 0 + 1)) ≤
        B * V * Real.exp (x * (r + offset))) :
    (localResidualCoordinateBudget d m W T : ℝ) ≤
      B * V * Real.exp (x * (m + offset)) * (1 / ((d:ℝ) * x ^ 2) + 1 / x) := by
  have h := localResidualCoordinateBudget_le_positivePart_sum d m W T
  have hs : (∑ r ∈ Finset.range m, (((m - r) ⌈/⌉ (d + 1) : ℕ) : ℝ) *
      ∑ z ∈ weightedHigherJetTuples d (W + r), (max (T - higherJetTupleDegree z) 0 + 1)) ≤
      B * V * ∑ r ∈ Finset.range m,
        (((m - r) ⌈/⌉ (d + 1) : ℕ) : ℝ) * Real.exp (x * (r + offset)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have ht := mul_le_mul_of_nonneg_left (hfiber r hr)
      (Nat.cast_nonneg ((m - r) ⌈/⌉ (d + 1)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using ht
  exact h.trans (hs.trans ((mul_le_mul_of_nonneg_left
    (localRank_contact_exp_sum_le d m hd (B := offset) hx) (mul_nonneg hB hV)).trans_eq
      (by ring)))

end ReedSolomon.HiddenDerivative
