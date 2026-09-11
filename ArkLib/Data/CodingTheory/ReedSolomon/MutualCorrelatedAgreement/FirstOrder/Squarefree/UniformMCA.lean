/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.Uniform
/-!
# The height-276 first-order MCA certificate

The line-MCA support uses `(m, M, μ) = (12, 4, 23)`, separately from the
list support `(12, 4, 22)`.  The last shell has local rank zero but supplies
the challenge-height margin needed at height `276`.

The source has truncated degree blocks.  We retain exactly the active prefix
on each of the nine rate intervals cut out by `25 s k = 72 n`, for
`s = 4, ..., 11`.  Prefix accounting avoids replacing those truncated blocks
by a weaker global affine estimate.
-/

@[expose] public section

namespace ReedSolomon

open HiddenDerivative
open scoped BigOperators

set_option maxRecDepth 4096

/-- Height weight of the first `q` total-degree shells. -/
private def uniformFirstOrderMCAHeightWeightUpTo (q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range q, (min t 4 + 1) * (277 - t)

/-- Total-degree height weight of the first `q` shells. -/
private def uniformFirstOrderMCAHeightDegreeWeightUpTo (q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range q, (min t 4 + 1) * t * (277 - t)

/-- First-jet height weight of the first `q` shells. -/
private def uniformFirstOrderMCAHeightFirstJetWeightUpTo (q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range q,
    ∑ b ∈ Finset.range (min t 4 + 1), b * (277 - t)

private theorem uniformFirstOrderMCAHeightWeightUpTo_eq_nested (q : ℕ) :
    uniformFirstOrderMCAHeightWeightUpTo q =
      ∑ t ∈ Finset.range q,
        Finset.sum (Finset.range (min t 4 + 1)) (fun _ ↦ 277 - t) := by
  simp [uniformFirstOrderMCAHeightWeightUpTo, Finset.sum_const]

private theorem uniformFirstOrderMCAHeightDegreeWeightUpTo_eq_nested (q : ℕ) :
    uniformFirstOrderMCAHeightDegreeWeightUpTo q =
      ∑ t ∈ Finset.range q,
        Finset.sum (Finset.range (min t 4 + 1)) (fun _ ↦ t * (277 - t)) := by
  simp [uniformFirstOrderMCAHeightDegreeWeightUpTo, Finset.sum_const, Nat.mul_assoc]

/-- Prefix accounting for the truncated shifted source. -/
private theorem uniformFirstOrderMCA_shiftedHeightSlot_accounting
    (D A q : ℕ) :
    12 * A * uniformFirstOrderMCAHeightWeightUpTo q +
        uniformFirstOrderMCAHeightFirstJetWeightUpTo q ≤
      (∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
        (12 * A + b - D * t) * (277 - t)) +
        D * uniformFirstOrderMCAHeightDegreeWeightUpTo q := by
  have hleft :
      12 * A * uniformFirstOrderMCAHeightWeightUpTo q +
          uniformFirstOrderMCAHeightFirstJetWeightUpTo q =
        ∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
          (12 * A + b) * (277 - t) := by
    rw [uniformFirstOrderMCAHeightWeightUpTo_eq_nested]
    simp only [uniformFirstOrderMCAHeightFirstJetWeightUpTo, Nat.add_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hright :
      (∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
          (12 * A + b - D * t) * (277 - t)) +
          D * uniformFirstOrderMCAHeightDegreeWeightUpTo q =
        ∑ t ∈ Finset.range q, ∑ b ∈ Finset.range (min t 4 + 1),
          ((12 * A + b - D * t) * (277 - t) + D * t * (277 - t)) := by
    rw [uniformFirstOrderMCAHeightDegreeWeightUpTo_eq_nested]
    simp only [Nat.mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro b hb
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

set_option maxHeartbeats 10000000 in
-- The nine exact interval branches require more than the default heartbeat budget.
/-- The support `(12, 4, 23)` has a strict shifted source surplus at height
`276` throughout the gap-`6/25` regime. -/
theorem uniformFirstOrderMCA_heightSlotCount (n k A : ℕ)
    (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : 25 * k + 6 * n ≤ 25 * A) :
    let D := max (k - 1) 2
    firstOrderCurveShiftedRowSlotBound D A 12 4 23 n 1 276 <
      firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
  dsimp only
  let D := max (k - 1) 2
  have hrow := firstOrderCurveShiftedRowSlotBound_le_of_rankBound
    D A 12 4 23 n 1 276 uniformFirstOrderGradedRankProfile
      (firstOrderGradedRankBound_le_uniformFirstOrderProfile D A)
  have hrow' :
      firstOrderCurveShiftedRowSlotBound D A 12 4 23 n 1 276 ≤ n * 81530 := by
    calc
      _ ≤ ∑ t ∈ Finset.range (23 + 1),
          n * uniformFirstOrderGradedRankProfile t * (276 + 1 - t) := hrow
      _ = n * 81530 := by
        norm_num [Finset.sum_range_succ, uniformFirstOrderGradedRankProfile]
        ring
  let sourceTerm := fun t ↦
    ∑ b ∈ Finset.range (min t 4 + 1),
      (12 * A + b - D * t) * (276 + 1 - t)
  have hpartial (q : ℕ) (hq : q ≤ 24) :
      (∑ t ∈ Finset.range q, sourceTerm t) ≤
        firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
    unfold firstOrderCurveShiftedHeightSlotCount
    simpa only [sourceTerm, Nat.one_mul, show 23 + 1 = 24 by norm_num] using
      (Finset.sum_le_sum_of_subset
        (Finset.range_mono hq) :
          (∑ t ∈ Finset.range q, sourceTerm t) ≤
            ∑ t ∈ Finset.range 24, sourceTerm t)
  apply hrow'.trans_lt
  by_cases h11 : 275 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 24 le_rfl)
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 24
    have hw : uniformFirstOrderMCAHeightWeightUpTo 24 = 29100 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 24 = 357890 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 24 = 55445 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h10 : 250 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 23 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 23
    have hw : uniformFirstOrderMCAHeightWeightUpTo 23 = 27830 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 23 = 328680 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 23 = 52905 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h9 : 225 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 22 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 22
    have hw : uniformFirstOrderMCAHeightWeightUpTo 22 = 26555 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 22 = 300630 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 22 = 50355 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h8 : 200 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 21 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 21
    have hw : uniformFirstOrderMCAHeightWeightUpTo 21 = 25275 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 21 = 273750 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 21 = 47795 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h7 : 175 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 20 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 20
    have hw : uniformFirstOrderMCAHeightWeightUpTo 20 = 23990 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 20 = 248050 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 20 = 45225 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h6 : 150 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 19 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 19
    have hw : uniformFirstOrderMCAHeightWeightUpTo 19 = 22700 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 19 = 223540 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 19 = 42645 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h5 : 125 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 18 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 18
    have hw : uniformFirstOrderMCAHeightWeightUpTo 18 = 21405 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 18 = 200230 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 18 = 40055 := by decide
    rw [hw, ht, hj] at haccount
    omega
  by_cases h4 : 100 * k ≤ 72 * n
  · apply lt_of_lt_of_le ?_ (hpartial 17 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 17
    have hw : uniformFirstOrderMCAHeightWeightUpTo 17 = 20105 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 17 = 178130 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 17 = 37455 := by decide
    rw [hw, ht, hj] at haccount
    omega
  · apply lt_of_lt_of_le ?_ (hpartial 16 (by omega))
    dsimp only [sourceTerm]
    norm_num only [Nat.reduceAdd]
    have haccount := uniformFirstOrderMCA_shiftedHeightSlot_accounting D A 16
    have hw : uniformFirstOrderMCAHeightWeightUpTo 16 = 18800 := by decide
    have ht : uniformFirstOrderMCAHeightDegreeWeightUpTo 16 = 157250 := by decide
    have hj : uniformFirstOrderMCAHeightFirstJetWeightUpTo 16 = 34845 := by decide
    rw [hw, ht, hj] at haccount
    omega

/-- The height-276 support supplies precisely the ambient-degree, positive-budget,
message-degree, and shifted-slot hypotheses used by the semantic curve constructor. -/
theorem uniformFirstOrderMCA_parameters (n k A : ℕ)
    (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : 25 * k + 6 * n ≤ 25 * A) :
    let D := max (k - 1) 2
    1 < D ∧ 0 < 12 * A ∧ k ≤ D + 1 ∧
      firstOrderCurveShiftedRowSlotBound D A 12 4 23 n 1 276 <
        firstOrderCurveShiftedHeightSlotCount D A 12 4 23 1 276 := by
  dsimp only
  refine ⟨by omega, by omega, by omega, ?_⟩
  exact uniformFirstOrderMCA_heightSlotCount n k A hk hAn hgap

end ReedSolomon
