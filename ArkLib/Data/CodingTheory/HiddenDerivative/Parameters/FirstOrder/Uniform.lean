/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting

/-!
# Uniform first-order shifted-height parameters

For the fixed support `(m, M, μ) = (12, 4, 22)` and challenge height `851`, the exact
unrestricted graded-rank profile bounds the numerical row slots. Its finite sums yield a
strict shifted source-slot surplus when `2 ≤ k` and `25 * k + 6 * n ≤ 25 * A`.

## Main statements

* `uniformFirstOrderGradedRankProfile_values`: the exact finite graded-rank profile.
* `uniformFirstOrder_parameters`: the positive ambient and shifted-slot bounds in the
  gap-`6/25` regime.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

set_option maxRecDepth 4096

/-- The exact unrestricted block-rank profile for `(m, M) = (12, 4)`. -/
def uniformFirstOrderGradedRankProfile (t : ℕ) : ℕ :=
  Finset.sum (Finset.range 12) fun s ↦
    min (12 - s) (min t s + 1 - (t - 4))

/-- The fixed profile bounds every first-order graded-rank bound with `(m, M) = (12, 4)`. -/
theorem firstOrderGradedRankBound_le_uniformFirstOrderProfile (D A t : ℕ) :
    firstOrderGradedRankBound D A 12 4 t ≤ uniformFirstOrderGradedRankProfile t := by
  apply Finset.sum_le_sum
  intro s hs
  apply min_le_min le_rfl
  simp only [firstOrderGradedSourceCount]
  split <;> omega

/-- Total coefficient-height multiplicity of the fixed shifted source. -/
def uniformFirstOrderHeightWeightSum : ℕ :=
  Finset.sum (Finset.range 23) fun t ↦
    Finset.sum (Finset.range (min t 4 + 1)) fun _ ↦ 852 - t

/-- Total jet grade, weighted by the remaining coefficient-height slots. -/
def uniformFirstOrderHeightTotalDegreeSum : ℕ :=
  Finset.sum (Finset.range 23) fun t ↦
    Finset.sum (Finset.range (min t 4 + 1)) fun _ ↦ t * (852 - t)

/-- Total first-jet exponent contribution in the fixed shifted source. -/
def uniformFirstOrderHeightFirstJetSum : ℕ :=
  Finset.sum (Finset.range 23) fun t ↦
    Finset.sum (Finset.range (min t 4 + 1)) fun b ↦ b * (852 - t)

/-- Total compressed-row slots per evaluation point for the exact rank profile. -/
def uniformFirstOrderRowWeightSum : ℕ :=
  Finset.sum (Finset.range 23) fun t ↦
    uniformFirstOrderGradedRankProfile t * (852 - t)

/-- The fixed graded-rank profile has the displayed values through grade `22`. -/
theorem uniformFirstOrderGradedRankProfile_values :
    List.ofFn (fun t : Fin 23 ↦ uniformFirstOrderGradedRankProfile t) =
      [12, 22, 30, 36, 40, 35, 30, 25, 20, 16, 12, 9, 6, 4, 2, 1,
        0, 0, 0, 0, 0, 0, 0] := by decide

/-- The fixed graded-rank profile sums to `300` through grade `22`. -/
theorem uniformFirstOrderGradedRankProfile_sum :
    Finset.sum (Finset.range 23) uniformFirstOrderGradedRankProfile = 300 := by decide

/-- The grade-weighted fixed profile sums to `1570` through grade `22`. -/
theorem uniformFirstOrderGradedRankProfile_weighted_sum :
    Finset.sum (Finset.range 23) (fun t ↦ t * uniformFirstOrderGradedRankProfile t) = 1570 := by
  decide

/-- The total coefficient-height multiplicity is `88205`. -/
theorem uniformFirstOrderHeightWeightSum_eq :
    uniformFirstOrderHeightWeightSum = 88205 := by decide

/-- The total grade weighted by coefficient-height slots is `1050305`. -/
theorem uniformFirstOrderHeightTotalDegreeSum_eq :
    uniformFirstOrderHeightTotalDegreeSum = 1050305 := by decide

/-- The first-jet exponent contribution to the coefficient-height sum is `167905`. -/
theorem uniformFirstOrderHeightFirstJetSum_eq :
    uniformFirstOrderHeightFirstJetSum = 167905 := by decide

/-- The compressed-row weight sum for the fixed rank profile is `254030`. -/
theorem uniformFirstOrderRowWeightSum_eq :
    uniformFirstOrderRowWeightSum = 254030 := by decide

private theorem uniformFirstOrder_shiftedHeightSlot_accounting (D A : ℕ) :
    12 * A * 88205 + 167905 ≤
      firstOrderCurveShiftedHeightSlotCount D A 12 4 22 1 851 + D * 1050305 := by
  rw [← uniformFirstOrderHeightWeightSum_eq,
    ← uniformFirstOrderHeightTotalDegreeSum_eq,
    ← uniformFirstOrderHeightFirstJetSum_eq]
  have hleft :
      12 * A * uniformFirstOrderHeightWeightSum + uniformFirstOrderHeightFirstJetSum =
        Finset.sum (Finset.range 23) fun t ↦
          Finset.sum (Finset.range (min t 4 + 1)) fun b ↦
            (12 * A + b) * (852 - t) := by
    simp only [uniformFirstOrderHeightWeightSum, uniformFirstOrderHeightFirstJetSum,
      Nat.add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  have hright :
      firstOrderCurveShiftedHeightSlotCount D A 12 4 22 1 851 +
          D * uniformFirstOrderHeightTotalDegreeSum =
        Finset.sum (Finset.range 23) fun t ↦
          Finset.sum (Finset.range (min t 4 + 1)) fun b ↦
            ((12 * A + b - D * t) * (852 - t) + D * t * (852 - t)) := by
    simp only [firstOrderCurveShiftedHeightSlotCount,
      uniformFirstOrderHeightTotalDegreeSum, Nat.reduceAdd, Nat.one_mul, Nat.mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro b hb
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

/-- In the gap-`6/25` regime with `2 ≤ n`, `2 ≤ k`, and `A ≤ n`, ambient degree `k - 1`
is positive, `12 * A` is positive, `k ≤ (k - 1) + 1`, and the fixed shifted row slots are
strictly fewer than the height-851 source slots. -/
theorem uniformFirstOrder_parameters (n k A : ℕ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (_hAn : A ≤ n)
    (hgap : 25 * k + 6 * n ≤ 25 * A) :
    let D := k - 1
    0 < D ∧ 0 < 12 * A ∧ k ≤ D + 1 ∧
      firstOrderCurveShiftedRowSlotBound D A 12 4 22 n 1 851 <
        firstOrderCurveShiftedHeightSlotCount D A 12 4 22 1 851 := by
  dsimp only
  let D := k - 1
  have hD : 0 < D := by dsimp only [D]; omega
  have hkD : k ≤ D + 1 := by dsimp only [D]; omega
  have hDk : D ≤ k := by dsimp only [D]; omega
  have hA : 0 < A := by omega
  refine ⟨hD, by positivity, hkD, ?_⟩
  have hrow' := firstOrderCurveShiftedRowSlotBound_le_of_rankBound
    D A 12 4 22 n 1 851 uniformFirstOrderGradedRankProfile
      (firstOrderGradedRankBound_le_uniformFirstOrderProfile D A)
  have hrow : firstOrderCurveShiftedRowSlotBound D A 12 4 22 n 1 851 ≤
      n * 254030 := by
    calc
      firstOrderCurveShiftedRowSlotBound D A 12 4 22 n 1 851 ≤
          ∑ t ∈ Finset.range (22 + 1),
            n * uniformFirstOrderGradedRankProfile t * (851 + 1 - 1 * t) := hrow'
      _ = n * uniformFirstOrderRowWeightSum := by
        rw [uniformFirstOrderRowWeightSum, show 22 + 1 = 23 by norm_num,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        norm_num only [Nat.reduceAdd, Nat.one_mul]
        ring
      _ = n * 254030 := by rw [uniformFirstOrderRowWeightSum_eq]
  have haccount := uniformFirstOrder_shiftedHeightSlot_accounting D A
  have hstrict :
      n * 254030 + D * 1050305 < 12 * A * 88205 + 167905 := by
    omega
  exact Nat.add_lt_add_iff_right.mp
    ((Nat.add_le_add_right hrow _).trans_lt (hstrict.trans_le haccount))

end ReedSolomon.HiddenDerivative
