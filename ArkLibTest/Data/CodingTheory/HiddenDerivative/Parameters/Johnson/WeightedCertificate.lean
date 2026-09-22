/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.WeightedCertificate

/-!
# Weighted Johnson certificate acceptance tests

A small certificate computed in full, one with a negative moment, cases showing that the slope and
cutoff hypotheses are needed, and the three table rows at `n = 2¹⁶`, `η = 1/100` (rates `1/16`,
`1/4` and `1/2`) with their agreement ceilings and slot inequality.
-/

namespace ReedSolomon.HiddenDerivative

/-! ### A small certificate: `n = 3`, `D = 1`, `A = 3`, `m = 2`, `B = 1` -/

/-- `N = 6 + 5`, `W = 5`, `R = 2 + 1`, `T = 1`, slope `2`, moment `2`, height `max 1 1`. -/
example : johnsonWeightedN 1 3 2 1 = 11 ∧ johnsonWeightedW 1 3 2 1 = 5 ∧
    johnsonWeightedR 2 1 = 3 ∧ johnsonWeightedT 2 1 = 1 ∧
    johnsonWeightedSlope 3 1 3 2 1 = 2 ∧ johnsonWeightedMoment 3 1 3 2 1 = 2 ∧
    johnsonWeightedHeight 3 1 3 2 1 = 1 := by
  decide

private theorem small_cert : IsJohnsonWeightedCertificate 3 1 3 2 1 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- The slot inequality from the certificate: `15 < 17`. -/
example : johnsonWeightedRowSlots 3 2 1 1 < johnsonWeightedSourceSlots 1 3 2 1 1 :=
  small_cert.rowSlots_lt_sourceSlots

example : johnsonWeightedRowSlots 3 2 1 1 = 15 ∧ johnsonWeightedSourceSlots 1 3 2 1 1 = 17 := by
  decide

/-- The rectangle identities at this instance: `17 + 5 = 2 · 11` and `15 + 3 · 1 = 3 · 2 · 3`. -/
example : johnsonWeightedSourceSlots 1 3 2 1 1 + johnsonWeightedW 1 3 2 1 =
    2 * johnsonWeightedN 1 3 2 1 := johnsonWeightedSourceSlots_add_W le_rfl

example : johnsonWeightedRowSlots 3 2 1 1 + 3 * johnsonWeightedT 2 1 =
    3 * 2 * johnsonWeightedR 2 1 := johnsonWeightedRowSlots_add_nT (by decide)

/-! ### A negative moment: `n = 2`, `D = 5`, `A = 3`, `m = 2`, `B = 1` -/

/-- `W - nT = 1 - 2 = -1` with slope `7 - 6 = 1`; the height is the cutoff `B = 1`. -/
example : johnsonWeightedMoment 2 5 3 2 1 = -1 ∧ johnsonWeightedSlope 2 5 3 2 1 = 1 ∧
    johnsonWeightedHeightInt 2 5 3 2 1 = 1 := by
  decide

private theorem neg_cert : IsJohnsonWeightedCertificate 2 5 3 2 1 1 :=
  ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

example : johnsonWeightedRowSlots 2 2 1 1 < johnsonWeightedSourceSlots 5 3 2 1 1 :=
  neg_cert.rowSlots_lt_sourceSlots

/-! ### The kept hypotheses are needed -/

/-- Without `n R < N` the strict height inequality fails: at `m = 0` both moment and slope are
`0`. -/
example : ¬ johnsonWeightedMoment 5 1 1 0 2 <
    ((johnsonWeightedHeight 5 1 1 0 2 + 1 : ℕ) : ℤ) * johnsonWeightedSlope 5 1 1 0 2 := by
  decide

/-- Without the slope condition the slot inequality fails: at `n = 4` there are `20` rows and
`17` slots at height `1`. -/
example : ¬ johnsonWeightedRowSlots 4 2 1 1 < johnsonWeightedSourceSlots 1 3 2 1 1 := by
  decide

/-- The strict cutoff is needed for positive widths: at `D B = m A` the last width is `0`. -/
example : ¬ 0 < 2 * 3 - 3 * 2 := by decide

example : 0 < 2 * 3 - 2 * 2 := johnsonWeighted_slice_pos (D := 2) (B := 2) le_rfl (by norm_num)

/-- The quotient guard at `D = 2`, `m A = 7`: `D B < 7 ↔ B ≤ 3`. -/
example : 2 * 3 < 7 ↔ 3 ≤ (7 - 1) / 2 :=
  johnsonWeighted_cutoff_iff_le_div (m := 7) (A := 1) (by norm_num) (by norm_num)

/-! ### Zero multiplicity -/

example : johnsonWeightedHeight 10 3 4 0 7 = 7 := johnsonWeightedHeight_zero_m 10 3 4 7

/-! ### Table rows at `n = 2¹⁶`, `η = 1/100` -/

/-- The agreement count of the `k/n = 1/16` table row: `⌈(√(4095/2¹⁶) + 1/100) 2¹⁶⌉ = 17038`. -/
theorem johnsonWeightedAgreementCeil_rate_one_sixteenth :
    ⌈(√((4095 : ℝ) / 65536) + 1 / 100) * 65536⌉₊ = 17038 := by
  let x := √((4095 : ℝ) / 65536)
  change ⌈(x + 1 / 100) * 65536⌉₊ = 17038
  rw [Nat.ceil_eq_iff (by norm_num : (17038 : ℕ) ≠ 0)]
  have hx2 : x ^ 2 = (4095 : ℝ) / 65536 := by
    exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  constructor <;> norm_num at ⊢ <;> nlinarith

/-- The agreement count of the `k/n = 1/4` table row: `⌈(√(16383/2¹⁶) + 1/100) 2¹⁶⌉ = 33423`. -/
theorem johnsonWeightedAgreementCeil_rate_one_fourth :
    ⌈(√((16383 : ℝ) / 65536) + 1 / 100) * 65536⌉₊ = 33423 := by
  let x := √((16383 : ℝ) / 65536)
  change ⌈(x + 1 / 100) * 65536⌉₊ = 33423
  rw [Nat.ceil_eq_iff (by norm_num : (33423 : ℕ) ≠ 0)]
  have hx2 : x ^ 2 = (16383 : ℝ) / 65536 := by
    exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  constructor <;> norm_num at ⊢ <;> nlinarith

/-- The agreement count of the `k/n = 1/2` table row: `⌈(√(32767/2¹⁶) + 1/100) 2¹⁶⌉ = 46996`. -/
theorem johnsonWeightedAgreementCeil_rate_one_half :
    ⌈(√((32767 : ℝ) / 65536) + 1 / 100) * 65536⌉₊ = 46996 := by
  let x := √((32767 : ℝ) / 65536)
  change ⌈(x + 1 / 100) * 65536⌉₊ = 46996
  rw [Nat.ceil_eq_iff (by norm_num : (46996 : ℕ) ≠ 0)]
  have hx2 : x ^ 2 = (32767 : ℝ) / 65536 := by
    exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  constructor <;> norm_num at ⊢ <;> nlinarith

/-- The `k/n = 1/16`, `η = 1/100` table row at `n = 2¹⁶` is a weighted certificate. -/
theorem johnsonWeightedCertificate_rate_one_sixteenth :
    IsJohnsonWeightedCertificate 65536 4095 17038 14 57 568 ∧
      57 ≤ (14 * 17038 - 1) / 4095 ∧ 57 ≤ 4095 ∧
      johnsonWeightedU 14 57 = 13 ∧
      johnsonWeightedN 4095 17038 14 57 = 7065821 ∧
      johnsonWeightedW 4095 17038 14 57 = 134813721 ∧
      johnsonWeightedR 14 57 = 105 ∧
      johnsonWeightedT 14 57 = 455 ∧
      johnsonWeightedSlope 65536 4095 17038 14 57 = 184541 ∧
      johnsonWeightedMoment 65536 4095 17038 14 57 = 104994841 ∧
      johnsonWeightedSourceSlots 4095 17038 14 57 568 = 3885638428 ∧
      johnsonWeightedRowSlots 65536 14 57 568 = 3885629440 ∧
      johnsonPairwiseListFloor 65536 4095 17038 = 38 ∧
      johnsonWeightedRefinedExceptionCountFloor 65536 4095 17038 57 568 = 2498629121 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight,
    johnsonWeightedHeightInt, johnsonWeightedSlope, johnsonWeightedMoment,
    johnsonWeightedSourceSlots, johnsonWeightedRowSlots, johnsonPairwiseListFloor,
    johnsonWeightedRefinedExceptionCountFloor,
    johnsonWeightedRefinedExceptionCount, johnsonWeightedN, johnsonWeightedW, johnsonWeightedR,
    johnsonWeightedT, johnsonWeightedU, Finset.sum_range_succ, Int.toNat_of_nonneg]

/-- The `k/n = 1/4`, `η = 1/100` table row at `n = 2¹⁶` is a weighted certificate. -/
theorem johnsonWeightedCertificate_rate_one_fourth :
    IsJohnsonWeightedCertificate 65536 16383 33423 18 36 504 ∧
      36 ≤ (18 * 33423 - 1) / 16383 ∧ 36 ≤ 16383 ∧
      johnsonWeightedU 18 36 = 17 ∧
      johnsonWeightedN 16383 33423 18 36 = 11348640 ∧
      johnsonWeightedW 16383 33423 18 36 = 135172026 ∧
      johnsonWeightedR 18 36 = 171 ∧
      johnsonWeightedT 18 36 = 969 ∧
      johnsonWeightedSlope 65536 16383 33423 18 36 = 141984 ∧
      johnsonWeightedMoment 65536 16383 33423 18 36 = 71667642 ∧
      johnsonWeightedSourceSlots 16383 33423 18 36 504 = 5595891174 ∧
      johnsonWeightedRowSlots 65536 18 36 504 = 5595856896 ∧
      johnsonPairwiseListFloor 65536 16383 33423 = 25 ∧
      johnsonWeightedRefinedExceptionCountFloor 65536 16383 33423 36 504 = 3383852708 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight,
    johnsonWeightedHeightInt, johnsonWeightedSlope, johnsonWeightedMoment,
    johnsonWeightedSourceSlots, johnsonWeightedRowSlots, johnsonPairwiseListFloor,
    johnsonWeightedRefinedExceptionCountFloor, johnsonWeightedRefinedExceptionCount,
    johnsonWeightedN, johnsonWeightedW, johnsonWeightedR, johnsonWeightedT, johnsonWeightedU,
    Finset.sum_range_succ, Int.toNat_of_nonneg]

/-- The `k/n = 1/2`, `η = 1/100` table row at `n = 2¹⁶` is a weighted certificate. -/
theorem johnsonWeightedCertificate_rate_one_half :
    IsJohnsonWeightedCertificate 65536 32767 46996 15 21 234 ∧
      21 ≤ (15 * 46996 - 1) / 32767 ∧ 21 ≤ 32767 ∧
      johnsonWeightedU 15 21 = 14 ∧
      johnsonWeightedN 32767 46996 15 21 = 7939503 ∧
      johnsonWeightedW 32767 46996 15 21 = 54349603 ∧
      johnsonWeightedR 15 21 = 120 ∧
      johnsonWeightedT 15 21 = 560 ∧
      johnsonWeightedSlope 65536 32767 46996 15 21 = 75183 ∧
      johnsonWeightedMoment 65536 32767 46996 15 21 = 17649443 ∧
      johnsonWeightedSourceSlots 32767 46996 15 21 234 = 1811433602 ∧
      johnsonWeightedRowSlots 65536 15 21 234 = 1811415040 ∧
      johnsonPairwiseListFloor 65536 32767 46996 = 15 ∧
      johnsonWeightedRefinedExceptionCountFloor 65536 32767 46996 21 234 = 1448631664 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight,
    johnsonWeightedHeightInt, johnsonWeightedSlope, johnsonWeightedMoment,
    johnsonWeightedSourceSlots, johnsonWeightedRowSlots, johnsonPairwiseListFloor,
    johnsonWeightedRefinedExceptionCountFloor, johnsonWeightedRefinedExceptionCount,
    johnsonWeightedN, johnsonWeightedW, johnsonWeightedR, johnsonWeightedT, johnsonWeightedU,
    Finset.sum_range_succ, Int.toNat_of_nonneg]

/-- The `k/n = 1/2` row: `1811415040 < 1811433602`. -/
example : johnsonWeightedRowSlots 65536 15 21 234 <
    johnsonWeightedSourceSlots 32767 46996 15 21 234 :=
  johnsonWeightedCertificate_rate_one_half.1.rowSlots_lt_sourceSlots

end ReedSolomon.HiddenDerivative
