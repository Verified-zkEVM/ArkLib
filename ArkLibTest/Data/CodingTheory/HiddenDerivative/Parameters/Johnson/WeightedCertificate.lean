/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.WeightedCertificate

/-!
# Weighted Johnson certificate acceptance tests

A small certificate computed in full, one with a negative moment, cases showing that the slope and
cutoff hypotheses are needed, and the slot inequality read off a reviewed table row.
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

/-! ### Zero multiplicity and the table rows -/

example : johnsonWeightedHeight 10 3 4 0 7 = 7 := johnsonWeightedHeight_zero_m 10 3 4 7

/-- The `k/n = 1/2` row: `1811415040 < 1811433602`. -/
example : johnsonWeightedRowSlots 65536 15 21 234 <
    johnsonWeightedSourceSlots 32767 46996 15 21 234 :=
  johnsonWeightedCertificate_rate_one_half.1.rowSlots_lt_sourceSlots

end ReedSolomon.HiddenDerivative
