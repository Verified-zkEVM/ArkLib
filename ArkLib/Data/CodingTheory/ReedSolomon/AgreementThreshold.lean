/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Integral agreement thresholds and capacity-gap radii

For a Reed–Solomon code of block length `n` and message length `k` and a gap `δ ≥ 0`, the
integral agreement threshold is `k + ⌈δ n⌉` and the matching relative radius is `1 - k / n - δ`.
A word is within this radius of a codeword exactly when the two agree in at least the threshold
number of coordinates. The radius is in the convention of `Code.Lambda`.

## Main definitions

* `ReedSolomon.capacityAgreementThreshold`: the threshold `k + ⌈δ n⌉`.
* `ReedSolomon.capacityRadius`: the radius `1 - k / n - δ`.

## Main statements

* `ReedSolomon.capacityAgreementThreshold_le_iff_real`: for `0 ≤ δ`, the threshold is at most `a`
  exactly when `k + δ n ≤ a`.
* `ReedSolomon.relHammingDist_le_capacityRadius_iff_capacityAgreementThreshold_le`: for `0 ≤ δ` and
  `0 < n`, relative distance at most `1 - k / n - δ` is agreement in at least `k + ⌈δ n⌉`
  coordinates.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

/-- The integral agreement threshold `k + ⌈δ n⌉` for block length `n` and message length `k`. -/
def capacityAgreementThreshold (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  messageDim + ⌈delta * blockLength⌉₊

/-- The relative radius `1 - k / n - δ` for block length `n` and message length `k`. -/
def capacityRadius (delta : ℝ) (blockLength messageDim : ℕ) : ℝ :=
  1 - (messageDim : ℝ) / blockLength - delta

/-- For `0 ≤ δ`, the threshold `k + ⌈δ n⌉` is at most `a` exactly when `k + δ n ≤ a`.

The hypothesis `0 ≤ δ` is needed: for `δ = -1`, `n = 1` and `k = 1` the threshold is `1`, while
`k + δ n = 0`. -/
theorem capacityAgreementThreshold_le_iff_real {delta : ℝ} (hdelta : 0 ≤ delta)
    (blockLength messageDim agreement : ℕ) :
    capacityAgreementThreshold delta blockLength messageDim ≤ agreement ↔
      (messageDim : ℝ) + delta * blockLength ≤ agreement := by
  rw [capacityAgreementThreshold, add_comm,
    ← Nat.ceil_add_natCast (mul_nonneg hdelta blockLength.cast_nonneg), Nat.ceil_le, add_comm]

/-- For `0 ≤ δ` and a nonempty coordinate type with `n` coordinates, the received word is within
relative distance `1 - k / n - δ` of the codeword exactly when they agree in at least
`k + ⌈δ n⌉` coordinates.

Both hypotheses are needed. For `δ = -1`, `n = 1` and `k = 1` the radius is `1`, so every
codeword is within it, while the threshold `1` excludes a codeword that disagrees with the word.
For `n = 0`, `k = 0` and `δ = 2` the radius is `-1`, so no codeword is within it, while the
threshold is `0`. -/
theorem relHammingDist_le_capacityRadius_iff_capacityAgreementThreshold_le {ι F : Type*} [Fintype ι]
    [DecidableEq F] {delta : ℝ} (hdelta : 0 ≤ delta) {messageDim : ℕ}
    (hn : 0 < Fintype.card ι) (codeword received : ι → F) :
    (Code.relHammingDist received codeword : ℝ) ≤
        capacityRadius delta (Fintype.card ι) messageDim ↔
      capacityAgreementThreshold delta (Fintype.card ι) messageDim ≤
        Code.agree codeword received := by
  have hnR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hradius : capacityRadius delta (Fintype.card ι) messageDim =
      1 - ((messageDim : ℝ) + delta * Fintype.card ι) / Fintype.card ι := by
    rw [capacityRadius, add_div, mul_div_cancel_right₀ _ hnR, sub_add_eq_sub_sub]
  rw [capacityAgreementThreshold_le_iff_real hdelta, hradius]
  exact Code.relHammingDist_le_one_sub_div_iff hn

end ReedSolomon
