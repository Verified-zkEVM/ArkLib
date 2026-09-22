/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FreeOrder

/-!
# Free-order parameter acceptance tests

A concrete parameter set with its slack conditions, the jet-degree budget computed by
`interpolationDegreeBudget_le_iff`, cases showing the remaining boundary hypotheses are needed,
and forms with extra or rounded hypotheses derived from the general statements.
-/

open Filter

namespace ReedSolomon.HiddenDerivative

/-! ### A concrete parameter set: `d = 4`, `ε = θ = 1/2`, `n = 64` -/

/-- `A = ⌈32⌉ = 32`. -/
private theorem test_A : agreementThreshold (1 / 2) 64 = 32 := by
  norm_num [agreementThreshold]

/-- `K = ⌊16⌋ = 16`. -/
private theorem test_K : ambientDimension (1 / 2) (1 / 2) 64 = 16 := by
  norm_num [ambientDimension]

/-- `C = ⌊(11/8) 64⌋ = 88` and `H = ⌊2⌋ = 2`. -/
private theorem test_C_H :
    higherJetDegreeBudget (1 / 2) 4 = 88 ∧ interpolationBoxWidth (1 / 2) 4 = 2 := by
  norm_num [higherJetDegreeBudget, interpolationBoxWidth, multiplicity]

/-- `B = ⌈2048 / 15⌉ = 137`, computed from `interpolationDegreeBudget_le_iff` in natural numbers:
`2048 ≤ 137 · 15` and `¬ 2048 ≤ 136 · 15`. -/
example : interpolationDegreeBudget 4 (1 / 2) (1 / 2) 64 = 137 := by
  have hden : 0 < ambientDimension (1 / 2) (1 / 2) 64 - 1 := by rw [test_K]; norm_num
  apply le_antisymm
  · rw [interpolationDegreeBudget_le_iff hden, test_K, test_A]
    decide
  · by_contra h
    have h' : interpolationDegreeBudget 4 (1 / 2) (1 / 2) 64 ≤ 136 := by omega
    rw [interpolationDegreeBudget_le_iff hden, test_K, test_A] at h'
    revert h'
    decide

/-- The three slack conditions at this parameter set: `2 ≤ 64`, `92 ≤ B`, `15 · 94 ≤ 64 · 32`. -/
example : 2 ≤ 64 ∧ 88 + 2 * 2 ≤ interpolationDegreeBudget 4 (1 / 2) (1 / 2) 64 ∧
    15 * (88 + 3 * 2) ≤ 64 * 32 := by
  have h := freeGlobalDimensionSlacks (ε := 1 / 2) (θ := 1 / 2) (d := 4) (n := 64)
    (by norm_num) (by norm_num) (by norm_num) (by rw [test_K]; norm_num)
  rw [test_C_H.1, test_C_H.2, test_K, test_A] at h
  exact ⟨by norm_num, h.2.1, h.2.2⟩

/-! ### Boundary hypotheses -/

/-- `le_ambientDimension_iff` needs `0 ≤ (1 - θ) ε`: at `ε = 1`, `θ = 2`, `n = 1`, `k = 0` the
left side holds and `0 ≤ -1` fails. -/
example : 0 ≤ ambientDimension 1 2 1 ∧ ¬ ((0 : ℝ) ≤ (1 - 2) * 1 * (1 : ℕ)) := by
  norm_num

/-- `ambientDimension_lt_blockLength` needs `(1 - θ) ε < 1`: at `ε = 1`, `θ = 0` the dimension is
`n`. -/
example : ambientDimension 1 0 5 = 5 := by
  norm_num [ambientDimension]

/-- `interpolationDegreeBudget_le_iff` needs `0 < K - 1`: at `d = 1`, `ε = 1`, `θ = 0`, `n = 1`
the dimension is `K = 1`, the budget is `⌈1 / 0⌉ = 0`, and `m A = 1 ≤ 0` fails. -/
example : interpolationDegreeBudget 1 1 0 1 = 0 ∧
    ¬ multiplicity 1 * agreementThreshold 1 1 ≤ 0 * (ambientDimension 1 0 1 - 1) := by
  norm_num [interpolationDegreeBudget, agreementThreshold, ambientDimension, multiplicity]

/-- `boxFamily_weightedBudget_lt` needs `θ ≥ 0`: at `θ = -1/6`, `d = 4`, `ε = 1`, `n = 600` the
parameters are `K = 700`, `A = 600`, `C = 56`, `H = 0`, and
`699 · 56 = 39144 ≥ 38400 = 64 · 600`. -/
example : ¬ ((ambientDimension 1 (-1 / 6) 600 - 1) *
      (higherJetDegreeBudget (-1 / 6) 4 + 3 * interpolationBoxWidth (-1 / 6) 4) <
    multiplicity 4 * agreementThreshold 1 600) := by
  have hK : ambientDimension 1 (-1 / 6) 600 = 700 := by norm_num [ambientDimension]
  have hA : agreementThreshold 1 600 = 600 := by norm_num [agreementThreshold]
  have hC : higherJetDegreeBudget (-1 / 6) 4 = 56 := by
    norm_num [higherJetDegreeBudget, multiplicity]
  have hH : interpolationBoxWidth (-1 / 6) 4 = 0 := by
    rw [interpolationBoxWidth]
    exact Nat.floor_of_nonpos (by norm_num [multiplicity])
  rw [hK, hA, hC, hH]
  norm_num [multiplicity]

/-- `interpolationBoxWidth_le_multiplicity` needs `θ ≤ 16`: at `θ = 32`, `d = 1` the width is
`2 > 1`. -/
example : interpolationBoxWidth 32 1 = 2 ∧ multiplicity 1 = 1 := by
  norm_num [interpolationBoxWidth, multiplicity]

/-- `interpolationBoxWidth_cast_le` needs `θ ≥ 0`: at `θ = -16`, `d = 1` the width is `0` and the
target is `-1`. -/
example : ¬ ((interpolationBoxWidth (-16) 1 : ℝ) ≤ -16 * (multiplicity 1 : ℝ) / 16) := by
  have hH : interpolationBoxWidth (-16) 1 = 0 := by
    rw [interpolationBoxWidth]
    exact Nat.floor_of_nonpos (by norm_num [multiplicity])
  rw [hH]
  norm_num [multiplicity]

/-- `half_interpolationBoxWidthTarget_le_cast` needs `1 ≤ θ m / 16`: at `θ = 8`, `d = 1` the
target is `1/2`, the width is `0`, and `θ m / 32 = 1/4`. -/
example : ¬ (8 * (multiplicity 1 : ℝ) / 32 ≤ (interpolationBoxWidth 8 1 : ℝ)) := by
  norm_num [interpolationBoxWidth, multiplicity]

/-- `half_rate_le_ambientDimension_sub_one_div` needs `3 ≤ K`: at `ε = 29/10`, `θ = 0`, `n = 1`
the dimension is `K = 2`, and `29/20 > 1 = (K - 1) / n`. -/
example : ambientDimension (29 / 10) 0 1 = 2 ∧
    ¬ ((1 - 0) * (29 / 10 : ℝ) / 2 ≤ ((2 - 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) := by
  refine ⟨?_, by norm_num⟩
  rw [ambientDimension, Nat.floor_eq_iff (by norm_num)]
  norm_num

/-! ### Forms with extra hypotheses -/

/-- `ambientDimension_lt_blockLength` under the hypotheses `0 < ε < 1` and `0 < θ < 1`. -/
example {ε θ : ℝ} {n : ℕ} (hε : 0 < ε) (hε1 : ε < 1) (hθ : 0 < θ) (_hθ1 : θ < 1) (hn : 0 < n) :
    ambientDimension ε θ n < n :=
  ambientDimension_lt_blockLength (by nlinarith) hn

/-- The strict form of `le_interpolationDegreeBudget_of_mul_denominator_le`. -/
example {ε θ : ℝ} {d n t : ℕ} (hd : 0 < d) (hdK : d < ambientDimension ε θ n)
    (ht : t * (ambientDimension ε θ n - 1) < multiplicity d * agreementThreshold ε n) :
    t ≤ interpolationDegreeBudget d ε θ n :=
  le_interpolationDegreeBudget_of_mul_denominator_le (interpolationDenominator_pos hd hdK) ht.le

/-- `freeGlobalDimensionSlacks` under the extra hypotheses `θ < 1` and `0 < n`. -/
example {ε θ : ℝ} {d n : ℕ} (hε : 0 < ε) (hθ : 0 < θ) (_hθ1 : θ < 1) (hd : 0 < d) (_hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    interpolationBoxWidth θ d ≤ multiplicity d ∧
      higherJetDegreeBudget θ d + 2 * interpolationBoxWidth θ d ≤
        interpolationDegreeBudget d ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudget θ d + 3 * interpolationBoxWidth θ d) ≤
        multiplicity d * agreementThreshold ε n :=
  freeGlobalDimensionSlacks hε hθ.le hd hdK

/-- `exists_orderThreshold_for_boxWidth` with the bound `2`. -/
example {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 2 ≤ θ * (multiplicity d : ℝ) / 16 :=
  exists_orderThreshold_for_boxWidth hθ 2

/-- `half_rate_le_ambientDimension_sub_one_div` under the hypothesis `2 ≤ d < K`. -/
example {ε θ : ℝ} {d n : ℕ} (hd : 2 ≤ d) (hdK : d < ambientDimension ε θ n) :
    (1 - θ) * ε / 2 ≤ ((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ) :=
  half_rate_le_ambientDimension_sub_one_div (by omega)

/-- The elementary large-order conditions and the rounded rank comparison hold together for all
large orders below the ambient dimension. -/
example {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, d < ambientDimension ε θ n →
      1 < (θ ^ 3 / 262144) * (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent θ := by
  filter_upwards [eventually_freeOrderElementary hε hθ hθ1] with d hd n hdK
  exact freeOrder_rank_comparison hθ.le (by omega) hd.2.2

end ReedSolomon.HiddenDerivative
