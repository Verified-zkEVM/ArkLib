/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.BlockLength

/-!
# Block-length threshold acceptance tests

The thresholds at `R = 1/2`, `d = 2`, `m = 3` and the guards they give, cases showing that
`0 < R`, `R < 1` and the positivity hypotheses of `marginHeight_one_add_inv` are needed, and the
margin height at the ratio `151/150`.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

/-! ### A concrete parameter set: `R = 1/2`, `d = 2`, `m = 3` -/

/-- The jet-degree cap is `⌈2 · 3 / (1/2)⌉₊ = 12`. -/
private theorem test_jetCap : rateJetCap (1 / 2) 3 = 12 := by
  norm_num [rateJetCap]

/-- The threshold is `⌈max (3 / (1/2), 12 + 1, 1 / (1/2))⌉₊ = 13`. -/
example : rateBlockThreshold (1 / 2) 2 3 = 13 := by
  norm_num [rateBlockThreshold, test_jetCap]

/-- The padded threshold is `⌈max (8 / (1/2), 12 / (1/2), 2 / (1/2), 13, 2)⌉₊ = 24`. -/
example : paddedRateBlockThreshold (1 / 2) 2 3 = 24 := by
  norm_num [paddedRateBlockThreshold, test_jetCap]

/-- At `n = 13`, with message dimension `6` and agreement `(1/2) · 13 ≤ 7`, the ambient degree
`D = ⌊13/2⌋₊` satisfies `3 ≤ D`, `D + 1 ≤ 13`, and `⌈13/2⌉₊ ≤ 7`. -/
example : 3 ≤ ⌊(1 / 2 : ℝ) * 13⌋₊ ∧ ⌊(1 / 2 : ℝ) * 13⌋₊ + 1 ≤ 13 ∧ ⌈(1 / 2 : ℝ) * 13⌉₊ ≤ 7 := by
  obtain ⟨hD, -, -, hn, -, -, hA, -⟩ :=
    rateBlockThreshold_guards (rate := 1 / 2) (agreement := 1 / 2) (order := 2)
      (multiplicity := 3) (n := 13) (k := 6) (A := 7) (by norm_num) (by norm_num)
      (by norm_num [rateBlockThreshold, test_jetCap]) (by norm_num) (by norm_num)
  exact ⟨hD, hn, hA⟩

/-! ### Boundary hypotheses -/

/-- `rateBlockThreshold_guards` needs `R < 1`: at `R = 1`, `d = m = 0` the threshold is `1`,
but `n = 1` has `⌊R n⌋₊ + 1 = 2 > n`. -/
example : rateBlockThreshold 1 0 0 ≤ 1 ∧ ¬ (⌊(1 : ℝ) * 1⌋₊ + 1 ≤ 1) := by
  norm_num [rateBlockThreshold, rateJetCap]

/-- `rateBlockThreshold_guards` needs `0 < R`: at `R = 0`, `d = m = 0` the threshold is `1`,
but `n = 1` has `⌊R n⌋₊ = 0 < d + 1`. -/
example : rateBlockThreshold 0 0 0 ≤ 1 ∧ ¬ (0 + 1 ≤ ⌊(0 : ℝ) * 1⌋₊) := by
  norm_num [rateBlockThreshold, rateJetCap]

/-- `paddedRateBlockThreshold_guards` needs `R < 1`: at `R = 1`, `d = m = 0` the padded threshold
is `4`, but `n = 4` has `⌊R n⌋₊ + 1 = 5 > n`. -/
example : paddedRateBlockThreshold 1 0 0 ≤ 4 ∧ ¬ (⌊(1 : ℝ) * 4⌋₊ + 1 ≤ 4) := by
  norm_num [paddedRateBlockThreshold, rateJetCap]

/-- `marginHeight_one_add_inv` needs `0 < ν`: the margin height of `0` is `1`, not `k · 0`. -/
example : marginHeight 0 (1 + 1 / (2 : ℕ)) = 1 := by
  norm_num [marginHeight]

/-- `marginHeight_one_add_inv` needs `0 < k`: at `k = 0` the ratio is `1 + 1/0 = 1`, and the
margin height of `5` is `1`, not `0 · 5`. -/
example : marginHeight 5 (1 + 1 / ((0 : ℕ) : ℝ)) = 1 := by
  norm_num [marginHeight]

/-! ### Margin heights -/

/-- At the ratio `3/2 = 1 + 1/2`, the margin height of `3` is `⌈3 / (1/2)⌉₊ = 6`. -/
example : marginHeight 3 (3 / 2) = 6 := by
  have h := marginHeight_one_add_inv (bound := 3) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- At the ratio `151/150`, the margin height of a positive bound `ν` is `150 ν`. -/
example {ν : ℕ} (hν : 0 < ν) : marginHeight ν (151 / 150 : ℝ) = 150 * ν := by
  have h := marginHeight_one_add_inv hν (k := 150) (by norm_num)
  norm_num at h
  exact h

end ReedSolomon.HiddenDerivative.RatePartition
