/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridRateEnvelope

/-!
# Polynomial-envelope acceptance tests

The rate bound on the agreement-incidence ratio at a concrete parameter set, its composition with
the list envelope, and cases showing that `ρ < a` and `1 ≤ n` are needed.
-/

namespace ReedSolomon.HiddenDerivative

/-- At `n = 10`, `D = 2`, `A = 7`, `ρ = 1/5` and `a = 7/10`, the ratio `8/5` is at most `2`. -/
example : agreementIncidenceRatio 10 2 7 ≤ 1 / (7 / 10 - 1 / 5) :=
  agreementIncidenceRatio_le_one_div_sub (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- With `C = 1 / (a - ρ)`, the rate bound feeds the list envelope. -/
example {n D A μ M : ℕ} {ρ a q : ℝ} (hDn : D ≤ n) (hDA : D < A) (hAn : A ≤ n)
    (hD : (D : ℝ) ≤ ρ * n) (hA : a * n ≤ A) (hρa : ρ < a) (hC : 1 ≤ 1 / (a - ρ)) (hq : 1 ≤ q)
    (hμ : (μ : ℝ) ≤ 1 / (a - ρ) * q) (hT : stageStaircase μ M ≤ 1 / (a - ρ) * q ^ 3) :
    firstOrderListConstant (agreementIncidenceRatio n D A) D μ M ≤
      3 * (1 / (a - ρ)) ^ 2 * n * q ^ 3 :=
  firstOrderListConstant_le_cubic hC hq (by omega) hDn
    (zero_le_one.trans (one_le_agreementIncidenceRatio hDA hAn))
    (agreementIncidenceRatio_le_one_div_sub hDn hDA hD hA hρa) hμ hT

/-- `agreementIncidenceRatio_le_one_div_sub` needs `ρ < a`: at `ρ = a = 7/10` the right side is
`1 / 0 = 0`, below the ratio `8/5`. -/
example : (1 : ℝ) / (7 / 10 - 7 / 10) < agreementIncidenceRatio 10 2 7 := by
  norm_num [agreementIncidenceRatio]

/-- `firstOrderListConstant_le_cubic` needs `1 ≤ n`: at `n = D = 0`, `μ = 1`, `M = 0` the list
constant is `1` and the envelope is `0`. -/
example : firstOrderListConstant 1 0 1 0 = 1 ∧ stageStaircase 1 0 = 0 := by
  norm_num [firstOrderListConstant, stageStaircase]

end ReedSolomon.HiddenDerivative
