/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FreeOrderDimension

/-!
# Free-order dimension comparison acceptance tests

Concrete values of the certified bound against its `4 d⁸` bound, a concrete instance of the
dimension comparison, the exponent identity failing at `θ = -5`, and the source-shaped statements
derived from the general ones.
-/

open Finset

namespace ReedSolomon.HiddenDerivative

/-! ### The certified bound at `m = M = d³` -/

/-- At `d = 1` the certified bound is `2` and the closed-form bound is `4 · Λ₁(1) = 4`. -/
example : certifiedEnlargedRankBound 1 (1 ^ 3) (1 ^ 3) 0 = 2 ∧
    4 * 1 ^ 8 * weightedHigherJetCount 1 (0 + 1 ^ 3) = 4 := by
  decide

/-- At `d = 2`, `W = 0` the certified bound is `755`, well below `4 · 2⁸ · Λ₂(8) = 9216`. -/
example : certifiedEnlargedRankBound 2 (2 ^ 3) (2 ^ 3) 0 = 755 ∧
    4 * 2 ^ 8 * weightedHigherJetCount 2 (0 + 2 ^ 3) = 9216 := by
  decide

/-- At `d = 0` the certified bound is `0`, so no positivity hypothesis on `d` is needed. -/
example (W : ℕ) : certifiedEnlargedRankBound 0 (0 ^ 3) (0 ^ 3) W = 0 := by
  simp [certifiedEnlargedRankBound]

/-- `certifiedEnlargedRankBound_le_of_le_mul` at `d = 1`, `m = 3`, `k = 3`, `M = 1`:
`certifiedEnlargedRankBound 1 3 1 0 ≤ 3 · 3 · 5`. -/
example : certifiedEnlargedRankBound 1 3 1 0 ≤ 3 * (3 * (3 + 1 + 1)) * weightedHigherJetCount 1 3 :=
  certifiedEnlargedRankBound_le_of_le_mul (k := 3) (by norm_num)

/-- `exhibitedKernelResidualCount_le` when the exhibited rectangle is empty (`h > r + 1`): the
residual is the whole `2 × 3` rectangle, `6 ≤ 3 · 5`. -/
example : exhibitedKernelResidualCount 1 2 3 = 6 ∧ 6 ≤ 3 * (1 + 1 + (2 + 1)) := by
  decide

/-- `contactThreshold_le_of_le_mul` at `d = 0`: the threshold is `0 ≤ k` for every `k`. -/
example (m r : ℕ) : contactThreshold 0 0 r ≤ m :=
  contactThreshold_le_of_le_mul (by simp) r

/-! ### The exponent identity -/

/-- `shellExponent_add_rankSavingExponent` needs `θ ≠ -5`: there both exponents divide by `0`. -/
example : shellExponent (-5) + rankSavingExponent (-5) = 0 := by
  norm_num [shellExponent, rankSavingExponent]

/-- At `θ = 1` the exponents are `2/3` and `1/3`. -/
example : shellExponent 1 = 2 / 3 ∧ rankSavingExponent 1 = 1 / 3 := by
  norm_num [shellExponent, rankSavingExponent]

/-! ### The dimension comparison -/

/-- A concrete instance with `d = 1` (`m = M = 1`), `K = 6`, `A = 15`, `W = C = 0`, `H = R = 1`,
`n = 1`: the shell estimate `Λ₁(1) = 1 ≤ 1 · 1` and `1 · 4 · 1 < 5 · 1` give
`certifiedEnlargedRankBound 1 1 1 0 = 2 < dim`. -/
example : 1 * certifiedEnlargedRankBound 1 (1 ^ 3) (1 ^ 3) 0 <
    Module.finrank ℚ (exactInterpolationSpace ℚ (6 - 1) 15 1 (1 ^ 3) (1 ^ 3) 0 (by norm_num)) := by
  have hgood : #(goodHigherExponents 1 0 0) = 1 := by
    rw [card_goodHigherExponents_of_le le_rfl]
    decide
  refine n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace ℚ (d := 1) (K := 6)
    (W := 0) (R := 1) (H := 1) (C := 0) (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num [certifiedEnlargedRankBound])
  rw [hgood]
  decide

/-- The exact-space lower bound at `d = 1`, `D = 2`, `K = 3`, `m = 1`, `A = 6`, `W = C = 0`,
`H = 1`: `#(goodHigherExponents 1 0 0) · 2 · 1 = 2` is at most the dimension, which is `21`. -/
example : #(goodHigherExponents 1 0 0) * (3 - 1) * 1 ^ 3 ≤
      Module.finrank ℚ (exactInterpolationSpace ℚ 2 6 1 1 1 0 (by norm_num)) ∧
    Module.finrank ℚ (exactInterpolationSpace ℚ 2 6 1 1 1 0 (by norm_num)) = 21 := by
  refine ⟨card_goodHigherExponents_mul_le_finrank_exactInterpolationSpace ℚ (K := 3)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num), ?_⟩
  rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
  decide

/-! ### Source-shaped statements -/

/-- The source's `certifiedEnlargedRankBound_le_four_mul_d_pow_eight`, with `0 < d`. -/
example {d W : ℕ} (_hd : 0 < d) :
    certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W ≤
      4 * d ^ 8 * weightedHigherJetCount d (W + d ^ 3) :=
  certifiedEnlargedRankBound_le_four_mul_d_pow_eight d W

/-- The source's `rankShellBound_lt_interpolationBox`, with `0 < θ`, `0 < d`, `0 < n`. -/
example {θ : ℝ} {d K H R n : ℕ} (_hθ : 0 < θ) (_hd : 0 < d) (_hn : 0 < n)
    (hH : θ * (d ^ 3 : ℕ) / 32 ≤ (H : ℝ)) (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent θ)
    (hcompare :
      1 < (θ ^ 3 / 262144) * (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ rankSavingExponent θ) :
    n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3 :=
  rankShellBound_lt_interpolationBox hH hR hcompare

/-- The source's `n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace`, with
`0 < d`, a jet-degree budget `B` with `C + 2H ≤ B`, and an implicit field. -/
example {F : Type*} [Field F] {d A K B W C H R n : ℕ}
    (_hd : 0 < d) (hdK : d < K - 1) (hH : H ≤ d ^ 3) (_hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hshell : weightedHigherJetCount d (W + d ^ 3) ≤ R * (goodHigherExponents d W C).card)
    (harithmetic : n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3) :
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W <
      Module.finrank F (exactInterpolationSpace F (K - 1) A d (d ^ 3) (d ^ 3) W hdK) :=
  n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace F hdK hH hweighted hshell
    harithmetic

/-- The source's `localRankBound_lt_interpolationSpace_of_shell_bounds`, with the parameter
estimates of `Parameters/FreeOrder.lean` supplying the slack conditions: at the free-order
parameters with `d + 1 < K`, the shell estimate and the three real estimates give the
comparison. -/
example {F : Type*} [Field F] {ε θ : ℝ} {d W R n : ℕ} (hε : 0 < ε) (hθ : 0 ≤ θ) (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n - 1)
    (hH : θ * (d ^ 3 : ℕ) / 32 ≤ (interpolationBoxWidth θ d : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent θ)
    (hcompare : 1 < (θ ^ 3 / 262144) * (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (d : ℝ) ^ rankSavingExponent θ)
    (hshell : weightedHigherJetCount d (W + d ^ 3) ≤
      R * #(goodHigherExponents d W (higherJetDegreeBudget θ d))) :
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W <
      Module.finrank F (exactInterpolationSpace F (ambientDimension ε θ n - 1)
        (agreementThreshold ε n) d (d ^ 3) (d ^ 3) W hdK) := by
  obtain ⟨hHle, -, hweighted⟩ := freeGlobalDimensionSlacks (n := n) hε hθ hd (by omega)
  exact localRankBound_lt_interpolationSpace_of_shell_bounds F hdK hHle hweighted hH hR
    hcompare hshell

end ReedSolomon.HiddenDerivative
