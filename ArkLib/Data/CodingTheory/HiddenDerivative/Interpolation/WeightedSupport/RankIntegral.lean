/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Finset.WeightedSimplex.RankIntegral
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer

/-!
# The weighted residual rank integral for the hidden-derivative support

The local rank estimate for the hidden-derivative weighted support sums the residual
`max (T - ∑ i, c i) 0 + 1` over the higher-jet exponents `c : Fin n → ℕ` with
`∑ i, (i + 1) * c i ≤ W`, that is, over `Finset.natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W`,
where `n = d - 1` for derivative order `d`. This file specializes the generic bounds of
`ArkLib.Data.Finset.WeightedSimplex.RankIntegral` to these weights and to coefficients `1`.

Write `W' = W + (n + 1).choose 2` for the budget enlarged by the total weight
`∑ i : Fin n, (i + 1)`, `H = harmonic n` and `H₂ = ∑ i : Fin n, 1 / (i + 1) ^ 2`. The coordinate
sum `∑ i, u i` has average `W' * H / (n + 1)` on the continuous simplex of budget `W'` and variance
at most `W' ^ 2 * H₂ / ((n + 1) * (n + 2))`. For `T + n > W' * H / (n + 1)`, the residual sum is at
most the volume of that simplex times
`T + n - μ + (W' ^ 2 * H₂ / ((n + 1) * (n + 2))) / (4 * (T + n - μ)) + 1` with
`μ = W' * H / (n + 1)`.
Finally, the volume of the simplex of budget `W + r + (n + 1).choose 2` is at most
`W ^ n / (n!) ^ 2 * exp (n / W * (r + (n + 1).choose 2))`.

## Main statements

* `ReedSolomon.HiddenDerivative.weighted_residual_sum_le_volume_mul_mean_variance`: the residual
  sum with an arbitrary variance bound `V`.
* `ReedSolomon.HiddenDerivative.weightedSimplex_centeredRadius_sq_le_harmonic`: the variance bound.
* `ReedSolomon.HiddenDerivative.weighted_residual_sum_le_volume_mul_harmonic_variance`: the residual
  sum with the variance discharged.
* `ReedSolomon.HiddenDerivative.volume_weightedSimplex_add_choose_le_exp`: the exponential volume
  bound for the enlarged simplex.

## References

Ports `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

* The source's `weightedHigherJetTuples d W` is `natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W`
  and its `higherJetTupleDegree c` is `∑ i, c i`, with `n` for `d - 1`, following
  `ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer`. The
  source's `harmonicPowerSum (d - 1) 1` is `harmonic n`, and `harmonicPowerSum (d - 1) 2` is
  written out as a sum.
* `weighted_residual_sum_le_volume_mul_mean_variance` and
  `weighted_residual_sum_le_volume_mul_harmonic_variance` are specializations of
  `Finset.sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le` and
  `Finset.sum_natWeightedSimplex_max_sub_add_one_le`. The hypotheses `1 ≤ d` and
  `0 < W + choose d 2` are dropped, and the variance is a set average instead of an integral
  against `weightedSimplexProbabilityMeasure`.
* `weightedSimplex_centeredRadius_sq_le_harmonic` specializes
  `MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean_sq_le`. The hypotheses `1 ≤ d` and
  `0 < W'` are dropped.
* `volume_weightedSimplex_add_choose_le_exp` specializes
  `MeasureTheory.volume_real_weightedSimplex_add_le_mul_exp`.

The consumer `WeightedSupport/NormalizedRank.lean` combines these bounds with the rank bound of
`WeightedSupport/RankBound.lean`. Deferred: the consumer `Margin.lean`, which needs the rounding
estimates of `Parameters/WeightedSupport/`, not ported yet.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

/-- The real weights `i + 1` of `Fin n` sum to `(n + 1).choose 2`. -/
private theorem sum_cast_succ_weight (n : ℕ) :
    ∑ i : Fin n, ((i : ℝ) + 1) = ((n + 1).choose 2 : ℕ) := by
  rw [← sum_fin_succ_eq_choose_two]
  push_cast
  rfl

/-- The harmonic number as a sum over `Fin n`. -/
private theorem harmonic_eq_sum_fin' (n : ℕ) :
    (harmonic n : ℝ) = ∑ i : Fin n, 1 / ((i : ℝ) + 1) := by
  rw [harmonic, Rat.cast_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1)) n]
  push_cast
  simp [one_div]

/-- The residual sum over the higher-jet exponents with an arbitrary variance bound. With
`W' = W + (n + 1).choose 2`, `S = Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W'`,
`μ = W' * harmonic n / (n + 1)` and `c = T + n`, if `μ < c` and `V` bounds
`⨍ u in S, (∑ i, u i - μ) ^ 2`, then
`∑ c ∈ natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W, (max (T - ∑ i, c i) 0 + 1) ≤
  vol S * (c - μ + V / (4 * (c - μ)) + 1)`.
The condition `μ < c` is needed by the positive-part bound
`MeasureTheory.setIntegral_max_sub_zero_le`. -/
theorem weighted_residual_sum_le_volume_mul_mean_variance (n W : ℕ) {T V : ℝ}
    (hc : ((W : ℝ) + ((n + 1).choose 2 : ℕ)) * harmonic n / (n + 1) < T + n)
    (hV : ⨍ u in Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1)
          ((W : ℝ) + ((n + 1).choose 2 : ℕ)),
        (∑ i, u i - ((W : ℝ) + ((n + 1).choose 2 : ℕ)) * harmonic n / (n + 1)) ^ 2 ≤ V) :
    ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W,
        (max (T - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) ≤
      volume.real (Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1)
          ((W : ℝ) + ((n + 1).choose 2 : ℕ))) *
        (T + n - ((W : ℝ) + ((n + 1).choose 2 : ℕ)) * harmonic n / (n + 1) +
          V / (4 * (T + n - ((W : ℝ) + ((n + 1).choose 2 : ℕ)) * harmonic n / (n + 1))) + 1) := by
  have hsum := sum_cast_succ_weight n
  have hH := harmonic_eq_sum_fin' n
  have h := Finset.sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le
    (w := fun i : Fin n ↦ i.val + 1) (fun i ↦ Nat.succ_ne_zero _) W (a := 1)
    (fun _ ↦ zero_le_one) (T := T) (V := V)
  simp only [Nat.cast_add, Nat.cast_one, Pi.one_apply, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum, ← hH] at h
  push_cast
  exact h hc hV

/-- The variance of the coordinate sum on the weighted simplex with weights `1, …, n` is at most
`W ^ 2 * H₂ / ((n + 1) * (n + 2))`, where `H₂ = ∑ i : Fin n, 1 / (i + 1) ^ 2`. The exact variance
is `W ^ 2 * ((n + 1) * H₂ - H ^ 2) / ((n + 1) ^ 2 * (n + 2))` with `H = harmonic n`; the bound drops
the term in `H ^ 2`. No hypothesis on `W` is needed. -/
theorem weightedSimplex_centeredRadius_sq_le_harmonic (n : ℕ) (W : ℝ) :
    ⨍ u in Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W,
        (∑ i, u i - W * harmonic n / (n + 1)) ^ 2 ≤
      W ^ 2 * (∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) / ((n + 1) * (n + 2)) := by
  have hH := harmonic_eq_sum_fin' n
  have h := setAverage_weightedSimplex_linearForm_sub_mean_sq_le
    (w := fun i : Fin n ↦ (i : ℝ) + 1) (fun i ↦ by positivity) 1 W
  simp only [Pi.one_apply, one_mul, Fintype.card_fin, div_pow, one_pow] at h
  rw [hH]
  exact h

/-- The residual sum over the higher-jet exponents with the variance discharged. With
`W' = W + (n + 1).choose 2`, `S = Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W'`,
`μ = W' * harmonic n / (n + 1)`, `c = T + n` and `H₂ = ∑ i : Fin n, 1 / (i + 1) ^ 2`, if `μ < c`
then
`∑ c ∈ natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W, (max (T - ∑ i, c i) 0 + 1) ≤
  vol S * (c - μ + (W' ^ 2 * H₂ / ((n + 1) * (n + 2))) / (4 * (c - μ)) + 1)`. -/
theorem weighted_residual_sum_le_volume_mul_harmonic_variance (n W : ℕ) {T : ℝ}
    (hc : ((W : ℝ) + ((n + 1).choose 2 : ℕ)) * harmonic n / (n + 1) < T + n) :
    ∑ c ∈ Finset.natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W,
        (max (T - ((∑ i, c i : ℕ) : ℝ)) 0 + 1) ≤
      volume.real (Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1)
          ((W : ℝ) + ((n + 1).choose 2 : ℕ))) *
        (T + n - ((W : ℝ) + ((n + 1).choose 2 : ℕ)) * harmonic n / (n + 1) +
          (((W : ℝ) + ((n + 1).choose 2 : ℕ)) ^ 2 * (∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) /
              ((n + 1) * (n + 2))) /
            (4 * (T + n - ((W : ℝ) + ((n + 1).choose 2 : ℕ)) * harmonic n / (n + 1))) + 1) :=
  weighted_residual_sum_le_volume_mul_mean_variance n W hc
    (weightedSimplex_centeredRadius_sq_le_harmonic n _)

/-- Enlarging the budget of the weighted simplex with weights `1, …, n` from `W` to
`W + r + (n + 1).choose 2` costs at most the factor `exp (n / W * (r + (n + 1).choose 2))`:
`vol (weightedSimplex (fun i ↦ i + 1) (W + r + (n + 1).choose 2)) ≤
  W ^ n / (n!) ^ 2 * exp (n / W * (r + (n + 1).choose 2))`.
The hypothesis `0 < W` is needed; for `W = 0` and `n ≥ 1` the right side is `0`. -/
theorem volume_weightedSimplex_add_choose_le_exp (n W r : ℕ) (hW : 0 < W) :
    volume.real (Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1)
        ((W : ℝ) + r + ((n + 1).choose 2 : ℕ))) ≤
      (W : ℝ) ^ n / (n.factorial : ℝ) ^ 2 *
        Real.exp (n / W * (r + ((n + 1).choose 2 : ℕ))) := by
  have h := volume_real_weightedSimplex_add_le_mul_exp (w := fun i : Fin n ↦ (i : ℝ) + 1)
    (fun i ↦ by positivity) (W := W) (Nat.cast_pos.2 hW) (r + ((n + 1).choose 2 : ℕ))
  rw [volume_real_weightedSimplex_succ n (Nat.cast_nonneg W), Fintype.card_fin, ← add_assoc]
    at h
  refine h.trans_eq ?_
  congr 2
  ring

end ReedSolomon.HiddenDerivative
