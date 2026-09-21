/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Finset.WeightedSimplex.Moments
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Weighted mean and variance on the unit-weight discrete simplex

Let `σ` be a finite index type with `n = Fintype.card σ`, let `Δ S` be the unit-weight simplex
`natWeightedSimplex (fun _ : σ ↦ 1) S`, and let `X c = ∑ i, w i * c i` for weights `w : σ → K`
in a field of characteristic zero. Under the uniform average `𝔼 c ∈ Δ S` (Mathlib's
`Finset.expect`),

* `𝔼 X = S / (n + 1) * ∑ i, w i`;
* `𝔼 X ^ 2 = (S * (S - 1) * (∑ i, w i) ^ 2 + S * (S + n + 1) * ∑ i, w i ^ 2) /
  ((n + 1) * (n + 2))`;
* `𝔼 (X - 𝔼 X) ^ 2 = S * (S + n + 1) / ((n + 1) ^ 2 * (n + 2)) *
  ((n + 1) * ∑ i, w i ^ 2 - (∑ i, w i) ^ 2)`.

The unused budget acts as an `(n + 1)`-st coordinate of weight zero, which is why `n + 1` rather
than `n` appears. The variance keeps the finite factor `S * (S + n + 1)`; replacing it with `S ^ 2`
gives the variance of the continuous simplex and loses the finite-size correction. All formulas
hold at `S = 0` and at an empty index type, and no division by `S` or `n` occurs. Over an ordered
field the variance is nonnegative, and Chebyshev's inequality bounds the number of simplex points
whose statistic deviates from the mean by at least `t`.

## Main statements

* `natSimplexWeightedMean`, `natSimplexWeightedVariance`: the closed forms.
* `expect_natWeightedSimplex_one_weighted`: the exact mean.
* `expect_natWeightedSimplex_one_weighted_sq`: the exact second moment.
* `expect_natWeightedSimplex_one_weighted_sub_sq`: the exact variance.
* `natSimplexWeightedVariance_nonneg`: nonnegativity over an ordered field.
* `sq_mul_card_filter_le_abs_sub_le_card_mul_variance`: Chebyshev's inequality in counting form.
* `sq_mul_card_filter_mean_add_le_le_card_mul_variance`: its upper-tail form.

## References

Generalizes, at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, the declarations of
`ToMathlib/Combinatorics/DiscreteSimplex/Variance.lean` from `OrdinarySimplex r S` over `Fin r`
and real weights to `natWeightedSimplex (fun _ ↦ 1) S` over any finite index type, with weights in
any field of characteristic zero for the identities and any ordered field for the inequalities.
`simplexAverage` is replaced by Mathlib's `Finset.expect`, and `simplexWeightedStatistic` by the
explicit sum `∑ i, w i * c i`. `card_ordinarySimplex_pos` becomes `natWeightedSimplex_nonempty` in
`ArkLib.Data.Finset.WeightedSimplex.Moments`. `simplexWeightedMean` and `simplexWeightedVariance`
become `natSimplexWeightedMean` and `natSimplexWeightedVariance`; `simplex_average_weighted`,
`simplex_average_weighted_square`, `simplex_average_centered_square`, and
`simplexWeightedVariance_nonneg` become the theorems above. `simplex_upper_tail_count`, stated for
an arbitrary subset of the upper tail, becomes
`sq_mul_card_filter_mean_add_le_le_card_mul_variance` for the full upper tail, and is derived from
the two-sided `sq_mul_card_filter_le_abs_sub_le_card_mul_variance`. The source's unnamed example
with variance `5 / 12` is an acceptance case. The sharper one-sided Cantelli bound, continuous
simplex moments, and a comparison between the finite and continuous variances are not treated.
-/

@[expose] public section

namespace Finset

open scoped BigOperators

variable {σ : Type*} [Fintype σ] {K : Type*}

/-- The mean `S / (n + 1) * ∑ i, w i` of the weighted statistic `∑ i, w i * c i` over the
unit-weight simplex of budget `S`, where `n = Fintype.card σ`. The denominator counts the slack
coordinate, which carries weight zero. -/
def natSimplexWeightedMean [Field K] (S : ℕ) (w : σ → K) : K :=
  (S : K) / ((Fintype.card σ : K) + 1) * ∑ i, w i

/-- The variance of the weighted statistic `∑ i, w i * c i` over the unit-weight simplex of
budget `S`, where `n = Fintype.card σ`:
`S * (S + n + 1) / ((n + 1) ^ 2 * (n + 2)) * ((n + 1) * ∑ i, w i ^ 2 - (∑ i, w i) ^ 2)`.
The factor `S * (S + n + 1)` is exact; the continuous simplex has `S ^ 2` in its place. The last
factor is `(n + 1) ^ 2` times the population variance of the `n + 1` values `w i` and `0`. -/
def natSimplexWeightedVariance [Field K] (S : ℕ) (w : σ → K) : K :=
  (S : K) * ((S : K) + ((Fintype.card σ : K) + 1)) /
    (((Fintype.card σ : K) + 1) ^ 2 * ((Fintype.card σ : K) + 2)) *
      (((Fintype.card σ : K) + 1) * ∑ i, w i ^ 2 - (∑ i, w i) ^ 2)

section Field

variable [Field K] [CharZero K]

omit [Fintype σ] in
private theorem card_add_one_ne_zero (σ : Type*) [Fintype σ] :
    (Fintype.card σ : K) + 1 ≠ 0 := by
  exact_mod_cast (show Fintype.card σ + 1 ≠ 0 by omega)

omit [Fintype σ] in
private theorem card_add_two_ne_zero (σ : Type*) [Fintype σ] :
    (Fintype.card σ : K) + 2 ≠ 0 := by
  exact_mod_cast (show Fintype.card σ + 2 ≠ 0 by omega)

variable [DecidableEq σ]

private theorem card_natWeightedSimplex_one_cast_ne_zero (S : ℕ) :
    ((natWeightedSimplex (fun _ : σ ↦ 1) S).card : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (natWeightedSimplex_nonempty _ S).card_pos.ne'

/-- The exact mean of the weighted statistic under the uniform distribution on the unit-weight
simplex. It holds for all budgets, including `S = 0`, where both sides vanish. -/
theorem expect_natWeightedSimplex_one_weighted (w : σ → K) (S : ℕ) :
    𝔼 c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, ∑ i, w i * (c i : K) =
      natSimplexWeightedMean S w := by
  have hC := card_natWeightedSimplex_one_cast_ne_zero (σ := σ) (K := K) S
  have hd := card_add_one_ne_zero (K := K) σ
  have h := card_add_one_mul_sum_natWeightedSimplex_one_weighted w S
  have hsum : ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, ∑ i, w i * (c i : K) =
      (S : K) * (natWeightedSimplex (fun _ : σ ↦ 1) S).card * (∑ i, w i) /
        ((Fintype.card σ : K) + 1) := by
    rw [eq_div_iff hd, mul_comm]
    exact h
  rw [expect_eq_sum_div_card, hsum, natSimplexWeightedMean]
  field_simp

/-- The exact second moment of the weighted statistic under the uniform distribution on the
unit-weight simplex. -/
theorem expect_natWeightedSimplex_one_weighted_sq (w : σ → K) (S : ℕ) :
    𝔼 c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (∑ i, w i * (c i : K)) ^ 2 =
      ((S : K) * ((S : K) - 1) * (∑ i, w i) ^ 2 +
        (S : K) * ((S : K) + ((Fintype.card σ : K) + 1)) * ∑ i, w i ^ 2) /
          (((Fintype.card σ : K) + 1) * ((Fintype.card σ : K) + 2)) := by
  have hC := card_natWeightedSimplex_one_cast_ne_zero (σ := σ) (K := K) S
  have hd := mul_ne_zero (card_add_one_ne_zero (K := K) σ) (card_add_two_ne_zero σ)
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_weighted_sq w S
  have hsum : ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (∑ i, w i * (c i : K)) ^ 2 =
      ((S : K) * ((S : K) - 1) * (∑ i, w i) ^ 2 +
        (S : K) * ((S : K) + ((Fintype.card σ : K) + 1)) * ∑ i, w i ^ 2) *
          (natWeightedSimplex (fun _ : σ ↦ 1) S).card /
            (((Fintype.card σ : K) + 1) * ((Fintype.card σ : K) + 2)) := by
    rw [eq_div_iff hd, mul_comm]
    exact h
  rw [expect_eq_sum_div_card, hsum]
  field_simp

/-- The exact variance of the weighted statistic under the uniform distribution on the unit-weight
simplex. It holds at `S = 0` and at an empty index type, where both sides vanish, without
dividing by `S` or by `Fintype.card σ`. -/
theorem expect_natWeightedSimplex_one_weighted_sub_sq (w : σ → K) (S : ℕ) :
    𝔼 c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S,
        (∑ i, w i * (c i : K) - natSimplexWeightedMean S w) ^ 2 =
      natSimplexWeightedVariance S w := by
  set m := natSimplexWeightedMean (σ := σ) S w
  have hExpand : ∀ c : σ → ℕ, (∑ i, w i * (c i : K) - m) ^ 2 =
      (∑ i, w i * (c i : K)) ^ 2 - 2 * m * ∑ i, w i * (c i : K) + m ^ 2 := fun _ ↦ by ring
  have hne := natWeightedSimplex_nonempty (fun _ : σ ↦ 1) S
  simp_rw [hExpand, expect_add_distrib, expect_sub_distrib, ← mul_expect, expect_const hne,
    expect_natWeightedSimplex_one_weighted_sq, expect_natWeightedSimplex_one_weighted]
  have hd := card_add_one_ne_zero (K := K) σ
  have hd' := card_add_two_ne_zero (K := K) σ
  simp only [m, natSimplexWeightedMean, natSimplexWeightedVariance]
  field_simp
  ring

end Field

section Ordered

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The variance is nonnegative, since it is an average of squares. Equivalently,
`(∑ i, w i) ^ 2 ≤ (n + 1) * ∑ i, w i ^ 2` whenever `S ≠ 0`, which is Cauchy–Schwarz for the
`n + 1` weights `w` and `0`. -/
theorem natSimplexWeightedVariance_nonneg (S : ℕ) (w : σ → K) :
    0 ≤ natSimplexWeightedVariance S w := by
  classical
  rw [← expect_natWeightedSimplex_one_weighted_sub_sq]
  exact expect_nonneg fun _ _ ↦ sq_nonneg _

variable [DecidableEq σ]

/-- Summing the squared deviations over the whole simplex gives the cardinality times the
variance. -/
private theorem sum_sub_sq_eq_card_mul_variance (w : σ → K) (S : ℕ) :
    ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S,
        (∑ i, w i * (c i : K) - natSimplexWeightedMean S w) ^ 2 =
      (natWeightedSimplex (fun _ : σ ↦ 1) S).card * natSimplexWeightedVariance S w := by
  rw [← expect_natWeightedSimplex_one_weighted_sub_sq, card_mul_expect]

/-- Chebyshev's inequality on the unit-weight simplex, in division-free counting form: each point
whose weighted statistic deviates from the mean by at least `t` contributes at least `t ^ 2` to the
total squared deviation, which is `#(Δ S)` times the variance. The hypothesis `0 ≤ t` is
necessary: for negative `t` every point is counted, and at `S = 0` the variance is zero. -/
theorem sq_mul_card_filter_le_abs_sub_le_card_mul_variance (w : σ → K) (S : ℕ) {t : K}
    (ht : 0 ≤ t) :
    t ^ 2 * ((natWeightedSimplex (fun _ : σ ↦ 1) S).filter fun c ↦
        t ≤ |∑ i, w i * (c i : K) - natSimplexWeightedMean S w|).card ≤
      (natWeightedSimplex (fun _ : σ ↦ 1) S).card * natSimplexWeightedVariance S w := by
  rw [← sum_sub_sq_eq_card_mul_variance, mul_comm, ← nsmul_eq_mul, ← sum_const]
  calc
    ∑ _c ∈ (natWeightedSimplex (fun _ : σ ↦ 1) S).filter (fun c ↦
          t ≤ |∑ i, w i * (c i : K) - natSimplexWeightedMean S w|), t ^ 2 ≤
        ∑ c ∈ (natWeightedSimplex (fun _ : σ ↦ 1) S).filter (fun c ↦
          t ≤ |∑ i, w i * (c i : K) - natSimplexWeightedMean S w|),
          (∑ i, w i * (c i : K) - natSimplexWeightedMean S w) ^ 2 := by
      refine sum_le_sum fun c hc ↦ ?_
      rw [← sq_abs (_ - _)]
      exact pow_le_pow_left₀ ht (mem_filter.mp hc).2 2
    _ ≤ ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S,
          (∑ i, w i * (c i : K) - natSimplexWeightedMean S w) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ sq_nonneg _

/-- The upper-tail form of Chebyshev's inequality on the unit-weight simplex: the points whose
weighted statistic is at least `mean + t` number at most `#(Δ S) * variance / t ^ 2`, stated
without division. The hypothesis `0 ≤ t` is necessary for the same reason as in
`sq_mul_card_filter_le_abs_sub_le_card_mul_variance`. The sharper one-sided Cantelli bound is not
claimed. -/
theorem sq_mul_card_filter_mean_add_le_le_card_mul_variance (w : σ → K) (S : ℕ) {t : K}
    (ht : 0 ≤ t) :
    t ^ 2 * ((natWeightedSimplex (fun _ : σ ↦ 1) S).filter fun c ↦
        natSimplexWeightedMean S w + t ≤ ∑ i, w i * (c i : K)).card ≤
      (natWeightedSimplex (fun _ : σ ↦ 1) S).card * natSimplexWeightedVariance S w := by
  refine le_trans ?_ (sq_mul_card_filter_le_abs_sub_le_card_mul_variance w S ht)
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)
  refine Nat.cast_le.mpr (card_le_card fun c hc ↦ ?_)
  rw [mem_filter] at hc ⊢
  exact ⟨hc.1, le_abs.mpr (Or.inl (by linarith [hc.2]))⟩

end Ordered

end Finset
