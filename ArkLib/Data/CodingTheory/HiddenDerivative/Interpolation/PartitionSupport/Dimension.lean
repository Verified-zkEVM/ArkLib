/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting
public import ArkLib.ToMathlib.Combinatorics.QuadraticStaircase

/-!
# A quadratic lower bound on the dimension of the partition support space

Fix a tuple `c` of exponents of `Y₁, ..., Y_d` of derivative-order weight at most `W`. The
remaining exponents `(x, b₀)` of `X` and `Y₀` satisfy `x + D (b₀ + ∑_i c_i) < L`, and for `0 < D`
their number is the real-cutoff staircase count `QuadraticStaircase.count D (L / D - ∑_i c_i)`
(`QuadraticStaircase.count_div_sub_eq_sum`). Hence the dimension of the partition support space at
the natural cutoff `L` is exactly

```text
∑_{c} QuadraticStaircase.count D (L / D - ∑_i c_i) ≥ ∑_{c} D (max (L / D - ∑_i c_i) 0) ^ 2 / 2,
```

with no tuple discarded near the boundary. For a code of length `n` and an upper rate bound
`D ≤ rate * n`, a level with `level * n ≤ L` gives the rate form
`n / (2 rate) * ∑_c (max (level - rate ∑_i c_i) 0) ^ 2 ≤ dim`.

Both bounds hold at a real cutoff `L`: the space at `L` is the space at `⌈L⌉₊`
(`partitionSupportSpace_natCeil`), and each term of the lower bound increases with the cutoff.

## Main statements

* `finrank_partitionSupportSpace_eq_sum_count`: the dimension as a sum of staircase counts.
* `partitionSupport_dimension_ge_quadratic_sum`: the positive-part square lower bound.
* `partition_quadratic_rate_lower`: the comparison of one term with its rate form.
* `partitionSupport_dimension_ge_rate_sum`: the rate form of the lower bound.
* `partitionSupport_dimension_ge_quadratic_sum_real` and
  `partitionSupport_dimension_ge_rate_sum_real`: both bounds at a real cutoff.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient Decoding
  and Smaller Cryptographic Proofs*][DKT26], Section 6.2, (73), and Appendix D.2, in the proof of
  Lemma 6.2
-/

@[expose] public section

open PolynomialDifferential Finset

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

/-- For `0 < D`, the dimension of the partition support space at the natural cutoff `L` is the sum,
over the tuples `c` of derivative-order weight at most `W`, of the staircase counts
`QuadraticStaircase.count D (L / D - ∑_i c_i)` of the pairs `(x, b₀)` with
`x + D (b₀ + ∑_i c_i) < L`. -/
theorem finrank_partitionSupportSpace_eq_sum_count (F : Type*) [Field F] (hD : 0 < D) (L : ℕ) :
    Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) =
      ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        QuadraticStaircase.count D ((L : ℝ) / D - ((∑ i, c i : ℕ) : ℝ)) := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount, partitionSourceCount]
  exact sum_congr rfl fun c _ => (QuadraticStaircase.count_div_sub_eq_sum hD L _).symm

/-- The quadratic lower bound on the dimension of the partition support space: for `0 < D`, the
sum over the tuples `c` of derivative-order weight at most `W` of
`D * (max (L / D - ∑_i c_i) 0) ^ 2 / 2` is at most the dimension at the natural cutoff `L`. Each
term bounds one staircase count from below (`QuadraticStaircase.count_ge_quadratic`); tuples with
`L / D ≤ ∑_i c_i` contribute zero. -/
theorem partitionSupport_dimension_ge_quadratic_sum (F : Type*) [Field F] (hD : 0 < D) (L : ℕ) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max ((L : ℝ) / D - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  rw [finrank_partitionSupportSpace_eq_sum_count, Nat.cast_sum]
  exact sum_le_sum fun c _ => QuadraticStaircase.count_ge_quadratic _ _

/-- One term of the quadratic lower bound in rate form. If `0 < D ≤ rate * n` and
`level * n ≤ L`, then for every natural `deg`,
`n / (2 rate) * (max (level - rate * deg) 0) ^ 2 ≤ D * (max (L / D - deg) 0) ^ 2 / 2`.
Multiplying `level - rate * deg` by `n` gives at most `L - D * deg`, and `2 D ≤ 2 rate n`. The
hypothesis `D ≤ rate * n` may be strict: the ambient dimension `D` can be smaller than `rate * n`.
It also forces `0 < rate` and `0 < n`, so neither is assumed. -/
theorem partition_quadratic_rate_lower {n L deg : ℕ} {rate level : ℝ} (hD : 0 < D)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L) :
    (n : ℝ) / (2 * rate) * (max (level - rate * deg) 0) ^ 2 ≤
      (D : ℝ) * (max ((L : ℝ) / D - deg) 0) ^ 2 / 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrn : 0 < rate * n := hDR.trans_le hupper
  have hnR : (0 : ℝ) < n := by
    rcases hn0.eq_or_lt with h | h
    · rw [← h, mul_zero] at hrn
      exact absurd hrn (lt_irrefl 0)
    · exact h
  have hrate : 0 < rate := pos_of_mul_pos_left hrn hn0
  have hsource : (n : ℝ) * (level - rate * deg) ≤ (L : ℝ) - D * deg := by
    have hdeg := mul_le_mul_of_nonneg_right hupper (Nat.cast_nonneg deg : (0 : ℝ) ≤ deg)
    calc
      (n : ℝ) * (level - rate * deg) = level * n + -(rate * n * deg) := by ring
      _ ≤ (L : ℝ) + -(D * deg) := add_le_add hlevel (neg_le_neg hdeg)
      _ = (L : ℝ) - D * deg := by ring
  have hmax : (n : ℝ) * max (level - rate * deg) 0 ≤ max ((L : ℝ) - D * deg) 0 := by
    rw [mul_max_of_nonneg _ _ hnR.le, mul_zero]
    exact max_le_max_right 0 hsource
  have hquot : ((n : ℝ) * max (level - rate * deg) 0) ^ 2 / (2 * rate * n) ≤
      (max ((L : ℝ) - D * deg) 0) ^ 2 / (2 * D) := by
    apply div_le_div₀ (by positivity)
    · exact pow_le_pow_left₀ (by positivity) hmax 2
    · positivity
    · calc
        2 * (D : ℝ) ≤ 2 * (rate * n) := mul_le_mul_of_nonneg_left hupper (by positivity)
        _ = 2 * rate * n := by ring
  have hleft : ((n : ℝ) * max (level - rate * deg) 0) ^ 2 / (2 * rate * n) =
      (n : ℝ) / (2 * rate) * (max (level - rate * deg) 0) ^ 2 := by
    field_simp
  have hright : (max ((L : ℝ) - D * deg) 0) ^ 2 / (2 * D) =
      (D : ℝ) * (max ((L : ℝ) / D - deg) 0) ^ 2 / 2 := by
    have hfactor : (L : ℝ) - D * deg = D * ((L : ℝ) / D - deg) := by field_simp
    have hmaxfactor := mul_max_of_nonneg ((L : ℝ) / D - deg) 0 hDR.le
    rw [mul_zero] at hmaxfactor
    rw [hfactor, ← hmaxfactor, mul_pow]
    field_simp
  simpa only [hleft, hright] using hquot

/-- The rate form of the quadratic lower bound: if `0 < D ≤ rate * n` and `level * n ≤ L`, then
`n / (2 rate) * ∑_c (max (level - rate * ∑_i c_i) 0) ^ 2` is at most the dimension of the
partition support space at the natural cutoff `L`, the sum running over the tuples `c` of
derivative-order weight at most `W`. -/
theorem partitionSupport_dimension_ge_rate_sum (F : Type*) [Field F] {n L : ℕ} {rate level : ℝ}
    (hD : 0 < D) (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L) :
    (n : ℝ) / (2 * rate) *
        ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
          (max (level - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  rw [mul_sum]
  exact (sum_le_sum fun c _ => partition_quadratic_rate_lower hD hupper hlevel).trans
    (partitionSupport_dimension_ge_quadratic_sum F hD L)

/-! ### Real cutoffs -/

/-- The quadratic lower bound on the dimension of the partition support space at a real cutoff
`L`: for `0 < D`, the sum over the tuples `c` of derivative-order weight at most `W` of
`D * (max (L / D - ∑_i c_i) 0) ^ 2 / 2` is at most the dimension. It follows from the
natural-cutoff bound `partitionSupport_dimension_ge_quadratic_sum` at `⌈L⌉₊`, since `L ≤ ⌈L⌉₊`
and both cutoffs give the same space. -/
theorem partitionSupport_dimension_ge_quadratic_sum_real (F : Type*) [Field F] (hD : 0 < D)
    (L : ℝ) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max (L / D - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W L hD) : ℝ) := by
  rw [← partitionSupportSpace_natCeil]
  refine (sum_le_sum fun c _ => ?_).trans (partitionSupport_dimension_ge_quadratic_sum F hD ⌈L⌉₊)
  gcongr
  exact Nat.le_ceil L

/-- The rate form of the quadratic lower bound at a real cutoff: if `0 < D ≤ rate * n` and
`level * n ≤ L`, then `n / (2 rate) * ∑_c (max (level - rate * ∑_i c_i) 0) ^ 2` is at most the
dimension of the partition support space at `L`, the sum running over the tuples `c` of
derivative-order weight at most `W`. The hypothesis `D ≤ rate * n` forces `0 < rate` and `0 < n`,
so neither is assumed. -/
theorem partitionSupport_dimension_ge_rate_sum_real (F : Type*) [Field F] {n : ℕ}
    {rate level L : ℝ} (hD : 0 < D) (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L) :
    (n : ℝ) / (2 * rate) *
        ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
          (max (level - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W L hD) : ℝ) := by
  rw [← partitionSupportSpace_natCeil]
  exact partitionSupport_dimension_ge_rate_sum F hD hupper (hlevel.trans (Nat.le_ceil L))

end ReedSolomon.HiddenDerivative
