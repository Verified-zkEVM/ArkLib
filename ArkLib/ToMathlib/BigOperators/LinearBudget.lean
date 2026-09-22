/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Summing charges bounded by a linear function of two budgets

Suppose each index `i` of a finite set carries a charge `x i` bounded by `c * h i + e * a i`,
where `h i` and `a i` are the index's shares of two budgets. If the shares of the first budget,
together with a separate nonnegative amount `r`, total at most `H`, and the shares of the second
budget total at most `B`, then `r` plus all charges is at most `c * H + e * B`, provided
`1 ≤ c` and `0 ≤ e`. The amount `r` is charged at rate one, so it costs no more than it would at
rate `c`.

Exceptional-set counts in mutual correlated agreement arguments are aggregated this way: every
irreducible factor of an interpolating polynomial contributes a count bounded linearly by its
height and root degree, the content contributes its height, and heights and root degrees add up
over the factorization.

## Main statements

* `Finset.add_sum_le_mul_add_mul_of_le`: the aggregated bound in an ordered semiring.

## References

This generalizes the common summation step of `ReedSolomon.ordinaryFactorRaw_sum_le`,
`ReedSolomon.ordinaryUnifiedPowerFactorRawAt_sum_le`, and
`ReedSolomon.ordinaryUnifiedPowerFactorRaw_sum_le` in
`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Factors/{AggregationBounds,
UnifiedBudget}.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source
proved the step three times over `ℚ` for three specific charges. Here the charges, shares and
coefficients are arbitrary elements of an ordered semiring.
-/

@[expose] public section

namespace Finset

open scoped BigOperators

/-- If each charge satisfies `x i ≤ c * h i + e * a i`, the shares `h i` together with `r` total at
most `H`, and the shares `a i` total at most `B`, then `r + ∑ i ∈ s, x i ≤ c * H + e * B`.

The hypothesis `1 ≤ c` lets the amount `r`, charged at rate one, be absorbed at rate `c`; it also
gives `0 ≤ c`, which is needed to scale the first budget. The hypothesis `0 ≤ r` is needed as
well: with `s = ∅`, `r = H = -1`, `c = 2` and `e = B = 0` the conclusion reads `-1 ≤ -2`. The
hypothesis `0 ≤ e` is needed to scale the second budget. -/
theorem add_sum_le_mul_add_mul_of_le {ι R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (s : Finset ι) {x h a : ι → R} {r c e H B : R}
    (hr : 0 ≤ r) (hc : 1 ≤ c) (he : 0 ≤ e)
    (hx : ∀ i ∈ s, x i ≤ c * h i + e * a i)
    (hH : r + ∑ i ∈ s, h i ≤ H) (hB : ∑ i ∈ s, a i ≤ B) :
    r + ∑ i ∈ s, x i ≤ c * H + e * B :=
  calc
    r + ∑ i ∈ s, x i ≤ c * r + ∑ i ∈ s, (c * h i + e * a i) :=
      add_le_add (le_mul_of_one_le_left hr hc) (sum_le_sum hx)
    _ = c * (r + ∑ i ∈ s, h i) + e * ∑ i ∈ s, a i := by
      rw [sum_add_distrib, mul_add, mul_sum, mul_sum, add_assoc]
    _ ≤ c * H + e * B :=
      add_le_add (mul_le_mul_of_nonneg_left hH (zero_le_one.trans hc))
        (mul_le_mul_of_nonneg_left hB he)

end Finset
