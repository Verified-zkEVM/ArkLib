/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.RatePartition.Basic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Dimension

/-!
# Quadratic lower bounds on the partition support dimension at a real cutoff

`PartitionSupport/Dimension.lean` bounds the dimension of the partition support space at a
natural cutoff `L` from below by

```text
∑_{c} D (max (L / D - ∑_i c_i) 0) ^ 2 / 2,
```

the sum running over the tuples `c` of exponents of `Y₁, ..., Y_d` of derivative-order weight at
most `W`, and gives the rate form of this bound. This file extends both bounds to a real cutoff
`L`. The space at `L` is the space at `⌈L⌉₊` (`partitionSupportSpace_natCeil`), and each term of
the lower bound increases with the cutoff, so the natural-cutoff bound at `⌈L⌉₊` implies the bound
at `L`. For `L ≤ 0` every term is zero.

## Main statements

* `partitionSupport_dimension_ge_quadratic_sum_real`: the quadratic lower bound at a real
  cutoff.
* `partitionSupport_dimension_ge_rate_sum_real`: its rate form, with a real level and cutoff.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`RatePartition/Area.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `ratePartition_dimension_ge_quadratic_sum` becomes
  `partitionSupport_dimension_ge_quadratic_sum_real`, stated for the dimension of
  `partitionSupportSpace` in place of the number of eligible exponents
  (`finrank_partitionSupportSpace_eq_card` converts between them), with the source's
  `weightedHigherJetTuples (d + 1) W` written `Finset.natWeightedSimplex (fun i : Fin d ↦ i + 1) W`
  and `higherJetTupleDegree c` written `∑ i, c i`. The acceptance tests derive the source's form.
* The source's slot type `RatePartitionSlot` and its lemmas `ratePartitionSlotExponent`,
  `ratePartitionSlotExponent_eligible` and `ratePartitionSlotExponent_injective` proved the
  bound by an injection of staircase slots into the support. Here the bound follows from the
  exact count `finrank_partitionSupportSpace_eq_sum_count` of `PartitionSupport/Dimension.lean`
  at the cutoff `⌈L⌉₊`, so the slot type is not needed.
* `partitionSupport_dimension_ge_rate_sum_real` is new. It extends
  `partitionSupport_dimension_ge_rate_sum` from a natural to a real cutoff.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Finset

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

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
