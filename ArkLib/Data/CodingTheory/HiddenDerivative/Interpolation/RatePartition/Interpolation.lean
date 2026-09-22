/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.LocalRank
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

/-!
# Interpolation from a surplus over the derivative-order coordinate budget

Let `S` be a space of differential polynomials whose exponents all have derivative-order weight at
most `W`. At each of finitely many points `(centers i, received i)`, the local constraint map of
order `m` restricted to `S` has rank at most `localDerivativeCoordinateBudget d m W`
(`finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight`). If `dim S` exceeds the
number of points times that budget, the joint kernel of the local constraint maps is nonzero
(`LinearMap.exists_ne_zero_of_sum_finrank_range_lt`), so `S` contains a nonzero polynomial
satisfying all local constraints. The partition support space is such a space, and this gives the
interpolant of the rate-dependent construction.

The rank bound is an upper bound, not an independence claim, so the surplus condition is
sufficient but not necessary. No hypothesis on `d`, `m`, `L` or the points is needed; for `m = 0`
the budget is zero and every nonzero member of `S` is an interpolant.

## Main statements

* `exists_ne_zero_satisfiesLocalConstraints_of_derivative_weight`: the interpolant in any space
  of derivative-order weight at most `W`.
* `exists_nonzero_partitionSupport_interpolant`: the interpolant in the partition support space.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`RatePartition/Interpolation.lean` and `RatePartition/Rank.lean` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `exists_nonzero_ratePartition_interpolant` becomes `exists_nonzero_partitionSupport_interpolant`,
  with the source's `ratePartitionSpace` and `ratePartitionRankBound` written
  `partitionSupportSpace` and `localDerivativeCoordinateBudget`. Its argument, which uses only the
  derivative-order weight bound, is the new
  `exists_ne_zero_satisfiesLocalConstraints_of_derivative_weight` for any submodule. The linear
  algebra is `LinearMap.exists_ne_zero_of_sum_finrank_range_lt` in
  `ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional`.
* `RatePartition/Rank.lean` is covered by existing declarations. The source's
  `ratePartitionTupleCount d B` is `weightedHigherJetCount (d + 1) B`, and its
  `ratePartitionRankBound d m W` is `localDerivativeCoordinateBudget d m W`, with
  `(m - s) ⌈/⌉ (d + 1)` written `contactThreshold (d + 1) m s`; the acceptance tests check both
  identifications by `rfl`. `RatePartitionLocalIndex`, `card_ratePartitionLocalIndex`,
  `ratePartitionLocalExponent`, `ratePartitionLocalExponents`,
  `card_ratePartitionLocalExponents_le` and `mem_ratePartitionLocalExponents_of_bounds` are
  `localDerivativeExponent`, `localDerivativeExponents`, `card_localDerivativeExponents_le` and
  `mem_localDerivativeExponents_of_bounds` of `Interpolation/Local/Coordinates.lean`, where the
  index type is a `Finset.sigma`. `localDerivativeJetWeight_eq_tuple` is
  `weight_localDerivativeJetWeight`, and `localContactOrder_eq_t_add_error` is
  `localContactOrder_eq` of `HiddenDerivative/Variables.lean`. `ratePartitionLocalConstraint` and
  `finrank_ratePartitionLocalConstraint_le` are `partitionSupportLocalConstraint` and
  `finrank_partitionSupportLocalConstraint_le` of `PartitionSupport/LocalRank.lean`.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Finset

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ} {L : ℝ}

/-- Let `S` be a space of differential polynomials whose exponents all have derivative-order
weight at most `W`. If `card ι * localDerivativeCoordinateBudget d m W < dim S`, then `S` contains
a nonzero polynomial satisfying the local constraints of order `m` at every point
`(centers i, received i)`. The surplus must be strict: for `m = 0` the budget is zero, and the
zero space has no nonzero member. `S` need not be assumed finite-dimensional. -/
theorem exists_ne_zero_satisfiesLocalConstraints_of_derivative_weight {F ι : Type*} [Field F]
    [Fintype ι] {m : ℕ} (centers received : ι → F) (S : Submodule F (DifferentialPolynomial F d))
    (hS : ∀ Q ∈ S, ∀ u ∈ Q.support, fullDerivativeJetWeight u ≤ W)
    (hdim : Fintype.card ι * localDerivativeCoordinateBudget d m W < Module.finrank F S) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ S ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  let φ := fun i => (localConstraintAt m (centers i) (received i)).domRestrict S
  have hsum : ∑ i, Module.finrank F (LinearMap.range (φ i)) < Module.finrank F S :=
    calc ∑ i, Module.finrank F (LinearMap.range (φ i))
        ≤ ∑ _i : ι, localDerivativeCoordinateBudget d m W := sum_le_sum fun i _ =>
          finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight m W _ _ S hS
      _ = Fintype.card ι * localDerivativeCoordinateBudget d m W := by simp
      _ < Module.finrank F S := hdim
  obtain ⟨Q, hQ, hlocal⟩ := LinearMap.exists_ne_zero_of_sum_finrank_range_lt φ hsum
  exact ⟨Q.1, fun h => hQ (Subtype.ext h), Q.2, hlocal⟩

/-- If the number of partition-support eligible exponents exceeds `card ι` times the local
coordinate budget `localDerivativeCoordinateBudget d m W`, the partition support space contains a
nonzero polynomial satisfying the local constraints of order `m` at every point
`(centers i, received i)`. The statement holds over every field and for every real cutoff `L`. -/
theorem exists_nonzero_partitionSupport_interpolant {F ι : Type*} [Field F] [Fintype ι] {m : ℕ}
    (hD : 0 < D) (centers received : ι → F)
    (hdim : Fintype.card ι * localDerivativeCoordinateBudget d m W <
      #(partitionSupportExponents D d W L hD)) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ partitionSupportSpace F D d W L hD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_ne_zero_satisfiesLocalConstraints_of_derivative_weight centers received _
    (fun _ hQ u hu => (mem_partitionSupportSpace_iff.mp hQ u hu).1)
    (by rwa [finrank_partitionSupportSpace_eq_card])

end ReedSolomon.HiddenDerivative
