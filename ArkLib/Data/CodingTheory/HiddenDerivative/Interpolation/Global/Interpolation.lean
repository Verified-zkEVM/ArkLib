/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

/-!
# A nonzero global hidden-derivative interpolant

The global interpolation step asks for a nonzero differential polynomial `Q` in the exact
interpolation space that satisfies the local constraints at every received point
`(centers i, received i)`. This file derives such a `Q` from a strict comparison between the rank
of the global constraint map and the dimension of the exact interpolation space. The rank
comparison stays a hypothesis: bounding it is the job of the local rank analysis
(`Interpolation/Local/Rank.lean`, `Interpolation/Local/CertifiedRankBound.lean`) and of the
parameter choice.

The global constraint map `globalExactCoefficientConstraintMap` has a finite-dimensional domain
but an infinite-dimensional codomain `ι → LocalPolynomial F d`, so the argument is rank–nullity
on the range (`LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt`); no finite-dimensional
codomain is assumed. The rank of the global map is at most the sum of the local ranks
(`LinearMap.finrank_range_pi_le_sum`), which turns per-point rank bounds into the familiar
counting criterion `∑ i, rank_i < dim`.

## Main statements

* `range_exactCoefficientLocalConstraintAt`: the local constraint map has the same range on exact
  coefficients as on the exact interpolation space.
* `finrank_range_globalExactCoefficientConstraintMap_le_sum`: the global rank is at most the sum
  of the local ranks.
* `exists_nonzero_global_interpolation_coefficients_of_rank_lt` and
  `exists_nonzero_global_interpolant_of_rank_lt`: a global rank below the interpolation dimension
  gives a nonzero kernel vector, as coefficients and as a polynomial.
* `exists_nonzero_global_interpolant_of_rank_le`,
  `exists_nonzero_global_interpolant_of_local_rank_sum_lt`,
  `exists_nonzero_global_interpolant_of_local_rank_bounds`, and
  `exists_nonzero_global_interpolant_of_uniform_local_rank_bound`: the same conclusion from an
  explicit rank bound, from the sum of the local ranks, from per-point bounds, and from one
  uniform bound `#ι * r < dim`.

## References

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Global/Interpolation.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. Changes:

* The source's `range_exact_coefficient_local_constraint_at_eq` is
  `range_exactCoefficientLocalConstraintAt`, and
  `finrank_range_global_exact_coefficient_constraint_map_le_sum_local` is
  `finrank_range_globalExactCoefficientConstraintMap_le_sum`; its hand-built inclusion of the range
  into a product of ranges is replaced by the generic `LinearMap.finrank_range_pi_le_sum`.
* The rank–nullity argument of `exists_nonzero_global_interpolation_coefficients_of_rank_lt` is
  the generic `LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt`.
* `exists_nonzero_global_interpolation_coefficients_of_rank_lt`,
  `exists_nonzero_global_interpolant_of_rank_lt`, and
  `exists_nonzero_global_interpolant_of_rank_le` no longer assume `[Fintype ι]`: the set of
  received points may be infinite, because the global rank is bounded by the interpolation
  dimension regardless. Only the statements that sum over `ι` keep `[Fintype ι]`.
* The remaining statements keep their source forms.

Deferred: `Interpolation/Global/Multiplicity.lean`, which needs `Interpolation/SpecializationDegree`
and the root-counting chain behind it.

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164, Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F]
variable {D A d m M W : ℕ}
variable {ι : Type*}

/-! ### From local ranks to the global rank -/

/-- The local constraint map on exact coefficients and the local constraint map on the exact
interpolation space have the same range, because the coefficient map is the space map composed
with the coefficient-to-polynomial isomorphism. -/
theorem range_exactCoefficientLocalConstraintAt (hdD : d < D) (center received : F) :
    LinearMap.range (exactCoefficientLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
      hdD m center received) =
      LinearMap.range (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
        hdD m center received) := by
  rw [exactCoefficientLocalConstraintAt, exactInterpolationCoefficientEvaluator,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rfl

/-- The rank of the global constraint map is at most the sum of the ranks of the local constraint
maps on the exact interpolation space. Each local rank is stated for `exactLocalConstraintAt`,
the form bounded by the local rank analysis. The index type must be finite for the sum to make
sense. -/
theorem finrank_range_globalExactCoefficientConstraintMap_le_sum [Fintype ι]
    (hdD : d < D) (centers received : ι → F) :
    Module.finrank F (LinearMap.range
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received)) ≤
      ∑ i, Module.finrank F (LinearMap.range
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i))) := by
  refine (LinearMap.finrank_range_pi_le_sum _).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [range_exactCoefficientLocalConstraintAt]

/-! ### Nonzero kernel extraction -/

/-- If the rank of the global constraint map is below the dimension of the exact interpolation
space, some nonzero coefficient vector lies in its kernel. The set of received points may be
infinite. -/
theorem exists_nonzero_global_interpolation_coefficients_of_rank_lt
    (hdD : d < D) (centers received : ι → F)
    (hrank : Module.finrank F (LinearMap.range
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received)) <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ v : ExactInterpolationCoefficients F D A d m M W hdD,
      v ≠ 0 ∧
        globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received v = 0 := by
  apply LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt
  rwa [LinearEquiv.finrank_eq (exactInterpolationPolynomial hdD)]

/-- If the rank of the global constraint map is below the dimension of the exact interpolation
space, there is a nonzero polynomial in the exact interpolation space that satisfies the local
constraints at every received point. The set of received points may be infinite. -/
theorem exists_nonzero_global_interpolant_of_rank_lt
    (hdD : d < D) (centers received : ι → F)
    (hrank : Module.finrank F (LinearMap.range
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received)) <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨v, hv0, hvker⟩ :=
    exists_nonzero_global_interpolation_coefficients_of_rank_lt hdD centers received hrank
  refine ⟨exactInterpolationPolynomial hdD v, ?_, (exactInterpolationPolynomial hdD v).2,
    fun i => ?_⟩
  · rw [Ne, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff]
    exact hv0
  · simpa [SatisfiesLocalConstraints, exactCoefficientLocalConstraintAt,
      exactInterpolationCoefficientEvaluator] using congrFun hvker i

/-- An explicit upper bound `rankBound` on the global rank, strictly below the dimension of the
exact interpolation space, gives the global interpolant. -/
theorem exists_nonzero_global_interpolant_of_rank_le
    (hdD : d < D) (centers received : ι → F) (rankBound : ℕ)
    (hrank : Module.finrank F (LinearMap.range
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received)) ≤ rankBound)
    (hdim : rankBound < Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_global_interpolant_of_rank_lt hdD centers received (hrank.trans_lt hdim)

/-- If the sum of the local ranks over finitely many received points is below the dimension of
the exact interpolation space, the global interpolant exists. -/
theorem exists_nonzero_global_interpolant_of_local_rank_sum_lt [Fintype ι]
    (hdD : d < D) (centers received : ι → F)
    (hdim : (∑ i, Module.finrank F (LinearMap.range
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i)))) <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_global_interpolant_of_rank_le hdD centers received _
    (finrank_range_globalExactCoefficientConstraintMap_le_sum hdD centers received) hdim

/-- Per-point upper bounds `rankBound i` on the local ranks give the global interpolant when
their sum is below the dimension of the exact interpolation space. -/
theorem exists_nonzero_global_interpolant_of_local_rank_bounds [Fintype ι]
    (hdD : d < D) (centers received : ι → F) (rankBound : ι → ℕ)
    (hrank : ∀ i, Module.finrank F (LinearMap.range
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i))) ≤ rankBound i)
    (hdim : (∑ i, rankBound i) <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_global_interpolant_of_local_rank_sum_lt hdD centers received
    ((Finset.sum_le_sum fun i _ => hrank i).trans_lt hdim)

/-- One uniform bound `rankBound` on every local rank gives the global interpolant when
`#ι * rankBound` is below the dimension of the exact interpolation space. -/
theorem exists_nonzero_global_interpolant_of_uniform_local_rank_bound [Fintype ι]
    (hdD : d < D) (centers received : ι → F) (rankBound : ℕ)
    (hrank : ∀ i, Module.finrank F (LinearMap.range
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i))) ≤ rankBound)
    (hdim : Fintype.card ι * rankBound <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_global_interpolant_of_local_rank_bounds hdD centers received
    (fun _ => rankBound) hrank (by simpa using hdim)

end ReedSolomon.HiddenDerivative
