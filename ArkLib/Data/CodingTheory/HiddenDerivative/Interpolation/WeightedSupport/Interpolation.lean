/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

/-!
# A nonzero interpolant from a weighted-support surplus

Over a field, the local constraint map of order `m` at each received point, restricted to the
weighted support space, has rank at most `localResidualCoordinateBudget d m W ⌈L / D⌉₊`
(`finrank_weightedSupportLocalConstraint_le`). The product of these maps over a finite index type
`ι` therefore has rank at most `card ι` times that budget. If this is below the number of
weighted-support exponents, which is the dimension of the space, some nonzero member of the space
satisfies every local constraint. The rank bound holds in every characteristic, and no
independence of the constraints is assumed.

## Main statements

* `weightedSupportGlobalConstraint`, `finrank_weightedSupportGlobalConstraint_le`: the product map
  and its rank bound.
* `exists_nonzero_weightedSupport_interpolant`: a nonzero interpolant in the weighted support
  space.
* `exists_nonzero_exact_interpolant_of_weightedSupport_surplus`: the same interpolant in the exact
  interpolation space, when `L ≤ m A` and `L ≤ D M`.

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`Interpolation.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* The local budget is `localResidualCoordinateBudget d m W ⌈L / D⌉₊`, the natural-cutoff form used
  by `finrank_weightedSupportLocalConstraint_le` since P3 slice 8; the source wrote the real
  cutoff `L / D`.
* `weightedSupportGlobalConstraint` is unchanged.
* `finrank_weightedSupportGlobalConstraint_le` and `exists_nonzero_weightedSupport_interpolant`
  are specializations of `LinearMap.finrank_range_pi_le` and
  `LinearMap.exists_ne_zero_forall_eq_zero_of_sum_lt` in
  `ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional`, which hold for any finite family of linear
  maps over a division ring.
* `exists_nonzero_exact_interpolant_of_weightedSupport_surplus` is unchanged apart from the
  budget.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] {D d m W : ℕ} {L : ℝ}

/-- The local constraint maps of order `m` at the points `(centers i, received i)`, as one linear
map from the weighted support space to `ι → LocalPolynomial F d`. -/
def weightedSupportGlobalConstraint (hD : 0 < D) (centers received : ι → F) :
    weightedSupportSpace F D d W L hD →ₗ[F] (ι → LocalPolynomial F d) :=
  LinearMap.pi fun i => weightedSupportLocalConstraint m hD (centers i) (received i)

/-- For `0 < d` and `0 < D`, the product map has rank at most
`card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊`. The codomain `LocalPolynomial F d` is
infinite-dimensional; only the ranges of the local maps are finite-dimensional. -/
theorem finrank_weightedSupportGlobalConstraint_le (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F) :
    Module.finrank F (LinearMap.range (weightedSupportGlobalConstraint (d := d) (m := m)
      (W := W) (L := L) hD centers received)) ≤
        Fintype.card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊ := by
  refine (LinearMap.finrank_range_pi_le _).trans ?_
  refine (Finset.sum_le_sum fun i _ => finrank_weightedSupportLocalConstraint_le hd hD
    (centers i) (received i)).trans ?_
  simp

/-- For `0 < d` and `0 < D`, if `card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊` is less
than the number of weighted-support exponents, then some nonzero `Q` in the weighted support space
satisfies the local constraints of order `m` at every `(centers i, received i)`. The
hypothesis `hdim` is the dimension surplus: the space has dimension equal to the number of
exponents (`finrank_weightedSupportSpace_eq_card`), and the product map has smaller rank. -/
theorem exists_nonzero_weightedSupport_interpolant (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊ <
      (weightedSupportExponents D d W L hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ weightedSupportSpace F D d W L hD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨v, hv0, hv⟩ := LinearMap.exists_ne_zero_forall_eq_zero_of_sum_lt
    (fun i => weightedSupportLocalConstraint (d := d) (W := W) (L := L) m hD (centers i)
      (received i))
    (fun i => finrank_weightedSupportLocalConstraint_le hd hD (centers i) (received i))
    (by simpa [finrank_weightedSupportSpace_eq_card hD] using hdim)
  exact ⟨v.1, fun h => hv0 (Subtype.ext h), v.2, hv⟩

/-- Under the hypotheses of `exists_nonzero_weightedSupport_interpolant`, and `d < D`,
`L ≤ m A` and `L ≤ D M`, the nonzero interpolant lies in `exactInterpolationSpace F D A d m M W`.
The two cutoff hypotheses are those of `weightedSupportSpace_le_exactInterpolationSpace`: the
first bounds the specialization weight, the second the first-derivative exponent. -/
theorem exists_nonzero_exact_interpolant_of_weightedSupport_surplus {A M : ℕ}
    (hd : 0 < d) (hD : 0 < D) (hdD : d < D) (centers received : ι → F)
    (hL : L ≤ (m * A : ℕ)) (hcap : L ≤ (D : ℝ) * M)
    (hdim : Fintype.card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊ <
      (weightedSupportExponents D d W L hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨Q, hQ0, hQ, hQlocal⟩ :=
    exists_nonzero_weightedSupport_interpolant hd hD centers received hdim
  exact ⟨Q, hQ0, weightedSupportSpace_le_exactInterpolationSpace hD hdD hL hcap hQ, hQlocal⟩

end ReedSolomon.HiddenDerivative
