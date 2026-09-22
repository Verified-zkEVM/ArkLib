/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Dimension
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.CertifiedRankBound
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact

/-!
# A nonzero first-order interpolant from a dimension surplus

Interpolation through received points `(centers i, received i)`, `i : ι`, with multiplicity `m`
imposes the homogeneous linear conditions `SatisfiesLocalConstraints m (centers i) (received i)`
on a differential polynomial. On the first-order space of `Interpolation/FirstOrder/Space.lean`
each point imposes at most `certifiedEnlargedRankBound 1 m M 0` independent conditions, because
the first-order space embeds in an exact interpolation space with `d = 1` and the local
constraint maps do not depend on the degree bound or the agreement threshold. So if
`card ι * certifiedEnlargedRankBound 1 m M 0` is below the dimension of the first-order space,
rank–nullity gives a nonzero interpolant. The field and the degree bound `D` are arbitrary, and
the centers need not be distinct.

The interpolant depends only on the received points, so one interpolant serves every polynomial
`P` that agrees with them: for each such `P` and each `i`, `(X - centers i)^m` divides the
specialization `Q(X, P, P')`. This holds in every characteristic, since the jet variables are
Hasse derivatives.

## Main statements

* `finrank_firstOrderLocalConstraintAt_le`: the local constraint map on the first-order space has
  rank at most `certifiedEnlargedRankBound 1 m M 0`.
* `finrank_firstOrderGlobalConstraintMap_le`: the constraints at all points have rank at most
  `card ι * certifiedEnlargedRankBound 1 m M 0`.
* `exists_nonzero_firstOrder_interpolant` and
  `exists_nonzero_firstOrder_interpolant_of_dimensionCount`: a nonzero interpolant exists once
  that rank bound is below the number of eligible exponents, or below
  `firstOrderDimensionCount D A m M μ` when `0 < D`.
* `exists_nonzero_firstOrder_interpolant_X_sub_C_pow_dvd`: the interpolant vanishes to order `m`
  at every center after specialization at any polynomial agreeing with the received values.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1.
-/

@[expose] public section

open PolynomialDifferential Module

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F] {D A m M μ : ℕ} {ι : Type*}

/-- The local constraint map at `(center, received)` on the first-order space. -/
def firstOrderLocalConstraintAt (center received : F) :
    firstOrderSpace F D A m M μ →ₗ[F] LocalPolynomial F 1 :=
  (localConstraintAt m center received).domRestrict (firstOrderSpace F D A m M μ)

/-- The local constraint map on the first-order space has rank at most
`certifiedEnlargedRankBound 1 m M 0`, at every center and received value and for every `D`.
For `m = 0` the space is zero; otherwise it embeds in the exact interpolation space with `d = 1`,
degree bound `D + 2`, and agreement threshold `A + 2 μ`. -/
theorem finrank_firstOrderLocalConstraintAt_le (center received : F) :
    finrank F (LinearMap.range (firstOrderLocalConstraintAt (D := D) (A := A) (m := m)
      (M := M) (μ := μ) center received)) ≤ certifiedEnlargedRankBound 1 m M 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : finrank F (firstOrderSpace F D A 0 M μ) = 0 := by
      rw [finrank_firstOrderSpace_eq_card, Finset.card_eq_zero,
        Finset.eq_empty_iff_forall_notMem]
      intro u hu
      simpa using (mem_firstOrderExponents.mp hu).2.2
    exact ((LinearMap.finrank_range_le _).trans h0.le).trans (Nat.zero_le _)
  · have hA : m * A + (D + 2 - D) * μ ≤ m * (A + 2 * μ) := by
      rw [Nat.add_sub_cancel_left, Nat.mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hm) _
    have hle := firstOrderSpace_le_exactInterpolationSpace_of_le (F := F) (D := D) (A := A)
      (M := M) (μ := μ) (W := 0) (by omega : 1 < D + 2) (by omega) hA
    have hfactor : firstOrderLocalConstraintAt (D := D) (A := A) (m := m) (M := M) (μ := μ)
        center received =
        (exactLocalConstraintAt (A := A + 2 * μ) (M := M) (W := 0) (by omega : 1 < D + 2) m
          center received).comp (Submodule.inclusion hle) :=
      LinearMap.ext fun _ => rfl
    rw [hfactor]
    exact (LinearMap.finrank_range_comp_le_left _ _).trans
      (finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound Nat.one_pos _ _ _)

/-- The local constraints at every received point `(centers i, received i)` on the first-order
space, as one linear map into the product. -/
def firstOrderGlobalConstraintMap (centers received : ι → F) :
    firstOrderSpace F D A m M μ →ₗ[F] (ι → LocalPolynomial F 1) :=
  LinearMap.pi fun i => firstOrderLocalConstraintAt (centers i) (received i)

/-- Coordinate `i` of `firstOrderGlobalConstraintMap` is the local constraint map at
`(centers i, received i)`. -/
@[simp]
theorem firstOrderGlobalConstraintMap_apply (centers received : ι → F)
    (Q : firstOrderSpace F D A m M μ) (i : ι) :
    firstOrderGlobalConstraintMap centers received Q i =
      localConstraintAt m (centers i) (received i) Q.1 :=
  rfl

/-- The constraints at all points of a finite received word have rank at most
`card ι * certifiedEnlargedRankBound 1 m M 0`. -/
theorem finrank_firstOrderGlobalConstraintMap_le [Fintype ι] (centers received : ι → F) :
    finrank F (LinearMap.range (firstOrderGlobalConstraintMap (D := D) (A := A) (m := m)
      (M := M) (μ := μ) centers received)) ≤
      Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 := by
  refine (LinearMap.finrank_range_pi_le_sum _).trans ?_
  simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    finrank_firstOrderLocalConstraintAt_le (D := D) (A := A) (m := m) (M := M) (μ := μ)
      (centers i) (received i)

/-- If `card ι * certifiedEnlargedRankBound 1 m M 0` is below the number of first-order eligible
exponents, some nonzero polynomial in the first-order space satisfies the local constraints at
every received point. -/
theorem exists_nonzero_firstOrder_interpolant [Fintype ι] (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧ Q ∈ firstOrderSpace F D A m M μ ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨Q, hQ0, hQ⟩ := LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt
    (f := firstOrderGlobalConstraintMap (D := D) (A := A) (m := m) (M := M) (μ := μ) centers
      received)
    (by
      rw [finrank_firstOrderSpace_eq_card]
      exact (finrank_firstOrderGlobalConstraintMap_le centers received).trans_lt hdim)
  exact ⟨Q.1, fun h => hQ0 (Subtype.ext h), Q.2, fun i => congrFun hQ i⟩

/-- For `0 < D`, if `card ι * certifiedEnlargedRankBound 1 m M 0` is below
`firstOrderDimensionCount D A m M μ`, some nonzero polynomial in the first-order space satisfies
the local constraints at every received point. -/
theorem exists_nonzero_firstOrder_interpolant_of_dimensionCount [Fintype ι] (hD : 0 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      firstOrderDimensionCount D A m M μ) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧ Q ∈ firstOrderSpace F D A m M μ ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_firstOrder_interpolant centers received
    (by rwa [card_firstOrderExponents hD])

/-- Under the hypothesis of `exists_nonzero_firstOrder_interpolant`, some nonzero polynomial `Q`
in the first-order space has the following property: for every polynomial `P` with
`P (centers i) = received i`, the specialization `Q(X, P, P')` is divisible by
`(X - centers i)^m`. The interpolant is chosen before `P`. -/
theorem exists_nonzero_firstOrder_interpolant_X_sub_C_pow_dvd [Fintype ι]
    (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧ Q ∈ firstOrderSpace F D A m M μ ∧
      ∀ P : Polynomial F, ∀ i, P.eval (centers i) = received i →
        (Polynomial.X - Polynomial.C (centers i)) ^ m ∣ differentialSpecialization Q P := by
  obtain ⟨Q, hQ0, hQmem, hQ⟩ := exists_nonzero_firstOrder_interpolant centers received hdim
  exact ⟨Q, hQ0, hQmem, fun P i hP =>
    X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P _ _ hP (hQ i)⟩

end

end ReedSolomon.HiddenDerivative
