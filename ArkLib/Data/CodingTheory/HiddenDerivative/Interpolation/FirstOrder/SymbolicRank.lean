/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Interpolant
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rank of first-order local constraint matrices

For columns whose exponents lie in the first-order interpolation support, the local constraint
matrix of any family of received polynomials has rank over the rational function field at most
the number of points times the certified local rank bound. The proof factors the matrix through
the actual global constraint map on the first-order space.

## Main statements

* `rank_firstOrderLocalConstraintMatrix_le`: the rank bound over the rational function field for
  arbitrary received polynomials and finite point and column types.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

/-- The local constraint matrix over the rational function field has rank at most the number of
points times the certified local rank bound, for arbitrary received polynomials. -/
theorem rank_firstOrderLocalConstraintMatrix_le {F : Type*} [Field F]
    {D A m M μ : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (centers : ι → F) (received : ι → F[X]) (columns : κ → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i))
      received columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤
      Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 := by
  classical
  let K := RatFunc F
  let φ : F[X] →+* K := algebraMap F[X] K
  let V := firstOrderSpace K D A m M μ
  let monomial (j : κ) : V := ⟨(columns j).polynomial, by
    apply mem_firstOrderSpace_iff.mpr
    intro u hu
    have heq : u = (columns j).exponent := by
      simpa [SourceColumn.polynomial] using MvPolynomial.support_monomial_subset hu
    exact heq ▸ mem_firstOrderExponents.mp (heligible j)⟩
  let assemble : (κ → K) →ₗ[K] V :=
    ∑ j, LinearMap.smulRight (LinearMap.proj j) (monomial j)
  let constraint := firstOrderGlobalConstraintMap (D := D) (A := A) (m := m) (M := M)
    (μ := μ) (fun i ↦ φ (Polynomial.C (centers i)))
      (fun i ↦ φ (received i))
  let coefficients : (ι → LocalPolynomial K 1) →ₗ[K]
      ((ι × LowContactIndex 1 m) → K) :=
    LinearMap.pi fun row ↦ MvPolynomial.lcoeff K row.2.1 ∘ₗ LinearMap.proj row.1
  let mat := (localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) received columns).map φ
  have hfactor : mat.mulVecLin = coefficients ∘ₗ constraint ∘ₗ assemble := by
    apply LinearMap.ext
    intro v
    funext row
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      LinearMap.comp_apply, coefficients, LinearMap.pi_apply, MvPolynomial.lcoeff_apply,
      LinearMap.proj_apply, assemble, LinearMap.sum_apply, map_sum,
      LinearMap.smulRight_apply, map_smul]
    change (∑ j,
      φ (localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) received columns row j) *
        v j) = _
    simp only [constraint, firstOrderGlobalConstraintMap_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [localConstraintMatrix_apply_eq_localConstraintAt_coeff, ← MvPolynomial.coeff_map,
      map_localConstraintAt]
    simp [monomial, SourceColumn.polynomial, mul_comm]
  let _ : Module.Finite K V := Module.Finite.of_basis (firstOrderSpaceBasis K D A m M μ)
  change Module.finrank K mat.mulVecLin.range ≤ _
  rw [hfactor]
  apply (LinearMap.finrank_range_comp_le_left (coefficients ∘ₗ constraint) assemble).trans
  rw [LinearMap.range_comp]
  apply (Submodule.finrank_map_le coefficients constraint.range).trans
  simpa [constraint] using
    (finrank_firstOrderGlobalConstraintMap_le (D := D) (A := A) (m := m) (M := M)
      (μ := μ) (fun i ↦ φ (Polynomial.C (centers i)))
      (fun i ↦ φ (received i)))

end ReedSolomon.HiddenDerivative
