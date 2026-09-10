/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Interpolation
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Soundness

/-!
# The actual symbolic matrix rank for first-order support

A received line has entries in `F[Z]`. Its rank must be bounded over `F(Z)`, where
row dependencies may use rational functions. The first-order local rank theorem
holds over every field, so it also holds over this rational function field.

This module identifies the mapped symbolic matrix with the composition of three
linear maps: assemble supported monomials, impose the actual local constraints,
and read their low-contact coefficients. Thus no matrix-rank hypothesis remains
for the first-order support when applying the column-height construction.

## Reading the statement

The source columns may be any selection of eligible monomials; they need not be
independent for the rank bound. `1 < D` is the existing exact-support hypothesis.
The conclusion uses the envelope rank `certifiedEnlargedRankBound 1 m M 0` and
holds uniformly over received words and evaluation points, in every characteristic.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation

variable {F : Type*} [Field F]

/-- Changing coefficients commutes with the projected local constraint map. -/
theorem map_localConstraintAt {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (m d : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d) :
    MvPolynomial.map φ (localConstraintAt m center received Q) =
      localConstraintAt m (φ center) (φ received) (MvPolynomial.map φ Q) := by
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [map_projectLowContact, map_unscaledLocalSubstitution]

/-- The symbolic first-order matrix has the certified global rank bound over `F(Z)`.
The proof factors it through the actual global constraint map on the capped support. -/
theorem firstOrder_symbolic_matrix_rank_le {D A m M μ n N : ℕ}
    (hD : 1 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((matrix m centers f g columns).map (algebraMap F[X] (RatFunc F))).rank ≤
      n * certifiedEnlargedRankBound 1 m M 0 := by
  classical
  let K := RatFunc F
  let φ : F[X] →+* K := algebraMap F[X] K
  let V := firstOrderSpace K D A m M μ
  let monomial (j : Fin N) : V := ⟨(columns j).polynomial, by
    apply mem_firstOrderSpace_iff.mpr
    intro u hu
    have heq : u = (columns j).exponent := by
      simpa [SourceColumn.polynomial] using MvPolynomial.support_monomial_subset hu
    exact heq ▸ heligible j⟩
  let assemble : (Fin N → K) →ₗ[K] V :=
    ∑ j, (LinearMap.smulRight (LinearMap.proj j) (monomial j))
  let constraint := firstOrderGlobalConstraint (D := D) (A := A) (m := m) (M := M) (μ := μ)
    (fun i ↦ φ (Polynomial.C (centers i))) (fun i ↦ φ (receivedLine (f i) (g i)))
  let coefficients : (Fin n → LocalPolynomial K 1) →ₗ[K]
      ((Fin n × LowContactIndex 1 m) → K) :=
    LinearMap.pi fun row ↦ MvPolynomial.lcoeff K row.2.1 ∘ₗ LinearMap.proj row.1
  let mat := (matrix m centers f g columns).map φ
  have hfactor : mat.mulVecLin = coefficients ∘ₗ constraint ∘ₗ assemble := by
    apply LinearMap.ext
    intro v
    funext row
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      LinearMap.comp_apply, coefficients, LinearMap.pi_apply, MvPolynomial.lcoeff_apply,
      LinearMap.proj_apply, assemble, LinearMap.sum_apply, map_sum, LinearMap.smulRight_apply,
      map_smul]
    change (∑ j, φ (matrix m centers f g columns row j) * v j) = _
    simp only [constraint, firstOrderGlobalConstraint, LinearMap.pi_apply,
      firstOrderLocalConstraintAt, LinearMap.domRestrict_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [matrix_entry_eq_coeff_localConstraintAt, ← MvPolynomial.coeff_map,
      map_localConstraintAt]
    simp [monomial, SourceColumn.polynomial, mul_comm]
  let _ : Module.Finite K V := Module.Finite.of_basis (firstOrderSpaceBasis K D A m M μ)
  change Module.finrank K mat.mulVecLin.range ≤ _
  rw [hfactor]
  apply (finrank_range_comp_le_outer (coefficients ∘ₗ constraint) assemble).trans
  rw [LinearMap.range_comp]
  apply (Submodule.finrank_map_le coefficients constraint.range).trans
  simpa [constraint] using
    (finrank_firstOrderGlobalConstraint_le (A := A) (m := m) (M := M) (μ := μ) hD
      (fun i ↦ φ (Polynomial.C (centers i)))
      (fun i ↦ φ (receivedLine (f i) (g i))))

end ReedSolomon.HiddenDerivative
