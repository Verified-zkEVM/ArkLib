/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rank bounds for derivative-order local constraint matrices

For any finite family of differential polynomials whose exponents have derivative-order weight at
most `W`, the matrix of low-contact coordinates at one point has rank at most
`localDerivativeCoordinateBudget d m W`. This bound applies to monomial columns and to arbitrary
polynomials. Entrywise base change commutes with the local constraint matrix, so stacking the
blocks of a symbolic received curve gives a rank bound proportional to the number of points.

## Main statements

* `localConstraintMatrix_map`: entrywise base change of the local constraint matrix.
* `localConstraintCoordinates_rank_le_of_derivative_weight`: the rank bound for a finite family
  of polynomials.
* `rank_map_supportedLocalConstraintMatrix_le_of_derivative_weight`: the bound for a finite
  symbolic matrix whose columns satisfy the derivative-weight condition.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential
open scoped Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {R : Type*} [CommRing R] {d : ℕ} {ι κ : Type*}

/-- Applying a ring homomorphism to every entry of the local constraint matrix maps its centers
and received values and leaves its source columns unchanged. -/
theorem localConstraintMatrix_map {S : Type*} [CommRing S] (f : R →+* S) (m : ℕ)
    (centers received : ι → R) (columns : κ → SourceColumn d) :
    (localConstraintMatrix m centers received columns).map f =
      localConstraintMatrix m (fun i => f (centers i)) (fun i => f (received i)) columns := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]

/-- The low-contact coordinate matrix of any finite family of differential polynomials whose
support has derivative-order weight at most `W` has rank at most
`localDerivativeCoordinateBudget d m W`. -/
theorem localConstraintCoordinates_rank_le_of_derivative_weight {F : Type*} [Field F]
    {d m W N : ℕ} (center received : F) (polynomials : Fin N → DifferentialPolynomial F d)
    (hweight : ∀ j u, u ∈ (polynomials j).support → fullDerivativeJetWeight u ≤ W) :
    Matrix.rank (fun row j => localConstraintCoordinatesAt m center received
      (polynomials j) row : Matrix (LowContactIndex d m) (Fin N) F) ≤
      localDerivativeCoordinateBudget d m W := by
  classical
  let M : Matrix (LowContactIndex d m) (Fin N) F := fun row j =>
    localConstraintCoordinatesAt m center received (polynomials j) row
  change M.rank ≤ _
  let s := localDerivativeExponents d m W
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F) (s : Set (LocalVariable d →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  let f := lowContactCoefficients (R := F) (d := d) m
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan : Submodule.span F (Set.range M.col) ≤ V.map f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨localConstraintAt m center received (polynomials j), ?_, ?_⟩
    · change localConstraintAt m center received (polynomials j) ∈
        MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro e he
      obtain ⟨hbalance, hweight', hcontact⟩ := localConstraintAt_support_of_derivative_weight
        center received (hweight j) he
      exact mem_localDerivativeExponents_of_bounds hbalance hweight' hcontact
    · ext row
      change f (localConstraintAt m center received (polynomials j)) row = M row j
      change (projectLowContact m (unscaledLocalSubstitution d center received
        (polynomials j))).coeff row.1 =
          (unscaledLocalSubstitution d center received (polynomials j)).coeff row.1
      rw [coeff_projectLowContact]
      simp [row.2]
  exact (Submodule.finrank_mono hspan).trans
    ((Submodule.finrank_map_le f V).trans
      (hdim.le.trans (card_localDerivativeExponents_le d m W)))

/-- The finite supported-row matrix of a symbolic received curve has rank at most the number of
points times the local derivative-order coordinate budget when every source column has weight at
most `W`. -/
theorem rank_map_supportedLocalConstraintMatrix_le_of_derivative_weight {F : Type*} [Field F]
    {d m W n N : ℕ} (centers : Fin n → F) (received : Fin n → F[X])
    (columns : Fin N → SourceColumn d)
    (hweight : ∀ j, fullDerivativeJetWeight (columns j).exponent ≤ W) :
    ((supportedLocalConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * localDerivativeCoordinateBudget d m W := by
  rw [rank_map_supportedLocalConstraintMatrix]
  apply (Matrix.rank_prod_rows_le_sum _).trans
  calc
    ∑ i : Fin n, Matrix.rank (fun row j =>
        ((localConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns).map
          (algebraMap F[X] (RatFunc F))) (i, row) j) ≤
        ∑ _ : Fin n, localDerivativeCoordinateBudget d m W := by
      apply Finset.sum_le_sum
      intro i hi
      change Matrix.rank (fun row j =>
        ((localConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns).map
          (algebraMap F[X] (RatFunc F))) (i, row) j) ≤ _
      rw [localConstraintMatrix_map]
      change Matrix.rank (fun row j => localConstraintCoordinatesAt m
        (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (algebraMap F[X] (RatFunc F) (received i)) (columns j).polynomial row) ≤ _
      apply localConstraintCoordinates_rank_le_of_derivative_weight
        (center := algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (received := algebraMap F[X] (RatFunc F) (received i))
        (polynomials := fun j => (columns j).polynomial)
      intro j u hu
      have heq : u = (columns j).exponent := by
        simpa using MvPolynomial.support_monomial_subset hu
      simpa [heq] using hweight j
    _ = n * localDerivativeCoordinateBudget d m W := by simp

end ReedSolomon.HiddenDerivative
