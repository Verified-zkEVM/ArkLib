/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Counting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.RankProduct
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Symbolic rank bounds from derivative-order support

If each source monomial has derivative-order weight at most `W`, one local constraint block has
rank at most `localDerivativeCoordinateBudget d m W`. Stacking blocks over `n` received points
gives the corresponding total rank bound, including when the received values are polynomials in a
symbolic challenge.

## Main statements

* `monomial_local_matrix_rank_le`: the rank bound for one local block.
* `symbolicLocalConstraintMatrix_rank_le_partition`: the bound for a symbolic curve.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential
open scoped BigOperators Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

/-- A local coefficient matrix on monomials of derivative-order weight at most `W` has rank at
most `localDerivativeCoordinateBudget d m W`. -/
theorem monomial_local_matrix_rank_le {F : Type*} [Field F] {d m W N : ℕ}
    (center received : F) (columns : Fin N → SourceColumn d)
    (hweight : ∀ j, fullDerivativeJetWeight (columns j).exponent ≤ W) :
    Matrix.rank (fun row j ↦ localConstraintCoordinatesAt m center received
      (MvPolynomial.monomial (columns j).exponent 1) row :
      Matrix (LowContactIndex d m) (Fin N) F) ≤ localDerivativeCoordinateBudget d m W := by
  classical
  let M : Matrix (LowContactIndex d m) (Fin N) F := fun row j ↦
    localConstraintCoordinatesAt m center received
      (MvPolynomial.monomial (columns j).exponent 1) row
  let s := localDerivativeExponents d m W
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport F (s : Set (LocalVariable d →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  let f := lowContactCoefficients (R := F) (d := d) m
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  change M.rank ≤ localDerivativeCoordinateBudget d m W
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan : Submodule.span F (Set.range M.col) ≤ V.map f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨localConstraintAt m center received
      (MvPolynomial.monomial (columns j).exponent 1), ?_, ?_⟩
    · change localConstraintAt m center received
        (MvPolynomial.monomial (columns j).exponent 1) ∈
          MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro e he
      have hmonomial : ∀ u ∈ (MvPolynomial.monomial (columns j).exponent (1 : F)).support,
          fullDerivativeJetWeight u ≤ W := by
        intro u hu
        have heq : u = (columns j).exponent := by
          simpa using MvPolynomial.support_monomial_subset hu
        simpa [heq] using hweight j
      obtain ⟨hb, hw, hc⟩ := localConstraintAt_support_of_derivative_weight center received
        hmonomial he
      exact mem_localDerivativeExponents_of_bounds hb hw hc
    · ext row
      change f (localConstraintAt m center received
        (MvPolynomial.monomial (columns j).exponent 1)) row = M row j
      have hrow : Finsupp.weight (localContactWeight d) row.1 < m := by
        exact row.2
      simp [M, f, localConstraintCoordinatesAt, localConstraintAt,
        lowContactCoefficients, projectLowContact, hrow]
  calc
    Module.finrank F (Submodule.span F (Set.range M.col)) ≤ Module.finrank F (V.map f) :=
      Submodule.finrank_mono hspan
    _ ≤ Module.finrank F V := Submodule.finrank_map_le _ _
    _ = s.card := hdim
    _ ≤ localDerivativeCoordinateBudget d m W := card_localDerivativeExponents_le d m W

private theorem mapped_symbolic_curve_block_eq_local_matrix {F : Type*} [Field F]
    {d m n N : ℕ} (centers : Fin n → F) (w : Fin n → F[X])
    (columns : Fin N → SourceColumn d) (i : Fin n) :
    (fun row j ↦ algebraMap F[X] (RatFunc F)
      (localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns (i, row) j)) =
      (fun row j ↦ localConstraintCoordinatesAt m
        (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (algebraMap F[X] (RatFunc F) (w i))
        (MvPolynomial.monomial (columns j).exponent 1) row) := by
  ext row j
  simp only [localConstraintMatrix, localConstraintCoordinatesAt,
    lowContactCoefficients, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]

/-- The symbolic local constraint matrix has rank at most `n` times the local derivative budget
when every source monomial has derivative-order weight at most `W`. -/
theorem symbolicLocalConstraintMatrix_rank_le_partition {F : Type*} [Field F]
    {d m W n N : ℕ} (centers : Fin n → F) (w : Fin n → F[X])
    (columns : Fin N → SourceColumn d)
    (hweight : ∀ j, fullDerivativeJetWeight (columns j).exponent ≤ W) :
    ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * localDerivativeCoordinateBudget d m W := by
  let M := (localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns).map
    (algebraMap F[X] (RatFunc F))
  apply (Matrix.rank_prod_rows_le_sum M).trans
  calc
    ∑ i : Fin n, (Matrix.rowBlock M i).rank ≤
        ∑ _i : Fin n, localDerivativeCoordinateBudget d m W := by
      apply Finset.sum_le_sum
      intro i _
      change Matrix.rank (fun row j ↦ algebraMap F[X] (RatFunc F)
        (localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns (i, row) j)) ≤ _
      rw [mapped_symbolic_curve_block_eq_local_matrix centers w columns i]
      exact monomial_local_matrix_rank_le _ _ columns hweight
    _ = _ := by simp

end ReedSolomon.HiddenDerivative
