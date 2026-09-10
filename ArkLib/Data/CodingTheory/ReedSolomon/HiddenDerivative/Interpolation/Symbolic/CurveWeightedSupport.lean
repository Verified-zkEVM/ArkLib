/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Soundness

/-!
# Weighted-support rank bounds for received polynomial curves

The local rank estimate is independent of the degree of the received polynomial. Over the
rational-function field each local block is a column restriction of the canonical support matrix.
Thus the same dimension surplus used for lines constructs a primitive curve interpolant;
only the coefficient-height estimate acquires the batching-degree factor.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

variable {F : Type*} [Field F] {d D m W n N : ℕ} {L : ℝ}

/-- Each curve block is a restriction of the canonical local band matrix over `F(Z)`. -/
theorem block_eq_canonical_submatrix (hD : 0 < D) (centers : Fin n → F)
    (w : Fin n → F[X]) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (i : Fin n) :
    (fun row j ↦ algebraMap F[X] (RatFunc F)
      (constraintMatrix m centers w columns (i, row) j) :
      Matrix (LowContactIndex d m) (Fin N) (RatFunc F)) =
    (weightedSupportLocalCoordinateMatrix (R := RatFunc F) (d := d) (m := m)
      (W := W) (L := L) hD
      (algebraMap F[X] (RatFunc F) (C (centers i)))
      (algebraMap F[X] (RatFunc F) (w i))).submatrix
        id (weightedSupportColumnIndex hD columns hband) := by
  ext row j
  simp only [Matrix.submatrix_apply, id_eq, constraintMatrix,
    weightedSupportLocalCoordinateMatrix_apply, weightedSupportColumnIndex, SourceColumn.polynomial]
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp

/-- The full symbolic curve matrix has rank at most the sum of the constant local ranks. -/
theorem constraintMatrix_rank_le (hD : 0 < D) (centers : Fin n → F)
    (w : Fin n → F[X]) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) :
    ((constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))).rank ≤
      n * Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
  let A := (constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))
  calc
    A.rank ≤ ∑ i, (SymbolicWeightedSupportInterpolation.Matrix.rowBlock A i).rank :=
      SymbolicWeightedSupportInterpolation.Matrix.rank_prod_rows_le_sum A
    _ ≤ ∑ _ : Fin n, Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
      apply Finset.sum_le_sum
      intro i _
      change Matrix.rank (fun row j ↦ algebraMap F[X] (RatFunc F)
        (constraintMatrix m centers w columns (i, row) j)) ≤ _
      rw [block_eq_canonical_submatrix hD centers w columns hband i]
      exact (Matrix.rank_submatrix_le _ id (weightedSupportColumnIndex hD columns hband)).trans
        (rank_weightedSupportLocalCoordinateMatrix_le_base_actual (F := F) hD
          (algebraMap F[X] (RatFunc F) (C (centers i)))
          (algebraMap F[X] (RatFunc F) (w i)))
    _ = _ := by simp

/-- Finite support reduction cannot increase the rational-function rank. -/
theorem finiteConstraintMatrix_rank_le (m : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (columns : Fin N → SourceColumn d) :
    ((finiteConstraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))).rank ≤
      ((constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))).rank := by
  let A := (constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))
  let rows := fun i ↦
    ((Fintype.equivFin {r // r ∈ supportedRows m centers w columns}).symm i).1
  change (A.submatrix rows (Equiv.refl _)).rank ≤ A.rank
  rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_submatrix, LinearMap.range_comp,
    LinearMap.range_comp,
    show LinearMap.funLeft (RatFunc F) (RatFunc F) (Equiv.refl (Fin N)).symm =
      LinearEquiv.funCongrLeft (RatFunc F) (RatFunc F) (Equiv.refl (Fin N)).symm from rfl,
    LinearEquiv.range, Submodule.map_top]
  exact Submodule.finrank_map_le _ _

/-- A weighted-support dimension surplus gives a primitive symbolic curve interpolant without any
unproved rank hypothesis. Its coefficient-height bound is linear in batching degree `ℓ`. -/
theorem exists_primitive_weightedSupport_interpolant (hD : 0 < D) (ℓ ν : ℕ)
    (centers : Fin n → F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (hmargin : n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := L) m hD 0 0)) < N) :
    let r := n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := L) m hD 0 0))
    ∃ v : Fin N → F[X], v ≠ 0 ∧
      (∀ j, (v j).natDegree ≤ r * (ℓ * ν) / (N - r)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i) (interpolant columns v) := by
  apply exists_primitive_interpolant_of_rank_le m ℓ ν _ centers w hw columns hcolumns hy₀
  · exact (finiteConstraintMatrix_rank_le m centers w columns).trans
      (constraintMatrix_rank_le hD centers w columns hband)
  · exact hmargin

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
