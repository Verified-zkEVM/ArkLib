/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.RankCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Rank

/-!
# Symbolic matrices for the derivative-order partition support

The local coordinate count applies over the rational-function field as well as
the base field. Every polynomial-curve block therefore has rank at most the same
integer `r₀`, and stacking n blocks costs at most `n*r₀`. No comparison to the
larger legacy weighted-support rank is needed.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation
open scoped BigOperators

/-- Selecting any monomials with derivative-order weight at most W gives the partition
local rank bound, independently of their coarse specialization cutoff. -/
theorem monomial_local_matrix_rank_le {F : Type*} [Field F] {d m W N : ℕ}
    (center received : F) (columns : Fin N → SourceColumn d)
    (hweight : ∀ j, fullDerivativeJetWeight (columns j).exponent ≤ W) :
    Matrix.rank (fun row j ↦ localConstraintCoordinatesAt m center received
      (MvPolynomial.monomial (columns j).exponent 1) row :
      Matrix (LowContactIndex d m) (Fin N) F) ≤ ratePartitionRankBound d m W := by
  classical
  let M : Matrix (LowContactIndex d m) (Fin N) F := fun row j ↦
    localConstraintCoordinatesAt m center received
      (MvPolynomial.monomial (columns j).exponent 1) row
  change M.rank ≤ _
  let s := ratePartitionLocalExponents d m W
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
    refine ⟨localConstraintAt m center received
      (MvPolynomial.monomial (columns j).exponent 1), ?_, ?_⟩
    · change localConstraintAt m center received
        (MvPolynomial.monomial (columns j).exponent 1) ∈
          MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro e he
      have hw : ∀ u ∈ (MvPolynomial.monomial (columns j).exponent (1 : F)).support,
          fullDerivativeJetWeight u ≤ W := by
        intro u hu
        have heq : u = (columns j).exponent := by
          simpa using MvPolynomial.support_monomial_subset hu
        simpa [heq] using hweight j
      obtain ⟨hb, hw, hc⟩ := localConstraint_support_of_derivative_weight center received hw he
      exact mem_ratePartitionLocalExponents_of_bounds hb hw hc
    · ext row
      change f (localConstraintAt m center received
        (MvPolynomial.monomial (columns j).exponent 1)) row = M row j
      simp [M, f, localConstraintCoordinatesAt, localConstraintAt,
        lowContactCoefficients, projectLowContact, coeff_filterLocalMonomials, row.2]
  exact (Submodule.finrank_mono hspan).trans
    ((Submodule.finrank_map_le f V).trans (hdim.le.trans
      (card_ratePartitionLocalExponents_le d m W)))

/-- Base change of a received block preserves its local coefficient interpretation. -/
theorem mapped_curve_block_eq_local_matrix {F : Type*} [Field F] {d m n N : ℕ}
    (centers : Fin n → F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn d)
    (i : Fin n) :
    (fun row j ↦ algebraMap F[X] (RatFunc F) (constraintMatrix m centers w columns (i, row) j)) =
    (fun row j ↦ localConstraintCoordinatesAt m
      (algebraMap F[X] (RatFunc F) (C (centers i)))
      (algebraMap F[X] (RatFunc F) (w i))
      (MvPolynomial.monomial (columns j).exponent 1) row) := by
  ext row j
  simp only [constraintMatrix, SourceColumn.polynomial]
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp

/-- Summing local partition counts bounds the finite symbolic interpolation matrix. -/
theorem finiteConstraintMatrix_rank_le_partition {F : Type*} [Field F] {d m W n N : ℕ}
    (centers : Fin n → F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn d)
    (hweight : ∀ j, fullDerivativeJetWeight (columns j).exponent ≤ W) :
    ((finiteConstraintMatrix m centers w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * ratePartitionRankBound d m W := by
  apply (finiteConstraintMatrix_rank_le m centers w columns).trans
  apply (Matrix.rank_prod_rows_le_sum _).trans
  calc
    ∑ i : Fin n, (Matrix.rowBlock
        ((constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))) i).rank ≤
        ∑ _ : Fin n, ratePartitionRankBound d m W := by
      apply Finset.sum_le_sum
      intro i _
      change Matrix.rank (fun row j ↦ algebraMap F[X] (RatFunc F)
        (constraintMatrix m centers w columns (i, row) j)) ≤ _
      rw [mapped_curve_block_eq_local_matrix centers w columns i]
      exact monomial_local_matrix_rank_le _ _ columns hweight
    _ = _ := by simp

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
