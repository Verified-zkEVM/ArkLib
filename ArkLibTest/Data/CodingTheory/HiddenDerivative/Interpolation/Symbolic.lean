/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ChallengeDegree
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ColumnHeight
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveHeight
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.PartitionRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Soundness
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.JohnsonCertificate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupportCertificate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedJohnsonCertificate
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Symbolic interpolation acceptance cases

Small concrete cases for coefficient bounds, substitutions, source-column interpolation,
weighted-support rank, and certificate construction.
-/

open Finset MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.WeightedSupportParameters

open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
open scoped Polynomial Matrix

example : ((unscaledLocalSubstitution 0 (Polynomial.C (0 : ℚ)) Polynomial.X
    (SourceColumn.polynomial (R := ℚ[X]) ⟨0, 2, ![]⟩)).coeff 0).natDegree ≤ 2 ∧
    (unscaledLocalSubstitution 0 (Polynomial.C (0 : ℚ)) Polynomial.X
      (SourceColumn.polynomial (R := ℚ[X]) ⟨0, 2, ![]⟩)).coeff 0 = Polynomial.X ^ 2 := by
  have hcoeff : (unscaledLocalSubstitution 0 (Polynomial.C (0 : ℚ)) Polynomial.X
      (SourceColumn.polynomial (R := ℚ[X]) ⟨0, 2, ![]⟩)).coeff 0 = Polynomial.X ^ 2 := by
    rw [SourceColumn.polynomial_eq_sourceMonomial]
    rw [sourceMonomial]
    simp only [map_mul, map_pow, unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero]
    rw [← constantCoeff_eq]
    simp [localCorrection]
  exact ⟨SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le
    (R := ℚ) (ℓ := 1) (a := 0) (received := Polynomial.X) (by norm_num)
    (⟨0, 2, ![]⟩ : SourceColumn 0) 0, hcoeff⟩

private noncomputable def matrixRowE : Fin 1 × LowContactIndex 0 1 :=
  (0, ⟨Finsupp.single (localE 0) 2, by simp [localContactOrder_eq, localT, localAux]⟩)

private def matrixColumnY : Fin 1 → SourceColumn 0 := fun _ => ⟨0, 1, ![]⟩

private def matrixRowZero : Fin 1 × LowContactIndex 0 1 :=
  (0, ⟨0, by simp [localContactOrder]⟩)

example : localConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 1)
    matrixColumnY matrixRowZero 0 = 1 := by
  rw [localConstraintMatrix_apply]
  rw [show matrixRowZero.2.1 = (0 : LocalVariable 0 →₀ ℕ) by rfl]
  have hcolumn : (matrixColumnY 0).polynomial =
      (X (some 0) : DifferentialPolynomial ℚ 0) := by
    simpa [matrixColumnY, sourceMonomial] using
      (SourceColumn.polynomial_eq_sourceMonomial (matrixColumnY 0))
  rw [hcolumn]
  rw [unscaledLocalSubstitution_Y_zero]
  rw [← constantCoeff_eq]
  simp [localCorrection]

example : localConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0)
    matrixColumnY matrixRowE 0 = 0 :=
  localConstraintMatrix_eq_zero_of_lt 1 _ _ matrixColumnY matrixRowE 0
    (by simp [matrixColumnY, matrixRowE, Finsupp.weight_single, localJetDegreeWeight, localAux])

example :
    1 * (curveInterpolationHeight 3 4 + 1) <
      ∑ i ∈ ({0, 1} : Finset (Fin 2)),
        ![1, 2] i * (curveInterpolationHeight 3 4 + 1 - 3 * ![0, 2] i) :=
  curveInterpolationHeight_preserves_certificate _ ![1, 2] ![0, 2] 1 4 3 (by decide)

private def sourceColumns : Fin 2 → SourceColumn 1 := ![⟨0, 1, ![0]⟩, ⟨1, 0, ![0]⟩]

private theorem sourceColumnsInjective : Function.Injective sourceColumns := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [sourceColumns]

example :
    (SourceColumn.interpolant sourceColumns ![(5 : ℚ), 7]).coeff (sourceColumns 1).exponent = 7 :=
  SourceColumn.coeff_interpolant sourceColumnsInjective _ 1

example : MvPolynomial.map (Int.castRingHom (ZMod 2))
    (SourceColumn.interpolant sourceColumns ![(2 : ℤ), 3]) ≠ 0 := by
  refine SourceColumn.map_interpolant_ne_zero sourceColumnsInjective _ fun h => ?_
  have h1 : ((3 : ℤ) : ZMod 2) = 0 := by simpa using congrFun h 1
  exact absurd h1 (by decide)
private theorem onePointLocalRank_le_two :
    Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) ≤ 2 := by
  calc
    _ ≤ localResidualCoordinateBudget 1 1 0 ⌈(2 : ℝ) / 1⌉₊ := by
      simpa using (finrank_weightedSupportLocalConstraint_le (F := ℚ) (d := 1) (D := 1)
        (W := 0) (L := 2) (m := 1) (by norm_num) Nat.one_pos (0 : ℚ) 0)
    _ ≤ 2 := by
      norm_num [localResidualCoordinateBudget, contactThreshold, Finset.natWeightedSimplex]
example :
    (weightedSupportLocalCoordinateMatrix (R := RatFunc ℚ) (d := 1) (D := 2) (W := 0) (L := 2)
      1 (by norm_num) 1 2).rank ≤
      Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (D := 2) (W := 0) (L := 2)
          1 (by norm_num) 0 0)) := by
  exact rank_weightedSupportLocalCoordinateMatrix_le_base_actual
    (F := ℚ) (E := RatFunc ℚ) (d := 1) (D := 2) (W := 0) (L := 2) 1 (by norm_num) 1 2
private def twoPointEmbedding : Fin 2 ↪ ℚ where
  toFun := fun i => (i.val : ℚ)
  inj' := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at hij
    exact_mod_cast hij

private theorem twoPointLocalRank_le_eight {F : Type*} [Field F] :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := 1) (W := 0) (L := 4) 2
        Nat.one_pos 0 0)) ≤ 8 := by
  calc
    _ ≤ localResidualCoordinateBudget 1 2 0 ⌈(4 : ℝ) / 1⌉₊ := by
      simpa using (finrank_weightedSupportLocalConstraint_le (F := F) (d := 1) (D := 1)
        (W := 0) (L := 4) (m := 2) (by norm_num) Nat.one_pos (0 : F) 0)
    _ ≤ 8 := by
      norm_num [localResidualCoordinateBudget, contactThreshold, Finset.natWeightedSimplex,
        Nat.ceilDiv_eq_add_pred_div]

private theorem twoPointSupportDimension_ge_twenty {F : Type*} [Field F] :
    20 ≤ Module.finrank F (weightedSupportSpace F 1 1 0 4 Nat.one_pos) := by
  have h := sum_count_le_finrank_weightedSupportSpace F (d := 1) (D := 1) (W := 0)
    (L := 4) (by decide) Nat.one_pos
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by
    decide
  have h4 : ⌈(4 : ℝ)⌉₊ = 4 := by exact_mod_cast Nat.ceil_natCast 4
  rw [hs, sum_singleton] at h
  norm_num [CubicStaircase.count, h4] at h
  exact h

private theorem twoPointFixedMargin {F : Type*} [Field F] :
    (543 / 500 : ℝ) * Fintype.card (Fin 2) * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := 1) (W := 0) (L := 4) 2
        Nat.one_pos 0 0)) < Module.finrank F (weightedSupportSpace F 1 1 0 4 Nat.one_pos) := by
  have hrank : (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := 1) (W := 0) (L := 4) 2
        Nat.one_pos 0 0)) : ℝ) ≤ 8 := by
    exact_mod_cast twoPointLocalRank_le_eight (F := F)
  have hdim : (20 : ℝ) ≤ Module.finrank F (weightedSupportSpace F 1 1 0 4 Nat.one_pos) := by
    exact_mod_cast twoPointSupportDimension_ge_twenty (F := F)
  have hmargin : (543 / 500 : ℝ) * 2 *
      (Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := 1) (W := 0) (L := 4) 2
          Nat.one_pos 0 0)) : ℝ) <
        Module.finrank F (weightedSupportSpace F 1 1 0 4 Nat.one_pos) := by
    nlinarith [hrank, hdim]
  exact_mod_cast hmargin

/-- The fixed-margin construction gives a certificate with a feasible two-point threshold. -/
example : ∃ cert : SymbolicReceivedCurve.Certificate 2 1 1 3 1 35 twoPointEmbedding
    (fun _ => receivedLine 0 0), ∃ stages terminal, SeparantChain cert.Q stages terminal := by
  obtain ⟨cert⟩ := exists_weightedSupport_certificate_of_fixed_margin
    (F := ℚ) (D := 1) (d := 1)
    (W := 0) (m := 2) (A := 2) (k := 1) (g₀ := 1) Nat.one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) twoPointEmbedding
    (fun _ => 0) (fun _ => 0) (by
      have hmargin := twoPointFixedMargin (F := ℚ)
      have hcut : ((1 : ℕ) : ℝ) * 2 * (1 + (1 : ℝ)) = 4 := by norm_num
      rw [← hcut] at hmargin
      exact hmargin)
  exact ⟨cert, cert.exists_separantChain (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))⟩

/-- The fixed-margin construction also accepts a quadratic received curve. -/
example : Nonempty (SymbolicReceivedCurve.Certificate 2 1 2 3 1 71 twoPointEmbedding
    (fun _ : Fin 2 => Polynomial.X ^ 2 + 1)) := by
  have hmargin := twoPointFixedMargin (F := ℚ)
  have hcut : ((1 : ℕ) : ℝ) * 2 * (1 + (1 : ℝ)) = 4 := by norm_num
  rw [← hcut] at hmargin
  exact SymbolicReceivedCurve.exists_certificate_of_fixed_margin
    (F := ℚ) (d := 1) (D := 1) (m := 2) (W := 0) (A := 2) (k := 1) (ℓ := 2)
    (g₀ := 1) Nat.one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) twoPointEmbedding (fun _ => Polynomial.X ^ 2 + 1)
    (by intro i; norm_num) hmargin

private noncomputable def twoPointWeightedColumns : Fin (Fintype.card
    (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))) → SourceColumn 1 :=
  weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos

private theorem twoPointWeightedColumns_eligible : ∀ j, WeightedSupportEligible 1 1 0 2
    (twoPointWeightedColumns j).exponent :=
  weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos
example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => Polynomial.X ^ 2 + 1) twoPointWeightedColumns).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 2 := by
  calc
    _ ≤ Fintype.card (Fin 1) * Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) := by
      exact localConstraintMatrix_rank_le_weightedSupport Nat.one_pos
        (fun _ : Fin 1 => 0) (fun _ : Fin 1 => Polynomial.X ^ 2 + 1)
        twoPointWeightedColumns twoPointWeightedColumns_eligible
    _ ≤ 2 := by
      simpa [Fintype.card_fin] using onePointLocalRank_le_two
example : ∀ u, ((SourceColumn.interpolant sourceColumns
    ![(Polynomial.X : ℚ[X]), 1]).coeff u).natDegree < 2 := by
  have hbound : ∀ u, ((SourceColumn.interpolant sourceColumns
      ![(Polynomial.X : ℚ[X]), 1]).coeff u).natDegree ≤ 2 - 1 :=
    SourceColumn.coeff_interpolant_natDegree_le (h := 2 - 1) sourceColumns
      sourceColumnsInjective ![(Polynomial.X : ℚ[X]), 1]
      (by intro j; fin_cases j <;> norm_num [sourceColumns])
  intro u
  have h := hbound u
  omega

/-- The weighted cutoff bounds both the interpolant support and its challenge specialization. -/
example :
    (∀ u ∈ (SourceColumn.interpolant twoPointWeightedColumns
      (fun _ : Fin (Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))) =>
        (1 : ℚ[X]))).support, totalJetDegree u ≤ 1) ∧
      jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) (0 : ℚ))
        (SourceColumn.interpolant twoPointWeightedColumns
          (fun _ : Fin (Fintype.card
            (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))) => (1 : ℚ[X])))) ≤ 1 := by
  have hband : ∀ j, WeightedSupportEligible 1 1 0
      (((1 : ℕ) : ℝ) * (1 : ℕ) * (1 + (1 : ℝ)))
      (twoPointWeightedColumns j).exponent := by
    intro j
    have hcut : ((1 : ℕ) : ℝ) * (1 : ℕ) * (1 + (1 : ℝ)) = 2 := by norm_num
    simpa only [hcut] using twoPointWeightedColumns_eligible j
  have hdegree : ∀ j, totalJetDegree (twoPointWeightedColumns j).exponent ≤ 1 := by
    intro j
    have h := totalJetDegree_le_pred_of_weightedSupportEligible (D := 1) (d := 1)
      (W := 0) (t := 2) Nat.one_pos (by norm_num) (hband j)
    simpa using h
  exact ⟨SourceColumn.interpolant_totalJetDegree_le twoPointWeightedColumns hdegree
      (fun _ => 1),
    SourceColumn.map_interpolant_jetTotalDegree_le
      (Polynomial.eval₂RingHom (RingHom.id ℚ) 0) twoPointWeightedColumns hdegree
      (fun _ => 1)⟩
example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => receivedLine (0 : ℚ) 0)
      (weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos)).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 2 := by
  calc
    _ ≤ 1 * Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) := by
      exact receivedLine_matrix_rank_le_base_actual (F := ℚ) (d := 1) (D := 1) (W := 0)
        (L := 2) (m := 1) Nat.one_pos (fun _ => 0) (fun _ => 0) (fun _ => 0) _
        (weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos)
    _ ≤ 2 := by simpa using onePointLocalRank_le_two
private def constructionColumns : Fin 2 → SourceColumn 1 :=
  ![⟨0, 0, ![0]⟩, ⟨0, 1, ![0]⟩]

private theorem constructionColumnsInjective : Function.Injective constructionColumns := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [constructionColumns]

private def constructionRow : Fin 1 × LowContactIndex 1 1 :=
  (0, ⟨0, by simp [localContactOrder]⟩)

private noncomputable def constructionConstraintMatrix (received : Fin 1 → ℚ[X]) :=
  localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ)) received constructionColumns

private theorem constructionConstraintMatrix_constant_entry (received : Fin 1 → ℚ[X]) :
    constructionConstraintMatrix received constructionRow 0 = 1 := by
  rw [constructionConstraintMatrix, localConstraintMatrix_apply]
  simp [constructionRow, constructionColumns, SourceColumn.polynomial, SourceColumn.exponent]

private theorem constructionColumnsDerivativeWeight : ∀ j,
    fullDerivativeJetWeight (constructionColumns j).exponent ≤ 0 := by
  intro j
  fin_cases j <;> change (constructionColumns _).exponent.weight jetDerivativeWeight ≤ 0 <;>
    rw [SourceColumn.weight_exponent] <;>
      simp [jetDerivativeWeight, constructionColumns]

private theorem constructionConstraintMatrix_rank_one (received : Fin 1 → ℚ[X]) :
    ((constructionConstraintMatrix received).map (algebraMap ℚ[X] (RatFunc ℚ))).rank = 1 := by
  have hbudget : localDerivativeCoordinateBudget 1 1 0 = 1 := by decide
  have hle : ((constructionConstraintMatrix received).map
      (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 := by
    change ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ)) received
      constructionColumns).map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1
    rw [← rank_map_supportedLocalConstraintMatrix (algebraMap ℚ[X] (RatFunc ℚ)) 1 _ _ _]
    simpa [hbudget] using
      (rank_map_supportedLocalConstraintMatrix_le_of_derivative_weight (F := ℚ) (d := 1)
        (m := 1) (W := 0) (centers := fun _ => 0) (received := received) constructionColumns
        constructionColumnsDerivativeWeight)
  let r : Fin 1 → Fin 1 × LowContactIndex 1 1 := fun _ => constructionRow
  let c : Fin 1 → Fin 2 := fun _ => 0
  have hminor : ((constructionConstraintMatrix received).map
      (algebraMap ℚ[X] (RatFunc ℚ))).submatrix r c = (1 : Matrix (Fin 1) (Fin 1) (RatFunc ℚ)) := by
    ext i j
    fin_cases i
    fin_cases j
    rw [Matrix.submatrix_apply, Matrix.map_apply]
    change algebraMap ℚ[X] (RatFunc ℚ) (constructionConstraintMatrix received constructionRow 0) = 1
    rw [constructionConstraintMatrix_constant_entry]
    simp
  have hge : 1 ≤ ((constructionConstraintMatrix received).map
      (algebraMap ℚ[X] (RatFunc ℚ))).rank := by
    have h := Matrix.rank_submatrix_le ((constructionConstraintMatrix received).map
      (algebraMap ℚ[X] (RatFunc ℚ))) r c
    rw [hminor, Matrix.rank_one] at h
    simpa using h
  exact Nat.le_antisymm hle hge

private theorem constructionRow_supported (received : Fin 1 → ℚ[X]) :
    constructionRow ∈ localConstraintSupportedRows 1
      (fun _ : Fin 1 => Polynomial.C (0 : ℚ)) received constructionColumns := by
  apply (mem_localConstraintSupportedRows_iff 1 _ _ _ constructionRow).mpr
  refine ⟨0, ?_⟩
  change constructionConstraintMatrix received constructionRow 0 ≠ 0
  rw [constructionConstraintMatrix_constant_entry]
  norm_num

example : ∃ v : Fin 2 → ℚ[X], v ≠ 0 ∧
    (∀ j, (v j).natDegree ≤ 1 - (constructionColumns j).y₀) ∧
    Ideal.span (Set.range v) = ⊤ ∧
    (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : ℚ[X] →+* S),
      MvPolynomial.map ψ (SourceColumn.interpolant constructionColumns v) ≠ 0) ∧
    ∀ _ : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ))
      (receivedLine (0 : ℚ) 1) (SourceColumn.interpolant constructionColumns v) := by
  have hsurplus : 1 * (1 + 1) <
      ∑ j : Fin 2, (1 + 1 - 1 * (constructionColumns j).y₀) := by decide
  obtain ⟨v, hv, hvdeg, hspan, hmap, hconstraints⟩ :=
    exists_primitive_receivedLine_interpolant_of_column_height (m := 1) (h := 1)
      (centers := fun _ : Fin 1 => (0 : ℚ)) (f := fun _ => 0) (g := fun _ => 1)
      constructionColumns constructionColumnsInjective (algebraMap ℚ[X] (RatFunc ℚ))
      (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) (s := 1)
      (constructionConstraintMatrix_rank_one (fun _ => receivedLine (0 : ℚ) 1)).le hsurplus
  refine ⟨v, hv, ?_, hspan, hmap, hconstraints⟩
  intro j
  fin_cases j
  · simpa [constructionColumns] using
      (Polynomial.natDegree_le_of_mem_degreeLT_succ (hvdeg 0))
  · simpa [constructionColumns] using
      (Polynomial.natDegree_le_of_mem_degreeLT_succ (hvdeg 1))

example : ∃ v : Fin 2 → ℚ[X], v ≠ 0 ∧ (∀ j, (v j).natDegree ≤ 1) ∧
    Ideal.span (Set.range v) = ⊤ ∧
    (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : ℚ[X] →+* S),
      MvPolynomial.map ψ (SourceColumn.interpolant constructionColumns v) ≠ 0) ∧
    ∀ _ : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ))
      (receivedLine (0 : ℚ) 1) (SourceColumn.interpolant constructionColumns v) := by
  obtain ⟨v, hv, hdegree, hspan, hmap, hconstraints⟩ :=
    exists_primitive_receivedLine_interpolant_of_rank_le (m := 1) (ν := 1)
      (centers := fun _ : Fin 1 => (0 : ℚ)) (f := fun _ => 0) (g := fun _ => 1)
      constructionColumns constructionColumnsInjective
      (by intro j; fin_cases j <;> norm_num [constructionColumns])
      (algebraMap ℚ[X] (RatFunc ℚ)) (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) (s := 1)
      (constructionConstraintMatrix_rank_one (fun _ => receivedLine (0 : ℚ) 1)).le (by decide)
  exact ⟨v, hv, hdegree, hspan, hmap, hconstraints⟩

example : constructionConstraintMatrix (fun _ => 0) constructionRow 0 = 1 ∧
    constructionRow ∈ localConstraintSupportedRows 1
      (fun _ : Fin 1 => Polynomial.C (0 : ℚ)) (fun _ => 0) constructionColumns ∧
    ((supportedLocalConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => (0 : ℚ[X])) constructionColumns).map
      (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 * localDerivativeCoordinateBudget 1 1 0 := by
  have hbudget : localDerivativeCoordinateBudget 1 1 0 = 1 := by decide
  refine ⟨constructionConstraintMatrix_constant_entry _, constructionRow_supported _, ?_⟩
  simpa [hbudget] using
    (rank_map_supportedLocalConstraintMatrix_le_of_derivative_weight
      (F := ℚ) (d := 1) (m := 1) (W := 0) (centers := fun _ => 0)
      (received := fun _ => 0) constructionColumns constructionColumnsDerivativeWeight)
private def nonzeroSupportColumns : Fin 1 → SourceColumn 1 :=
  fun _ => ⟨0, 1, fun _ => 0⟩

example : MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0)
    (SourceColumn.interpolant nonzeroSupportColumns
      (fun _ => (Polynomial.X + 1 : ℚ[X]))) ∈
      weightedSupportSpace ℚ 1 1 0 2 (by norm_num) := by
  exact map_interpolant_mem_weightedSupportSpace (D := 1) (d := 1) (W := 0) (L := 2)
    (by norm_num) nonzeroSupportColumns
    (by
      intro j
      fin_cases j
      simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree,
        nonzeroSupportColumns, SourceColumn.exponent, Finsupp.weight_single,
        jetHigherWeight, jetDegreeWeight])
    (fun _ => Polynomial.X + 1) (RingHom.id ℚ) 0

private def sixteenPointEmbedding : Fin 16 ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at hij
    exact_mod_cast hij

private noncomputable def johnsonKernelCoefficients :
    Fin (Fintype.card (JohnsonColumnIndex 2 1 0)) → ℚ[X] :=
  fun _ => 1

private theorem johnsonKernelInterpolant_eq :
    SourceColumn.interpolant (johnsonColumns 2 1 0) johnsonKernelCoefficients =
      (1 + (X none : DifferentialPolynomial ℚ[X] 0)) := by
  classical
  let e := Fintype.equivFin (JohnsonColumnIndex 2 1 0)
  rw [SourceColumn.interpolant, ← e.sum_comp]
  have hcoord (q : JohnsonColumnIndex 2 1 0) :
      (Fintype.equivFin (JohnsonColumnIndex 2 1 0)).symm (e q) = q := by
    change e.symm (e q) = q
    exact e.symm_apply_apply q
  simp_rw [johnsonColumns]
  rw [Fintype.sum_sigma]
  simp only [johnsonKernelCoefficients, SourceColumn.exponent, Nat.reduceAdd, univ_unique,
    Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero, sum_singleton, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Nat.mul_zero, Nat.sub_zero, Fin.sum_univ_two]
  rw [hcoord ⟨0, 0⟩, hcoord ⟨0, 1⟩]
  simp only [Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mul_zero,
    Nat.sub_zero, Finsupp.single_zero, add_zero, univ_eq_empty, sum_empty, monomial_zero', C_1,
    Nat.mod_succ, add_right_inj]
  simpa using (MvPolynomial.X_pow_eq_monomial (n := none) (e := 1) :
    (X none : DifferentialPolynomial ℚ[X] 0) ^ 1 =
      MvPolynomial.monomial (Finsupp.single none 1) 1).symm

private theorem johnsonKernelLocalConstraints :
    SatisfiesLocalConstraints 1 (Polynomial.C (-1 : ℚ)) (0 : ℚ[X])
      (SourceColumn.interpolant (johnsonColumns 2 1 0) johnsonKernelCoefficients) := by
  rw [johnsonKernelInterpolant_eq, satisfiesLocalConstraints_iff_coeff_eq_zero]
  intro e he
  have hT : e (localT 0) = 0 := by
    have horder : localContactOrder 0 e = e (localT 0) := by
      rw [localContactOrder_eq]
      simp [localT, localE, localAux]
    rw [horder] at he
    omega
  have hsub : unscaledLocalSubstitution 0 (Polynomial.C (-1 : ℚ)) (0 : ℚ[X])
      (1 + (X none : DifferentialPolynomial ℚ[X] 0)) = X (localT 0) := by
    rw [map_add, map_one, unscaledLocalSubstitution_X]
    simp [localT]
  rw [hsub]
  have hsingle : Finsupp.single (localT 0) 1 ≠ e := by
    intro h
    have h' : 1 = e (localT 0) := by
      simpa [localT] using congrArg (fun u => u (localT 0)) h
    rw [hT] at h'
    norm_num at h'
  simp [MvPolynomial.coeff_X, hsingle]

/-- A nonzero concrete coefficient vector lies in the Johnson matrix kernel. -/
example : johnsonConstraintMatrix 2 1 0 1 (fun _ : Fin 1 => -1) (fun _ => 0) *ᵥ
    johnsonKernelCoefficients = 0 ∧ johnsonKernelCoefficients ≠ 0 := by
  constructor
  · exact (johnsonConstraintMatrix_kernel_iff 2 1 0 1 (fun _ : Fin 1 => -1)
      (fun _ => 0) johnsonKernelCoefficients).2 (by
        intro i
        fin_cases i
        exact johnsonKernelLocalConstraints)
  · intro h
    have h0 := congrFun h ⟨0, by norm_num [johnsonKernelCoefficients]⟩
    simp [johnsonKernelCoefficients] at h0

private def agreementSoundnessColumns : Fin 1 → SourceColumn 0 := fun _ => ⟨0, 1, ![]⟩

private theorem agreementSoundnessInterpolant_eq :
    SourceColumn.interpolant agreementSoundnessColumns (fun _ => (1 : ℚ[X])) =
      (X (some 0) : DifferentialPolynomial ℚ[X] 0) := by
  simp [SourceColumn.interpolant, agreementSoundnessColumns, SourceColumn.exponent,
    MvPolynomial.X]

private theorem agreementSoundnessColumn_eligible : ∀ j,
    WeightedSupportEligible 1 0 0 2 (agreementSoundnessColumns j).exponent := by
  intro j
  fin_cases j
  simp [WeightedSupportEligible, agreementSoundnessColumns, SourceColumn.exponent,
    fullHigherJetWeight, jetHigherWeight, totalJetDegree_eq_sum, Finsupp.weight_single]

private theorem agreementSoundnessLocalConstraints : ∀ i : Fin 2,
    SatisfiesLocalConstraints 1 (Polynomial.C (twoPointEmbedding i)) (0 : ℚ[X])
      (SourceColumn.interpolant agreementSoundnessColumns (fun _ => (1 : ℚ[X]))) := by
  intro i
  rw [satisfiesLocalConstraints_iff_coeff_eq_zero]
  intro e he
  have hT : e (localT 0) = 0 := by
    have horder : localContactOrder 0 e = e (localT 0) := by
      rw [localContactOrder_eq]
      simp [localT, localE, localAux]
    rw [horder] at he
    omega
  have hmon : (X (localT 0) * X (localE 0) : LocalPolynomial (ℚ[X]) 0) =
      MvPolynomial.monomial (Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1) 1 := by
    rw [← pow_one (X (localT 0)), ← pow_one (X (localE 0)),
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial]
    norm_num
  rw [agreementSoundnessInterpolant_eq, unscaledLocalSubstitution_Y_zero]
  simp only [localCorrection, map_zero, zero_add, hmon]
  have hnot : Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1 ≠ e := by
    intro h
    have h' : 1 = e (localT 0) := by
      simpa [localT, localE, localAux] using congrArg (fun u => u none) h
    rw [hT] at h'
    norm_num at h'
  simp [MvPolynomial.coeff_monomial, hnot]

/-- A nonzero order-zero equation vanishes at a concrete two-point agreement set. -/
example : differentialSpecialization
    (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) (0 : ℚ))
      (SourceColumn.interpolant agreementSoundnessColumns (fun _ => (1 : ℚ[X]))))
    (0 : ℚ[X]) = 0 := by
  exact differentialSpecialization_curve_interpolant_eq_zero_of_agreements
    (F := ℚ) (E := ℚ) (d := 0) (D := 1) (m := 1) (A := 2) (W := 0) (L := 2)
    Nat.one_pos (by norm_num) (by norm_num) twoPointEmbedding (fun _ => 0)
    agreementSoundnessColumns agreementSoundnessColumn_eligible (fun _ => 1)
    agreementSoundnessLocalConstraints (RingHom.id ℚ) 0 Finset.univ 0 (by norm_num)
    twoPointEmbedding.injective.injOn (by norm_num) (by intro i hi; simp)

/-- The received-line agreement theorem handles a concrete constant received line. -/
example : differentialSpecialization
    (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) (0 : ℚ))
      (SourceColumn.interpolant agreementSoundnessColumns (fun _ => (1 : ℚ[X]))))
    (0 : ℚ[X]) = 0 := by
  exact differentialSpecialization_map_interpolant_eq_zero_of_agreements
    (F := ℚ) (E := ℚ) (d := 0) (D := 1) (m := 1) (A := 2) (W := 0) (L := 2)
    Nat.one_pos (by norm_num) (by norm_num) twoPointEmbedding (fun _ => 0) (fun _ => 0)
    agreementSoundnessColumns agreementSoundnessColumn_eligible (fun _ => 1)
    (by simpa [receivedLine] using agreementSoundnessLocalConstraints)
    (RingHom.id ℚ) 0 Finset.univ 0 (by norm_num) twoPointEmbedding.injective.injOn
    (by norm_num) (by intro i hi; simp)

/-- The degree-`< k` form applies to the same concrete two-point agreement. -/
example : differentialSpecialization
    (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) (0 : ℚ))
      (SourceColumn.interpolant agreementSoundnessColumns (fun _ => (1 : ℚ[X]))))
    (0 : ℚ[X]) = 0 := by
  exact differentialSpecialization_map_interpolant_eq_zero_of_degree_lt
    (F := ℚ) (E := ℚ) (d := 0) (D := 1) (m := 1) (A := 2) (W := 0) (L := 2) (k := 1)
    Nat.one_pos (by norm_num) (by norm_num) (by norm_num)
    twoPointEmbedding (fun _ => 0) (fun _ => 0)
    agreementSoundnessColumns agreementSoundnessColumn_eligible (fun _ => 1)
    (by simpa [receivedLine] using agreementSoundnessLocalConstraints)
    (RingHom.id ℚ) 0 Finset.univ 0 (by norm_num) twoPointEmbedding.injective.injOn
    (by norm_num) (by intro i hi; simp)

/-- The finite Johnson construction has a concrete degree-one rational instance. -/
example : Nonempty (JohnsonSymbolicCertificate (F := ℚ) 1 6
    (johnsonM 16 1 (1 / 8 : ℝ)) (johnsonMu 16 1 (1 / 8 : ℝ)) 1
    (johnsonH 16 1 (1 / 8 : ℝ)) (johnsonXCutoff 16 1 (1 / 8 : ℝ))
    sixteenPointEmbedding (fun _ => 0) (fun _ => 0)) := by
  exact exists_johnson_symbolic_certificate (F := ℚ)
    (hD := by norm_num) (hDn := by norm_num) (heta := by norm_num)
    (hthreshold := by
      have hrho : johnsonRhoMinus 16 1 = (1 / 16 : ℝ) := by
        norm_num [johnsonRhoMinus]
      rw [johnsonAgreement, hrho]
      have hsqrt : Real.sqrt (1 / 16 : ℝ) ≤ 1 / 4 := by
        apply Real.sqrt_le_iff.mpr
        constructor <;> norm_num
      nlinarith [hsqrt])
    (hkD := by norm_num) sixteenPointEmbedding (fun _ => 0) (fun _ => 0)

namespace WeightedJohnsonCertificateTest

private def onePointEmbedding : Fin 1 ↪ ℚ where
  toFun := fun _ => 0
  inj' := by
    intro i j _
    exact Fin.ext (by omega)

/- A one-point weighted system with four source slots and two row slots has a certificate. -/
example : Nonempty (JohnsonSymbolicCertificate (F := ℚ) 1 2 2 1 1 0 4
    onePointEmbedding (fun _ => 0) (fun _ => 0)) := by
  apply exists_weighted_johnson_symbolic_certificate
  · norm_num
  · norm_num
  · norm_num
  · norm_num [johnsonSourceSlotCount]

private theorem onePointWeightedArithmeticCertificate :
    IsJohnsonWeightedCertificate 1 1 2 2 1 1 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight,
    johnsonWeightedHeightInt, johnsonWeightedMoment, johnsonWeightedSlope,
    johnsonWeightedW, johnsonWeightedN, johnsonWeightedR, johnsonWeightedU,
    johnsonWeightedT]

/- The finite arithmetic certificate also supplies the interpolation surplus. -/
example : Nonempty (JohnsonSymbolicCertificate (F := ℚ) 1 2 2 1 1 1 4
    onePointEmbedding (fun _ => 0) (fun _ => 0)) := by
  exact IsJohnsonWeightedCertificate.exists_symbolic onePointWeightedArithmeticCertificate
    (by norm_num) (by norm_num) onePointEmbedding (fun _ => 0) (fun _ => 0)

private def truncationTestColumn : JohnsonColumnIndex 3 1 0 :=
  ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩

private noncomputable def truncationTestSelected :
    Fin (Fintype.card (JohnsonColumnIndex 3 1 0)) :=
  Fintype.equivFin (JohnsonColumnIndex 3 1 0) truncationTestColumn

private noncomputable def truncationTestCoefficients :
    Fin (Fintype.card (JohnsonColumnIndex 3 1 0)) → ℚ[X] :=
  fun j ↦ if j = truncationTestSelected then 1 else 0

/- The coefficient vector for `T^2` satisfies multiplicity two after truncating to error grade
zero, with the cutoff strictly below `m - 1`. -/
example :
    (0 : ℕ) < 2 - 1 ∧
      weightedJohnsonFinMatrix 3 1 0 2 (fun _ : Fin 1 ↦ (0 : ℚ))
        (fun _ ↦ (0 : ℚ[X])) *ᵥ truncationTestCoefficients = 0 ∧
      ∀ _i : Fin 1, SatisfiesLocalConstraints 2 (Polynomial.C (0 : ℚ)) (0 : ℚ[X])
        (SourceColumn.interpolant (johnsonColumns 3 1 0) truncationTestCoefficients) := by
  have hinterp : SourceColumn.interpolant (johnsonColumns 3 1 0) truncationTestCoefficients =
      (X none : DifferentialPolynomial ℚ[X] 0) ^ 2 := by
    have hselected : (Fintype.equivFin (JohnsonColumnIndex 3 1 0)).symm
        truncationTestSelected = truncationTestColumn :=
      (Fintype.equivFin (JohnsonColumnIndex 3 1 0)).symm_apply_apply _
    have hcolumn : johnsonColumns 3 1 0 truncationTestSelected =
        (⟨2, 0, Fin.elim0⟩ : SourceColumn 0) := by
      unfold johnsonColumns
      dsimp only
      rw [hselected]
      rfl
    rw [SourceColumn.interpolant_eq_sum_smul]
    rw [Finset.sum_eq_single truncationTestSelected]
    · rw [hcolumn, SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
      simp [truncationTestCoefficients]
    · intro j _ hj
      simp [truncationTestCoefficients, hj]
    · simp
  have hconstraints : ∀ _i : Fin 1,
      SatisfiesLocalConstraints 2 (Polynomial.C (0 : ℚ)) (0 : ℚ[X])
        (SourceColumn.interpolant (johnsonColumns 3 1 0) truncationTestCoefficients) := by
    intro _i
    rw [satisfiesLocalConstraints_iff_coeff_eq_zero, hinterp]
    intro e he
    have hT : e (localT 0) < 2 := by
      rw [localContactOrder_eq] at he
      simpa [localT, localE] using he
    have hne : e ≠ Finsupp.single (localT 0) 2 := by
      intro heq
      have hvalue := congrArg (fun a : LocalVariable 0 →₀ ℕ => a (localT 0)) heq
      simp at hvalue
      omega
    simp only [map_pow, unscaledLocalSubstitution_X, map_zero, zero_add]
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    simp [Ne.symm hne]
  refine ⟨by norm_num, ?_, hconstraints⟩
  exact (weightedJohnsonFinMatrix_kernel_iff 3 1 0 2
    (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (0 : ℚ[X])) truncationTestCoefficients).2
      hconstraints

end WeightedJohnsonCertificateTest
