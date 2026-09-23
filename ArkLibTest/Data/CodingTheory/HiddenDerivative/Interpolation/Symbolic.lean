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
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Soundness
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Symbolic interpolation acceptance cases

Concrete coefficient-degree, matrix-entry, rank, height-transfer, primitive-interpolant, and
source-column cases.
-/

open Finset MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
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

private theorem onePointWeightedSupportDimension_ge_four :
    4 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
  have h := sum_count_le_finrank_weightedSupportSpace ℚ (d := 1) (D := 1) (W := 0)
    (L := 2) (by decide) Nat.one_pos
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by
    decide
  have h1 : ⌈(1 : ℝ)⌉₊ = 1 := by exact_mod_cast Nat.ceil_natCast 1
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  rw [hs, sum_singleton] at h
  norm_num [CubicStaircase.count, h1, h2] at h
  exact h

example :
    (weightedSupportLocalCoordinateMatrix (R := RatFunc ℚ) (d := 1) (D := 2) (W := 0) (L := 2)
      1 (by norm_num) 1 2).rank ≤
      Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (D := 2) (W := 0) (L := 2)
          1 (by norm_num) 0 0)) := by
  exact rank_weightedSupportLocalCoordinateMatrix_le_base_actual
    (F := ℚ) (E := RatFunc ℚ) (d := 1) (D := 2) (W := 0) (L := 2) 1 (by norm_num) 1 2

private theorem onePointFixedMargin :
    (543 / 500 : ℝ) * ((1 : ℕ) : ℝ) * Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
  have hrank : (Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) : ℝ) ≤ 2 := by
    exact_mod_cast onePointLocalRank_le_two
  have hdim : (4 : ℝ) ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
    exact_mod_cast onePointWeightedSupportDimension_ge_four
  nlinarith

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

example : ∃ v : Fin (Fintype.card
    (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))) → ℚ[X], v ≠ 0 ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : ℚ →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z)
          (SourceColumn.interpolant
            (weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos) v) ≠ 0) ∧
      ∀ _ : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ))
        (receivedLine (0 : ℚ) 0)
        (SourceColumn.interpolant
          (weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos) v) := by
  obtain ⟨v, hv, _, _, _, hprimitive, hnonzero, hconstraints, _⟩ :=
    exists_symbolic_weightedSupport_interpolant_of_fixed_margin
      (F := ℚ) (d := 1) (D := 1) (W := 0) (L := 2) (m := 1)
      Nat.one_pos Nat.one_pos (fun _ : Fin 1 => 0) (fun _ => 0) (fun _ => 0)
      (by
        intro u hu
        have hY₀ : u (some 0) ≤ totalJetDegree u := by
          rw [totalJetDegree_eq_sum, Fin.sum_univ_succ]
          exact Nat.le_add_right _ _
        exact hY₀.trans
          (totalJetDegree_le_pred_of_weightedSupportEligible (D := 1) (L := 2) (t := 2)
            (by norm_num) (by norm_num) hu))
      onePointFixedMargin
  exact ⟨v, hv, hprimitive, hnonzero, hconstraints⟩

private def receivedLineColumns : Fin 1 → SourceColumn 1 := fun _ => ⟨1, 0, fun _ => 0⟩

private theorem receivedLineColumnsInjective : Function.Injective receivedLineColumns := by
  intro i j h
  fin_cases i
  fin_cases j
  rfl

private theorem receivedLineMatrixRankZero :
    ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => receivedLine (0 : ℚ) 0) receivedLineColumns).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 0 := by
  have hX : SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ)) (receivedLine (0 : ℚ) 0)
      (X none : DifferentialPolynomial ℚ[X] 1) := by
    rw [satisfiesLocalConstraints_iff_coeff_eq_zero]
    intro e he
    rw [unscaledLocalSubstitution_X]
    have hT : e (localT 1) = 0 := by
      rw [localContactOrder_eq] at he
      omega
    have hsingle : Finsupp.single (localT 1) 1 ≠ e := by
      intro h
      have := congrArg (fun a => a (localT 1)) h
      simp at this
      omega
    simp [MvPolynomial.coeff_X, hsingle]
  have hinterp : SourceColumn.interpolant receivedLineColumns (fun _ : Fin 1 => 1) =
      (X none : DifferentialPolynomial ℚ[X] 1) := by
    simp [SourceColumn.interpolant, receivedLineColumns, SourceColumn.exponent,
      MvPolynomial.X]
  have hmul := (localConstraintMatrix_mulVec_eq_zero_iff (m := 1)
    (centers := fun _ : Fin 1 => Polynomial.C (0 : ℚ))
    (received := fun _ => receivedLine (0 : ℚ) 0) receivedLineColumns
    (fun _ : Fin 1 => (1 : ℚ[X]))).2 (by intro i; simpa [hinterp] using hX)
  have hmatrix : localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => receivedLine (0 : ℚ) 0) receivedLineColumns = 0 := by
    apply Matrix.ext
    intro row j
    fin_cases j
    have hrow := congrFun hmul row
    simpa [Matrix.mulVec, dotProduct, localConstraintMatrix] using hrow
  rw [hmatrix]
  simp

example : Nonempty (Fin 1 × LowContactIndex 1 1) ∧ ∃ v : Fin 1 → ℚ[X], v ≠ 0 ∧
    (∀ j, v j ∈ Polynomial.degreeLT ℚ (1 + 1 - (receivedLineColumns j).y₀)) ∧
    Ideal.span (Set.range v) = ⊤ ∧
    (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : ℚ[X] →+* S),
      MvPolynomial.map ψ (SourceColumn.interpolant receivedLineColumns v) ≠ 0) ∧
    ∀ _ : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ))
      (receivedLine (0 : ℚ) 0) (SourceColumn.interpolant receivedLineColumns v) := by
  refine ⟨⟨(0 : Fin 1), ⟨0, by simp [localContactOrder]⟩⟩, ?_⟩
  exact exists_primitive_receivedLine_interpolant_of_column_height (d := 1) (m := 1) (h := 1)
    (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0) (fun _ => 0) receivedLineColumns
    receivedLineColumnsInjective (algebraMap ℚ[X] (RatFunc ℚ))
    (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) (s := 0) receivedLineMatrixRankZero
    (by decide)

example : Nonempty (Fin 1 × LowContactIndex 1 1) ∧ ∃ v : Fin 1 → ℚ[X], v ≠ 0 ∧
    (∀ j, (v j).natDegree ≤ 0 * 0 / (1 - 0)) ∧
    Ideal.span (Set.range v) = ⊤ ∧
    (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : ℚ[X] →+* S),
      MvPolynomial.map ψ (SourceColumn.interpolant receivedLineColumns v) ≠ 0) ∧
    ∀ _ : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ))
      (receivedLine (0 : ℚ) 0) (SourceColumn.interpolant receivedLineColumns v) := by
  refine ⟨⟨(0 : Fin 1), ⟨0, by simp [localContactOrder]⟩⟩, ?_⟩
  exact exists_primitive_receivedLine_interpolant_of_rank_le (d := 1) (m := 1) (ν := 0)
    (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0) (fun _ => 0) receivedLineColumns
    receivedLineColumnsInjective (by intro j; fin_cases j; decide)
    (algebraMap ℚ[X] (RatFunc ℚ)) (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
    (s := 0) receivedLineMatrixRankZero (by decide)

private theorem integerX_satisfiesLocalConstraints :
    SatisfiesLocalConstraints 1 (0 : ℤ) 0 (X none : DifferentialPolynomial ℤ 1) := by
  rw [satisfiesLocalConstraints_iff_coeff_eq_zero]
  intro e he
  rw [unscaledLocalSubstitution_X]
  have hT : e (localT 1) = 0 := by
    rw [localContactOrder_eq] at he
    omega
  have hsingle : Finsupp.single (localT 1) 1 ≠ e := by
    intro h
    have := congrArg (fun a => a (localT 1)) h
    simp at this
    omega
  simp [MvPolynomial.coeff_X, hsingle]

example : SatisfiesLocalConstraints 1 (0 : ZMod 5) 0
    (MvPolynomial.map (Int.castRingHom (ZMod 5)) (X none : DifferentialPolynomial ℤ 1)) := by
  simpa using ReedSolomon.HiddenDerivative.SatisfiesLocalConstraints.map
    (φ := Int.castRingHom (ZMod 5)) 1 0 0 (X none) integerX_satisfiesLocalConstraints

private def constantSupportColumns : Fin 1 → SourceColumn 1 :=
  fun _ => SourceColumn.ofExponent (0 : JetVariable 1 →₀ ℕ)

example : MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0)
    (SourceColumn.interpolant constantSupportColumns (fun _ => (1 : ℚ[X]))) ∈
      weightedSupportSpace ℚ 1 1 0 1 (by norm_num) := by
  exact map_interpolant_mem_weightedSupportSpace (D := 1) (d := 1) (W := 0) (L := 1)
    (by norm_num) constantSupportColumns
    (by
      intro j
      fin_cases j
      simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree,
        constantSupportColumns])
    (fun _ => 1) (RingHom.id ℚ) 0
