/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ChallengeDegree
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ColumnHeight
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveHeight
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupportCertificate
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Symbolic interpolation acceptance cases

Concrete coefficient-degree, matrix-entry, rank, height-transfer, primitive-interpolant, and
source-column cases.
-/

open Finset MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.WeightedSupportParameters
open scoped Polynomial Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

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
example : Nonempty (SymbolicReceivedCurve.Certificate 2 1 1 3 1 35 twoPointEmbedding
    (fun _ => receivedLine 0 0)) ∧
    (∃ cert : SymbolicReceivedCurve.Certificate 2 1 1 3 1 35 twoPointEmbedding
      (fun _ => receivedLine 0 0), ∃ stages terminal, SeparantChain cert.Q stages terminal) ∧
    ∃ indices : Finset (Fin 2), indices.card = 2 := by
  obtain ⟨cert⟩ := exists_weightedSupport_certificate_of_fixed_margin
    (F := ℚ) (D := 1) (d := 1)
    (W := 0) (m := 2) (A := 2) (k := 1) (g₀ := 1) Nat.one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) twoPointEmbedding
    (fun _ => 0) (fun _ => 0) (by
      have hmargin := twoPointFixedMargin (F := ℚ)
      have hcut : ((1 : ℕ) : ℝ) * 2 * (1 + (1 : ℝ)) = 4 := by norm_num
      rw [← hcut] at hmargin
      exact hmargin)
  refine ⟨⟨cert⟩, ⟨cert, ?_⟩, ⟨Finset.univ, by simp⟩⟩
  exact cert.exists_separantChain (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

private noncomputable def twoPointWeightedColumns : Fin (Fintype.card
    (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))) → SourceColumn 1 :=
  weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos

private theorem twoPointWeightedColumns_eligible : ∀ j, WeightedSupportEligible 1 1 0 2
    (twoPointWeightedColumns j).exponent :=
  weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos

/-- A nonzero two-point coefficient vector interpolates into its weighted-support space. -/
example : ∃ v : Fin (Fintype.card
    (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))) → ℚ,
    v ≠ 0 ∧ SourceColumn.interpolant twoPointWeightedColumns v ≠ 0 ∧
      SourceColumn.interpolant twoPointWeightedColumns v ∈
        weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos := by
  have hdim := onePointWeightedSupportDimension_ge_four
  rw [finrank_weightedSupportSpace_eq_card] at hdim
  have hcard' : 0 < (weightedSupportExponents 1 1 0 2 Nat.one_pos).card := by omega
  have hcard : 0 < Fintype.card
      (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos)) := by
    simpa [Fintype.card_coe] using hcard'
  let v : Fin (Fintype.card
      (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))) → ℚ := fun _ => 1
  have hv : v ≠ 0 := by
    intro hv
    have hzero := congrFun hv ⟨0, hcard⟩
    norm_num [v] at hzero
  have hcolumns : Function.Injective twoPointWeightedColumns :=
    weightedSupportColumns_injective (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos
  have hinterpolant : SourceColumn.interpolant twoPointWeightedColumns v ≠ 0 := by
    intro hzero
    exact hv ((SourceColumn.interpolant_eq_zero_iff hcolumns).mp hzero)
  exact ⟨v, hv, hinterpolant,
    interpolant_mem_weightedSupportSpace Nat.one_pos twoPointWeightedColumns
      twoPointWeightedColumns_eligible v⟩

/-- A concrete quadratic received curve block is the corresponding canonical support submatrix. -/
example :
    (fun row j => algebraMap ℚ[X] (RatFunc ℚ)
      (localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
        (fun _ => Polynomial.X ^ 2 + 1) twoPointWeightedColumns (0, row) j)) =
      (weightedSupportLocalCoordinateMatrix (R := RatFunc ℚ) (d := 1) (m := 1) (W := 0)
        (L := 2) Nat.one_pos
        (algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C (0 : ℚ)))
        (algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.X ^ 2 + 1))).submatrix id
          (weightedSupportColumnIndex Nat.one_pos twoPointWeightedColumns
            twoPointWeightedColumns_eligible) := by
  exact localConstraintBlock_eq_weightedSupportSubmatrix Nat.one_pos
    (fun _ : Fin 1 => 0) (fun _ : Fin 1 => Polynomial.X ^ 2 + 1)
    twoPointWeightedColumns twoPointWeightedColumns_eligible 0

/-- A quadratic received curve obeys the concrete weighted-support rank bound. -/
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

/-- Distinct source columns with coefficients of degree below two retain that bound. -/
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

example :
    let N := Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))
    let centers : Fin 1 → ℚ := fun _ => 0
    let polynomialCenters : Fin 1 → ℚ[X] := fun i => Polynomial.C (centers i)
    let received : Fin 1 → ℚ[X] := fun _ => receivedLine 0 0
    let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
    ∃ v : Fin N → ℚ[X], v ≠ 0 ∧
      localConstraintMatrix 1 polynomialCenters received columns *ᵥ v = 0 ∧
      Ideal.span (Set.range v) = ⊤ ∧
      SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ)) (receivedLine 0 0)
        (SourceColumn.interpolant columns v) := by
  dsimp only
  let centers : Fin 1 → ℚ := fun _ => 0
  let polynomialCenters : Fin 1 → ℚ[X] := fun i => Polynomial.C (centers i)
  let received : Fin 1 → ℚ[X] := fun _ => receivedLine 0 0
  let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
  let N := Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))
  have hband : ∀ j, WeightedSupportEligible 1 1 0 2 (columns j).exponent :=
    weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos
  have hcolumns : Function.Injective columns :=
    weightedSupportColumns_injective (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos
  have hy₀ : ∀ j, (columns j).y₀ ≤ 1 := by
    intro j
    have hband' : WeightedSupportEligible 1 1 0
        (((1 : ℕ) : ℝ) * (1 : ℕ) * (1 + (1 : ℝ))) (columns j).exponent := by
      have hcut : ((1 : ℕ) : ℝ) * (1 : ℕ) * (1 + (1 : ℝ)) = 2 := by norm_num
      simpa only [hcut] using hband j
    have h := y₀_le_two_mul_sub_one_of_eligible (d := 1) (D := 1) (m := 1) (W := 0)
      (g := 1) Nat.one_pos (by norm_num) hband'
    simpa using h
  have hdim : 3 ≤ N := by
    have hdim' := onePointWeightedSupportDimension_ge_four
    rw [finrank_weightedSupportSpace_eq_card] at hdim'
    have hdim'' : 3 ≤ (weightedSupportExponents 1 1 0 2 Nat.one_pos).card := by omega
    simpa [N, Fintype.card_coe] using hdim''
  have hmargin : Fintype.card (Fin 1) * Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) < Fintype.card (Fin N) := by
    have hrank := onePointLocalRank_le_two
    have hlt : Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) < N := by omega
    simpa [Fintype.card_fin] using hlt
  obtain ⟨v, hv, _, hspan, _, hconstraints⟩ :=
    exists_primitive_weightedSupport_interpolant.{0, 0, 0, 0}
      (F := ℚ) (d := 1) (D := 1) (W := 0)
      (L := 2) (m := 1) (ι := Fin 1) (κ := Fin N) Nat.one_pos 1 1 centers received
      (fun _ => natDegree_receivedLine_le 0 0) columns hcolumns hy₀ hband hmargin
  exact ⟨v, hv,
    (localConstraintMatrix_mulVec_eq_zero_iff 1 polynomialCenters received columns v).mpr
      hconstraints,
    hspan, hconstraints 0⟩

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

private def sixteenPointEmbedding : Fin 16 ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at hij
    exact_mod_cast hij

/-- The rate construction gives a certificate at a small, feasible agreement threshold. -/
example :
    let d := Nat.ceil (Real.exp (xi / (1 / 8 : ℝ)))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (SymbolicReceivedCurve.Certificate 2 1 1 (2 * m - 1) d
      (12 * (2 * m - 1) - 1) sixteenPointEmbedding (fun _ => receivedLine 0 0)) := by
  dsimp
  exact exists_weightedSupport_certificate_of_rate (F := ℚ) (δ := 1 / 8) (n := 16)
    (D := 1) (A := 2) (k := 1) sixteenPointEmbedding (fun _ => 0) (fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) Nat.one_pos (by norm_num) (by norm_num)
    (by norm_num) (by nlinarith [rateGap_le_one (1 / 8) (1 / 16)])

private noncomputable def prescribedExampleDelta : ℝ := 1 / 8

private noncomputable def prescribedExampleOrder : ℕ :=
  Nat.ceil (Real.exp (xi / prescribedExampleDelta))

private noncomputable def prescribedExampleHarmonic : ℝ :=
  harmonic (prescribedExampleOrder - 1)

private noncomputable def prescribedExampleMultiplicity : ℕ :=
  Nat.ceil (100 * (prescribedExampleOrder : ℝ) ^ 2 * prescribedExampleHarmonic)

private noncomputable def prescribedExampleBlockLength : ℕ :=
  8 * prescribedExampleMultiplicity

private def prescribedExampleCenters : Fin prescribedExampleBlockLength ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at hij
    exact_mod_cast hij

private theorem prescribedExampleMultiplicity_pos : 0 < prescribedExampleMultiplicity := by
  have horder := prescribed_order_lower prescribedExampleDelta
    (by norm_num [prescribedExampleDelta]) (by norm_num [prescribedExampleDelta])
  have hharmonic : 0 < prescribedExampleHarmonic := by
    have hlower : xi / prescribedExampleDelta ≤ prescribedExampleHarmonic := by
      simpa [prescribedExampleOrder, prescribedExampleHarmonic] using horder.2.2
    exact (div_pos xi_pos (by norm_num [prescribedExampleDelta])).trans_le hlower
  have horder_pos : 0 < (prescribedExampleOrder : ℝ) := by
    have horder_nat : 0 < prescribedExampleOrder :=
      lt_of_lt_of_le (by norm_num : 0 < 48000) horder.1
    exact_mod_cast horder_nat
  have hargument : 0 < 100 * (prescribedExampleOrder : ℝ) ^ 2 * prescribedExampleHarmonic := by
    positivity
  change 0 < Nat.ceil (100 * (prescribedExampleOrder : ℝ) ^ 2 * prescribedExampleHarmonic)
  exact Nat.ceil_pos.mpr hargument

/-- The prescribed-threshold construction gives a certificate when its threshold fits the block. -/
example :
    let A := ReedSolomon.agreementThreshold prescribedExampleDelta prescribedExampleBlockLength 1
    A ≤ prescribedExampleBlockLength ∧
      Nonempty (SymbolicReceivedCurve.Certificate A 1 1
        (2 * prescribedExampleMultiplicity - 1) prescribedExampleOrder
        (12 * (2 * prescribedExampleMultiplicity - 1) - 1) prescribedExampleCenters
        (fun _ => receivedLine 0 0)) := by
  dsimp
  have hceil : ⌈prescribedExampleDelta * prescribedExampleBlockLength⌉₊ =
      prescribedExampleMultiplicity := by
    have harg : prescribedExampleDelta * (prescribedExampleBlockLength : ℕ) =
        (prescribedExampleMultiplicity : ℝ) := by
      dsimp [prescribedExampleDelta, prescribedExampleBlockLength]
      push_cast
      ring
    rw [harg, Nat.ceil_natCast]
  have hA : ReedSolomon.agreementThreshold prescribedExampleDelta
      prescribedExampleBlockLength 1 ≤ prescribedExampleBlockLength := by
    have hm := prescribedExampleMultiplicity_pos
    rw [ReedSolomon.agreementThreshold, hceil]
    dsimp [prescribedExampleBlockLength]
    omega
  have hblock :
      let d := Nat.ceil (Real.exp (xi / prescribedExampleDelta))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ prescribedExampleBlockLength := by
    change 8 * prescribedExampleMultiplicity ≤ prescribedExampleBlockLength
    dsimp [prescribedExampleBlockLength]
    rfl
  exact ⟨hA, by
    simpa [prescribedExampleDelta, prescribedExampleOrder, prescribedExampleHarmonic,
      prescribedExampleMultiplicity] using
      (exists_prescribed_symbolic_weightedSupport_certificate (F := ℚ)
        prescribedExampleDelta prescribedExampleBlockLength 1 prescribedExampleCenters
        (fun _ => 0) (fun _ => 0) (by norm_num [prescribedExampleDelta])
        (by norm_num [prescribedExampleDelta]) hblock hA)⟩
private def shiftedKernelColumns : Fin 2 → SourceColumn 1 := fun j =>
  ⟨j.val, 0, fun _ => 1⟩

private theorem shiftedKernelColumns_injective : Function.Injective shiftedKernelColumns := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [shiftedKernelColumns]

private theorem shiftedKernelColumns_degree (j : Fin 2) :
    totalJetDegree (shiftedKernelColumns j).exponent = 1 := by
  fin_cases j <;> simp [shiftedKernelColumns]

private theorem shiftedKernelColumns_interpolant (v : Fin 2 → (ZMod 5)[X]) :
    SourceColumn.interpolant shiftedKernelColumns v =
      v 0 • (MvPolynomial.X (some 1) : DifferentialPolynomial (ZMod 5)[X] 1) +
        v 1 • ((MvPolynomial.X none : DifferentialPolynomial (ZMod 5)[X] 1) *
          MvPolynomial.X (some 1)) := by
  rw [SourceColumn.interpolant_eq_sum_smul]
  simp [shiftedKernelColumns, SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]

private noncomputable def shiftedConstraintMatrix :
    Matrix (Fin 1) (Fin 2) (ZMod 5)[X] := fun _ j => if j = 0 then 1 else 0

private theorem shiftedKernelColumns_constraint_iff (v : Fin 2 → (ZMod 5)[X]) :
    SatisfiesLocalConstraints 1 (Polynomial.C (0 : ZMod 5)) (0 : (ZMod 5)[X])
      (SourceColumn.interpolant shiftedKernelColumns v) ↔ v 0 = 0 := by
  rw [satisfiesLocalConstraints_iff_coeff_eq_zero]
  have hsub :
      unscaledLocalSubstitution 1 (Polynomial.C (0 : ZMod 5)) (0 : (ZMod 5)[X])
        (SourceColumn.interpolant shiftedKernelColumns v) =
      MvPolynomial.C (v 0) * MvPolynomial.X (localY 0) +
        MvPolynomial.C (v 1) *
          MvPolynomial.monomial
            (Finsupp.single (localT 1) 1 + Finsupp.single (localY 0) 1) 1 := by
    have hmon :
        (MvPolynomial.X (localT 1) : LocalPolynomial (ZMod 5)[X] 1) *
          MvPolynomial.X (localY 0) =
        MvPolynomial.monomial
          (Finsupp.single (localT 1) 1 + Finsupp.single (localY 0) 1) 1 := by
      rw [← pow_one (MvPolynomial.X (localT 1)), ← pow_one (MvPolynomial.X (localY 0)),
        MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.monomial_mul_monomial]
      norm_num
    have hsource : (some 1 : JetVariable 1) = some (Fin.succ (0 : Fin 1)) := by decide
    rw [shiftedKernelColumns_interpolant]
    simp only [map_add, map_smul, map_mul]
    rw [hsource]
    rw [unscaledLocalSubstitution_Y_succ, unscaledLocalSubstitution_X]
    simp only [Polynomial.C_0, MvPolynomial.C_0, zero_add]
    simp only [localT, localY] at hmon ⊢
    rw [smul_eq_C_mul, smul_eq_C_mul]
    rw [hmon]
  have hcoeff :
      (unscaledLocalSubstitution 1 (Polynomial.C (0 : ZMod 5)) (0 : (ZMod 5)[X])
        (SourceColumn.interpolant shiftedKernelColumns v)).coeff
          (Finsupp.single (localY 0) 1) = v 0 := by
    rw [hsub]
    have hne : Finsupp.single (localT 1) 1 + Finsupp.single (localY 0) 1 ≠
        Finsupp.single (localY 0) 1 := by
      intro h
      have ht := congrArg (fun q => q (localT 1)) h
      simp [localT, localY] at ht
    simp [hne]
  constructor
  · intro h
    have h := h (Finsupp.single (localY 0) 1) (by
      rw [localContactOrder_eq]
      simp [localT, localE, localAux, localY])
    rw [hcoeff] at h
    exact h
  · intro hv e he
    rw [hsub]
    have hT : e (localT 1) = 0 := by
      rw [localContactOrder_eq] at he
      omega
    have hT' : e none = 0 := by simpa [localT] using hT
    have hne : Finsupp.single (localT 1) 1 + Finsupp.single (localY 0) 1 ≠ e := by
      intro h
      have ht := congrArg (fun q => q (localT 1)) h
      simp [localT, localY] at ht
      omega
    simp [hv, hne]

/-- A concrete shifted row and column surplus constructs a primitive interpolant. -/
example :
    ∃ v : Fin 2 → (ZMod 5)[X],
      v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT (ZMod 5)
        (1 + 1 - 1 * totalJetDegree (shiftedKernelColumns j).exponent)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : ZMod 5 →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z)
          (SourceColumn.interpolant shiftedKernelColumns v) ≠ 0) ∧
      ∀ _i : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ZMod 5))
        (0 : (ZMod 5)[X])
        (SourceColumn.interpolant shiftedKernelColumns v) := by
  exact exists_primitive_interpolant_of_shifted_height
    (F := ZMod 5) (d := 1) (n := 1) (N := 2) (rows := 1) 1 1 1
    (fun _ : Fin 1 ↦ (0 : ZMod 5)) (fun _ : Fin 1 ↦ (0 : (ZMod 5)[X]))
    shiftedKernelColumns shiftedKernelColumns_injective
    shiftedConstraintMatrix (fun _ : Fin 1 ↦ 1)
    (by
      intro v
      constructor
      · intro hv i
        have hv0 : v 0 = 0 := by
          simpa [shiftedConstraintMatrix, Matrix.mulVec, dotProduct] using congrFun hv 0
        fin_cases i
        exact (shiftedKernelColumns_constraint_iff v).2 hv0
      · intro h
        have hv0 := (shiftedKernelColumns_constraint_iff v).1 (h 0)
        ext i
        fin_cases i
        simp [shiftedConstraintMatrix, Matrix.mulVec, dotProduct, hv0])
    (by
      intro i j h
      rw [shiftedKernelColumns_degree j] at h ⊢
      fin_cases i
      fin_cases j <;> norm_num [shiftedConstraintMatrix] at h ⊢)
    (by
      intro i j h
      rw [shiftedKernelColumns_degree j] at h
      norm_num at h)
    (by norm_num [shiftedKernelColumns, SourceColumn.totalJetDegree_exponent,
      shiftedConstraintMatrix])

namespace SymbolicCurveCertificateTest

open ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

/-- One center and the single source column `Y₀`. -/
noncomputable def centers : Fin 1 ↪ ℚ :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

noncomputable def received : Fin 1 → ℚ[X] := fun _ => 0

def columns : Fin 1 → SourceColumn 0 := fun _ => ⟨0, 1, Fin.elim0⟩

private theorem columnsInjective : Function.Injective columns := by
  intro i j _
  exact Subsingleton.elim _ _

private theorem columnsWeight :
    ∀ j, Finsupp.weight (differentialWeight 0) (columns j).exponent < 1 := by
  intro j
  simp [weight_differentialWeight_eq, columns, SourceColumn.exponent]

private theorem columnsDegree : ∀ j, totalJetDegree (columns j).exponent ≤ 1 := by
  intro j
  simp [columns]

private theorem singletonRankZero :
    ((supportedLocalConstraintMatrix 1 (fun i => Polynomial.C (centers i)) received columns).map
      (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 0 := by
  have hY : (columns 0).polynomial =
      (MvPolynomial.X (some 0) : DifferentialPolynomial ℚ[X] 0) := by
    simpa [columns, SourceColumn.polynomial, SourceColumn.exponent] using
      (MvPolynomial.X_pow_eq_monomial (n := some 0) (e := 1) :
        (MvPolynomial.X (some 0) : DifferentialPolynomial ℚ[X] 0) ^ 1 =
          MvPolynomial.monomial (Finsupp.single (some 0) 1) 1).symm
  have hsub : unscaledLocalSubstitution 0 (Polynomial.C (centers 0)) (received 0)
      ((columns 0).polynomial : DifferentialPolynomial ℚ[X] 0) =
        MvPolynomial.monomial
          (Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1) 1 := by
    rw [hY, unscaledLocalSubstitution_Y_zero]
    simp only [received, localCorrection, Finset.univ_eq_empty, Finset.sum_empty]
    rw [← pow_one (MvPolynomial.X (localT 0)), ← pow_one (MvPolynomial.X (localE 0)),
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial]
    norm_num
  have hcoeff : ∀ e : LowContactIndex 0 1,
      (unscaledLocalSubstitution 0 (Polynomial.C (centers 0)) (received 0)
        ((columns 0).polynomial : DifferentialPolynomial ℚ[X] 0)).coeff e.1 = 0 := by
    intro e
    have hne : e.1 ≠ Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1 := by
      intro he
      have hweight : localContactOrder 0
          (Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1) = 1 := by
        rw [localContactOrder, map_add, Finsupp.weight_single, Finsupp.weight_single]
        simp
      have hlow := e.2
      rw [he, hweight] at hlow
      omega
    rw [hsub, MvPolynomial.coeff_monomial]
    simp [Ne.symm hne]
  have hmatrix : localConstraintMatrix 1
      (fun i => Polynomial.C (centers i)) received columns = 0 := by
    apply Matrix.ext
    intro row j
    rcases row with ⟨i, e⟩
    fin_cases i
    fin_cases j
    rw [localConstraintMatrix_apply]
    simpa [centers, received, columns] using hcoeff e
  rw [rank_map_supportedLocalConstraintMatrix, hmatrix]
  rw [Matrix.map_zero _ (map_zero _)]
  exact (Matrix.rank_zero).le

private theorem singletonCertificate :
    Nonempty (Certificate 1 1 0 1 0 0 centers received) := by
  exact exists_certificate_of_monomial_rank_bound
    (d := 0) (D := 0) (m := 1) (A := 1) (k := 1) (ℓ := 0) (ν := 1) (r := 0)
    (hbudget := by norm_num) (hkD := by omega) centers received
    (by intro i; simp [received]) columns columnsInjective
    (by intro j; simp [columns]) columnsDegree columnsWeight
    (algebraMap ℚ[X] (RatFunc ℚ)) (IsFractionRing.injective _ _) singletonRankZero (by simp)

/-- The monomial-rank construction yields a nonzero equation vanishing on the received constant. -/
example : ∃ cert : Certificate 1 1 0 1 0 0 centers received,
    cert.Q ≠ 0 ∧ differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0) cert.Q) 0 = 0 := by
  obtain ⟨cert⟩ := singletonCertificate
  refine ⟨cert, cert.nonzero, ?_⟩
  have hs := cert.specialization_sound (E := ℚ) (RingHom.id ℚ) 0
  exact hs.2.2 Finset.univ 0 (by norm_num) (by simp) (by intro i hi; simp [received])

/-- The one-column example has a separant chain in characteristic zero. -/
example : ∃ cert : Certificate 1 1 0 1 0 0 centers received,
    ∃ stages terminal, SeparantChain cert.Q stages terminal := by
  obtain ⟨cert⟩ := singletonCertificate
  exact ⟨cert, cert.exists_separantChain (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))⟩

/-- At the zero challenge, the one-column example reaches a regular separant stage. -/
example : ∃ cert : Certificate 1 1 0 1 0 0 centers received,
    ∃ stages terminal, SeparantChain cert.Q stages terminal ∧
      ∃ stage ∈ stages,
        differentialSpecialization
          (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0) stage.1) 0 = 0 ∧
        differentialSpecialization
          (separant (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0) stage.1)
            stage.2) 0 ≠ 0 := by
  obtain ⟨cert⟩ := singletonCertificate
  obtain ⟨stages, terminal, hc⟩ :=
    cert.exists_separantChain (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨exceptional, hcard, hcoverage⟩ :=
    cert.exists_exceptional_stage_coverage hc (RingHom.id ℚ)
  have hex : exceptional = ∅ := Finset.card_eq_zero.mp (by omega)
  subst exceptional
  have hstage := hcoverage 0 (by simp) Finset.univ (0 : ℚ[X])
    (by simp) (by simp) (by intro i hi; simp [received])
  exact ⟨cert, stages, terminal, hc, hstage⟩

/-- Weighted-support eligibility gives the same concrete one-column certificate. -/
example : ∃ cert : Certificate 1 1 0 1 0 0 centers received, cert.Q ≠ 0 := by
  have hband : ∀ j, WeightedSupportEligible 0 0 0 1 (columns j).exponent := by
    intro j
    fin_cases j
    simp [WeightedSupportEligible, fullHigherJetWeight, SourceColumn.weight_exponent,
      SourceColumn.totalJetDegree_exponent, columns, jetHigherWeight]
  obtain ⟨cert⟩ := exists_certificate_of_rank_bound
    (L := 1) (W := 0) (D := 0) (m := 1) (A := 1) (k := 1) (ℓ := 0) (ν := 1) (r := 0)
    (by norm_num) (by norm_num) (by omega) centers received
    (by intro i; simp [received]) columns columnsInjective
    (by intro j; simp [columns]) columnsDegree hband
    (algebraMap ℚ[X] (RatFunc ℚ)) (IsFractionRing.injective _ _)
    singletonRankZero (by simp)
  exact ⟨cert, cert.nonzero⟩

end SymbolicCurveCertificateTest
