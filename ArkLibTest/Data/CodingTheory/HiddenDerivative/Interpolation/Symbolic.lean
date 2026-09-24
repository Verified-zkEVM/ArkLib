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
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.PartitionRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Soundness
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Symbolic interpolation acceptance cases

Concrete coefficient-degree, matrix-entry, rank, height-transfer, primitive-interpolant,
source-column, and curve-certificate cases.
-/

open Finset MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
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


namespace SymbolicPartitionRankTest

/-- Three distinct polynomials for the local rank bound with budget two. -/
private noncomputable def localRankPolynomials : Fin 3 → DifferentialPolynomial ℚ 1 :=
  ![1, X (some 1), 1 + X (some 1)]

/-- Their local coordinate matrix at center one with multiplicity one. -/
private noncomputable def localRankMatrix : Matrix (LowContactIndex 1 1) (Fin 3) ℚ :=
  fun row column => localConstraintCoordinatesAt 1 1 0 (localRankPolynomials column) row

/-- Three distinct nonzero columns attain the local coordinate budget of two. -/
example : Function.Injective localRankPolynomials ∧ 2 < Fintype.card (Fin 3) ∧
    localRankMatrix.rank = 2 := by
  let polynomials := localRankPolynomials
  let M := localRankMatrix
  have hconstant : (1 : DifferentialPolynomial ℚ 1) = MvPolynomial.monomial 0 1 := by
    simp
  have hYmon : (X (some 1) : DifferentialPolynomial ℚ 1) =
      MvPolynomial.monomial (Finsupp.single (some 1) 1) 1 := by
    rw [← MvPolynomial.X_pow_eq_monomial]
    simp
  have hweight : ∀ j u, u ∈ (polynomials j).support → fullDerivativeJetWeight u ≤ 1 := by
    intro j u hu
    fin_cases j
    · change u ∈ (1 : DifferentialPolynomial ℚ 1).support at hu
      rw [hconstant] at hu
      have hu' : u = 0 := by simpa using MvPolynomial.support_monomial_subset hu
      subst u
      simp [fullDerivativeJetWeight]
    · change u ∈ (X (some 1) : DifferentialPolynomial ℚ 1).support at hu
      rw [hYmon] at hu
      have hu' : u = Finsupp.single (some 1) 1 := by
        simpa using MvPolynomial.support_monomial_subset hu
      subst u
      simp [fullDerivativeJetWeight, jetDerivativeWeight, Finsupp.weight_single]
    · change u ∈ (1 + X (some 1) : DifferentialPolynomial ℚ 1).support at hu
      have hs := MvPolynomial.support_add hu
      rcases Finset.mem_union.mp hs with hconst | hmemY
      · rw [hconstant] at hconst
        have hu' : u = 0 := by simpa using MvPolynomial.support_monomial_subset hconst
        rw [hu']
        simp [fullDerivativeJetWeight]
      · rw [hYmon] at hmemY
        have hu' : u = Finsupp.single (some 1) 1 := by
          simpa using MvPolynomial.support_monomial_subset hmemY
        rw [hu']
        simp [fullDerivativeJetWeight, jetDerivativeWeight, Finsupp.weight_single]
  have hupper := localConstraintCoordinates_rank_le_of_derivative_weight
    (m := 1) (W := 1) (center := (1 : ℚ)) (received := (0 : ℚ)) polynomials hweight
  have hbudget : localDerivativeCoordinateBudget 1 1 1 = 2 := by decide
  have hupper' : M.rank ≤ 2 := by
    have hM : M = fun row j =>
        localConstraintCoordinatesAt 1 1 0 (polynomials j) row := by
      ext row j
      rfl
    rw [hM]
    simpa [polynomials, localRankPolynomials, hbudget] using hupper
  let rowZero : LowContactIndex 1 1 := ⟨0, by simp [localContactOrder]⟩
  let rowY : LowContactIndex 1 1 :=
    ⟨Finsupp.single (localY 0) 1,
      by rw [localContactOrder_eq]; simp [localT, localE, localAux, localY]⟩
  let rows : Fin 2 → LowContactIndex 1 1 := ![rowZero, rowY]
  let columns : Fin 2 → Fin 3 := fun j => ⟨j.val, by omega⟩
  have hsubstY : unscaledLocalSubstitution 1 1 0
      (X (some 1) : DifferentialPolynomial ℚ 1) = X (localY 0) := by
    simpa [localY] using
      (unscaledLocalSubstitution_Y_succ (d := 1) (center := (1 : ℚ))
        (received := (0 : ℚ)) (j := (0 : Fin 1)))
  have hminor : M.submatrix rows columns = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · change (unscaledLocalSubstitution 1 1 0
        (1 : DifferentialPolynomial ℚ 1)).coeff 0 = 1
      simp
    · change (unscaledLocalSubstitution 1 1 0
        (X (some 1) : DifferentialPolynomial ℚ 1)).coeff 0 = 0
      rw [hsubstY]
      simp [localY]
    · change M (rows (1 : Fin 2)) (columns (0 : Fin 2)) =
        (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 0
      rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      simp only [rows, columns, Matrix.cons_val_one]
      simp only [Matrix.cons_val_zero]
      change localConstraintCoordinatesAt 1 1 0
        (1 : DifferentialPolynomial ℚ 1) rowY = 0
      simp only [localConstraintCoordinatesAt, LinearMap.comp_apply, lowContactCoefficients,
        LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
      simp only [AlgHom.toLinearMap_apply, map_one]
      change (1 : LocalPolynomial ℚ 1).coeff (Finsupp.single (localY 0) 1) = 0
      apply MvPolynomial.coeff_C_of_ne_zero
      · intro hz
        have := congrArg (fun e : LocalVariable 1 →₀ ℕ => e (localY 0)) hz
        simp [localY] at this
    · change (unscaledLocalSubstitution 1 1 0
        (X (some 1) : DifferentialPolynomial ℚ 1)).coeff
        (Finsupp.single (localY 0) 1) = 1
      rw [hsubstY]
      simp [localY]
  have hminorRank : (M.submatrix rows columns).rank = 2 := by
    rw [hminor, Matrix.rank_one]
    simp
  have hlower : 2 ≤ M.rank := by
    calc
      2 = (M.submatrix rows columns).rank := hminorRank.symm
      _ ≤ M.rank := Matrix.rank_submatrix_le M rows columns
  have h01 : localRankPolynomials 0 ≠ localRankPolynomials 1 := by
    change (1 : DifferentialPolynomial ℚ 1) ≠ X (some 1)
    intro h
    have hc := congrArg (fun p : DifferentialPolynomial ℚ 1 =>
      p.coeff (Finsupp.single (some 1) 1)) h
    have he : (0 : JetVariable 1 →₀ ℕ) ≠ Finsupp.single (some 1) 1 := by
      intro hz
      have := congrArg (fun e : JetVariable 1 →₀ ℕ => e (some 1)) hz
      simp at this
    norm_num [MvPolynomial.coeff_one, he] at hc
  have h02 : localRankPolynomials 0 ≠ localRankPolynomials 2 := by
    change (1 : DifferentialPolynomial ℚ 1) ≠ 1 + X (some 1)
    intro h
    have hc := congrArg (fun p : DifferentialPolynomial ℚ 1 =>
      p.coeff (Finsupp.single (some 1) 1)) h
    have he : (0 : JetVariable 1 →₀ ℕ) ≠ Finsupp.single (some 1) 1 := by
      intro hz
      have := congrArg (fun e : JetVariable 1 →₀ ℕ => e (some 1)) hz
      simp at this
    norm_num [MvPolynomial.coeff_one, he] at hc
  have h12 : localRankPolynomials 1 ≠ localRankPolynomials 2 := by
    change (X (some 1) : DifferentialPolynomial ℚ 1) ≠ 1 + X (some 1)
    intro h
    have hc := congrArg (fun p : DifferentialPolynomial ℚ 1 =>
      p.coeff (0 : JetVariable 1 →₀ ℕ)) h
    norm_num [MvPolynomial.coeff_one] at hc
  exact ⟨by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (h01 hij)
      · exact False.elim (h02 hij)
      · exact False.elim (h01 hij.symm)
      · rfl
      · exact False.elim (h12 hij)
      · exact False.elim (h02 hij.symm)
      · exact False.elim (h12 hij.symm)
      · rfl,
    by norm_num, Nat.le_antisymm hupper' hlower⟩

private def supportedRankColumns : Fin 13 → SourceColumn 1 := fun j =>
  ⟨j.val - 1, if j.val = 0 then 1 else 0, ![0]⟩

private def supportedRankCenters : Fin 4 → ℚ := ![0, 1, 2, 3]

private noncomputable def supportedRankReceived : Fin 4 → ℚ[X] := fun _ => 0

private noncomputable def supportedRankMatrix : Matrix
    (localConstraintSupportedRows 2 (Polynomial.C ∘ supportedRankCenters)
      supportedRankReceived supportedRankColumns) (Fin 13) (RatFunc ℚ) :=
  (supportedLocalConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters)
    supportedRankReceived supportedRankColumns).map (algebraMap ℚ[X] (RatFunc ℚ))

/-- Thirteen columns support twelve local rows and give nonzero symbolic rank. -/
example : Function.Injective supportedRankColumns ∧ 12 < Fintype.card (Fin 13) ∧
    11 < Fintype.card (localConstraintSupportedRows 2
    (Polynomial.C ∘ supportedRankCenters) supportedRankReceived supportedRankColumns) ∧
    0 < supportedRankMatrix.rank ∧ supportedRankMatrix.rank ≤ 12 := by
  have hcolumns : Function.Injective supportedRankColumns := by
    intro i j hij
    have hx := congrArg SourceColumn.x hij
    have hy := congrArg SourceColumn.y₀ hij
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      by_cases hj : j.val = 0
      · exact Fin.ext (by omega)
      · simp [supportedRankColumns, hj] at hy
    · by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        subst j
        simp [supportedRankColumns, hi] at hy
      · have hx' : i.val - 1 = j.val - 1 := by
          simpa [supportedRankColumns, hi, hj] using hx
        exact Fin.ext (by omega)
  have hweight : ∀ j, fullDerivativeJetWeight (supportedRankColumns j).exponent ≤ 0 := by
    intro j
    change (supportedRankColumns j).exponent.weight jetDerivativeWeight ≤ 0
    rw [SourceColumn.weight_exponent]
    simp [jetDerivativeWeight, supportedRankColumns]
  have hupper := rank_map_supportedLocalConstraintMatrix_le_of_derivative_weight
    (m := 2) (W := 0) supportedRankCenters supportedRankReceived supportedRankColumns hweight
  have hbudget : localDerivativeCoordinateBudget 1 2 0 = 3 := by decide
  have hupper' : supportedRankMatrix.rank ≤ 12 := by
    change ((supportedLocalConstraintMatrix 2
      (fun i => Polynomial.C (supportedRankCenters i)) supportedRankReceived
      supportedRankColumns).map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 4 * 3
    simpa [hbudget] using hupper
  let rowZero : LowContactIndex 1 2 := ⟨0, by simp [localContactOrder]⟩
  let rowT : LowContactIndex 1 2 :=
    ⟨Finsupp.single (localT 1) 1,
      by rw [localContactOrder_eq]; simp [localT, localE, localAux]⟩
  let rowTY : LowContactIndex 1 2 :=
    ⟨Finsupp.single (localT 1) 1 + Finsupp.single (localY 0) 1,
      by rw [localContactOrder_eq]; simp [localT, localE, localAux, localY]⟩
  let localRows : Fin 3 → LowContactIndex 1 2 := ![rowZero, rowT, rowTY]
  let rawRows : Fin 4 × Fin 3 → Fin 4 × LowContactIndex 1 2 :=
    fun ij => (ij.1, localRows ij.2)
  have hzeroEntry (i : Fin 4) :
      localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters) supportedRankReceived
        supportedRankColumns (i, rowZero) (Fin.succ 0) = 1 := by
    rw [localConstraintMatrix_apply]
    rw [show rowZero.1 = (0 : LocalVariable 1 →₀ ℕ) by rfl]
    have hcolumn : (supportedRankColumns (Fin.succ 0)).polynomial =
        (1 : DifferentialPolynomial ℚ[X] 1) := by
      rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
      norm_num [supportedRankColumns]
    rw [hcolumn]
    simp [unscaledLocalSubstitution]
  have hTEntry (i : Fin 4) :
      localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters) supportedRankReceived
        supportedRankColumns (i, rowT) (Fin.succ (Fin.succ 0)) = 1 := by
    rw [localConstraintMatrix_apply]
    have hcolumn : (supportedRankColumns (Fin.succ (Fin.succ 0))).polynomial =
        (X none : DifferentialPolynomial ℚ[X] 1) := by
      rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
      norm_num [supportedRankColumns]
    rw [hcolumn, unscaledLocalSubstitution_X]
    have hne : Finsupp.single (localT 1) 1 ≠ 0 := by
      intro hz
      have := congrArg (fun e : LocalVariable 1 →₀ ℕ => e (localT 1)) hz
      simp [localT] at this
    change (MvPolynomial.C (Polynomial.C (supportedRankCenters i)) +
      MvPolynomial.X (localT 1)).coeff (Finsupp.single (localT 1) 1) = 1
    rw [AddMonoidAlgebra.coeff_add]
    change ((MvPolynomial.C (Polynomial.C (supportedRankCenters i))).coeff
      (Finsupp.single (localT 1) 1) +
        (MvPolynomial.X (localT 1)).coeff (Finsupp.single (localT 1) 1)) = 1
    rw [MvPolynomial.coeff_C_of_ne_zero hne, MvPolynomial.coeff_X_same]
    simp
  have hTYEntry (i : Fin 4) :
      localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters) supportedRankReceived
        supportedRankColumns (i, rowTY) 0 = 1 := by
    rw [localConstraintMatrix_apply]
    have hcolumn : (supportedRankColumns 0).polynomial =
        (X (some 0) : DifferentialPolynomial ℚ[X] 1) := by
      rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
      simp [supportedRankColumns]
    rw [hcolumn, unscaledLocalSubstitution_Y_zero]
    have hrowNZ : (0 : LocalVariable 1 →₀ ℕ) ≠
        Finsupp.single (localT 1) 1 + Finsupp.single (localY 0) 1 := by
      intro hz
      have := congrArg (fun e : LocalVariable 1 →₀ ℕ => e (localT 1)) hz
      simp [localT, localY] at this
    have hcorrection : localCorrection (R := ℚ[X]) 1 =
        X (localT 1) * X (localY 0) := by
      simp [localCorrection, localT, localY]
    rw [hcorrection]
    change (MvPolynomial.C (supportedRankReceived i) +
      MvPolynomial.X (localT 1) * MvPolynomial.X (localY 0) +
      MvPolynomial.X (localT 1) * MvPolynomial.X (localE 1)).coeff
      (Finsupp.single (localT 1) 1 + Finsupp.single (localY 0) 1) = 1
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [MvPolynomial.coeff_C_of_ne_zero hrowNZ.symm,
      MvPolynomial.coeff_X_mul, MvPolynomial.coeff_X_mul]
    simp [localE, localAux, localY]
  have hsupportedZero (ij : Fin 4 × Fin 3) : rawRows (ij.1, 0) ∈
      localConstraintSupportedRows 2 (Polynomial.C ∘ supportedRankCenters)
        supportedRankReceived supportedRankColumns := by
    rw [mem_localConstraintSupportedRows_iff]
    refine ⟨Fin.succ 0, ?_⟩
    change localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters)
      supportedRankReceived supportedRankColumns (rawRows (ij.1, 0)) (Fin.succ 0) ≠ 0
    change localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters)
      supportedRankReceived supportedRankColumns (ij.1, rowZero) (Fin.succ 0) ≠ 0
    rw [hzeroEntry ij.1]
    norm_num
  have hsupportedT (ij : Fin 4 × Fin 3) : rawRows (ij.1, 1) ∈
      localConstraintSupportedRows 2 (Polynomial.C ∘ supportedRankCenters)
        supportedRankReceived supportedRankColumns := by
    rw [mem_localConstraintSupportedRows_iff]
    refine ⟨Fin.succ (Fin.succ 0), ?_⟩
    change localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters)
      supportedRankReceived supportedRankColumns (ij.1, rowT) (Fin.succ (Fin.succ 0)) ≠ 0
    rw [hTEntry]
    norm_num
  have hsupportedTY (ij : Fin 4 × Fin 3) : rawRows (ij.1, 2) ∈
      localConstraintSupportedRows 2 (Polynomial.C ∘ supportedRankCenters)
        supportedRankReceived supportedRankColumns := by
    rw [mem_localConstraintSupportedRows_iff]
    refine ⟨0, ?_⟩
    change localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters)
      supportedRankReceived supportedRankColumns (ij.1, rowTY) 0 ≠ 0
    rw [hTYEntry]
    norm_num
  let supportedRows : Fin 4 × Fin 3 → localConstraintSupportedRows 2
      (Polynomial.C ∘ supportedRankCenters) supportedRankReceived supportedRankColumns :=
    fun ij => by
      rcases ij with ⟨i, j⟩
      refine ⟨rawRows (i, j), ?_⟩
      fin_cases j
      · simpa [rawRows, localRows] using hsupportedZero (i, 0)
      · simpa [rawRows, localRows] using hsupportedT (i, 1)
      · simpa [rawRows, localRows] using hsupportedTY (i, 2)
  have hinj : Function.Injective supportedRows := by
    intro ij kl hij
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    have hraw : rawRows (i, j) = rawRows (k, l) := congrArg Subtype.val hij
    have hfst : i = k := congrArg (fun p : Fin 4 × LowContactIndex 1 2 => p.1) hraw
    have hsnd : localRows j = localRows l :=
      congrArg (fun p : Fin 4 × LowContactIndex 1 2 => p.2) hraw
    have hlocal : j = l := by
      fin_cases j <;> fin_cases l
      all_goals
        first
        | rfl
        | {
            have hrow := congrArg Subtype.val hsnd
            have hT := congrArg (fun e : LocalVariable 1 →₀ ℕ => e (localT 1)) hrow
            have hY := congrArg (fun e : LocalVariable 1 →₀ ℕ => e (localY 0)) hrow
            simp [localRows, rowZero, rowT, rowTY, localT, localY] at hT hY
          }
    cases hfst
    cases hlocal
    rfl
  have hrows : 12 ≤ Fintype.card (localConstraintSupportedRows 2
      (Polynomial.C ∘ supportedRankCenters) supportedRankReceived supportedRankColumns) :=
    Fintype.card_le_of_injective supportedRows hinj
  have hentry : supportedRankMatrix (supportedRows (0, 0)) (Fin.succ 0) = 1 := by
    change algebraMap ℚ[X] (RatFunc ℚ)
      (localConstraintMatrix 2 (Polynomial.C ∘ supportedRankCenters) supportedRankReceived
        supportedRankColumns (rawRows (0, 0)) (Fin.succ 0)) = 1
    rw [show rawRows (0, 0) = (0, rowZero) by rfl]
    rw [hzeroEntry 0]
    simp
  have hminor : supportedRankMatrix.submatrix (fun _ : Fin 1 => supportedRows (0, 0))
      (fun _ : Fin 1 => Fin.succ 0) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa using hentry
  have hminorRank : (supportedRankMatrix.submatrix (fun _ : Fin 1 => supportedRows (0, 0))
      (fun _ : Fin 1 => Fin.succ 0)).rank = 1 := by
    rw [hminor, Matrix.rank_one]
    simp
  have hlower : 1 ≤ supportedRankMatrix.rank := by
    calc
      1 = (supportedRankMatrix.submatrix (fun _ : Fin 1 => supportedRows (0, 0))
        (fun _ : Fin 1 => Fin.succ 0)).rank := hminorRank.symm
      _ ≤ supportedRankMatrix.rank := Matrix.rank_submatrix_le _ _ _
  exact ⟨hcolumns, by norm_num, by omega, hlower, hupper'⟩

/- The coefficient map acts on a nonintegral entry from a source `X` column. -/
example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 => (1 / 2 : ℚ)) (fun _ => 0)
      (fun _ : Fin 1 => (⟨1, 0, ![]⟩ : SourceColumn 0))).map (Rat.castHom ℝ)) =
      localConstraintMatrix 1 (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => 0)
        (fun _ : Fin 1 => (⟨1, 0, ![]⟩ : SourceColumn 0)) ∧
    localConstraintMatrix 1 (fun _ : Fin 1 => (1 / 2 : ℚ)) (fun _ => 0)
      (fun _ : Fin 1 => (⟨1, 0, ![]⟩ : SourceColumn 0)) matrixRowZero 0 = (1 / 2 : ℚ) := by
  have hmap := localConstraintMatrix_map (R := ℚ) (f := Rat.castHom ℝ) 1
    (fun _ : Fin 1 => (1 / 2 : ℚ)) (fun _ : Fin 1 => (0 : ℚ))
    (fun _ : Fin 1 => (⟨1, 0, ![]⟩ : SourceColumn 0))
  refine ⟨by simpa using hmap, ?_⟩
  rw [localConstraintMatrix_apply]
  rw [show matrixRowZero.2.1 = (0 : LocalVariable 0 →₀ ℕ) by rfl]
  have hcolumn : (⟨1, 0, ![]⟩ : SourceColumn 0).polynomial =
      (X none : DifferentialPolynomial ℚ 0) := by
    rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
    simp
  rw [hcolumn, unscaledLocalSubstitution_X]
  simp [localT]

end SymbolicPartitionRankTest
