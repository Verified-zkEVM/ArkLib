/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Interpolant
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Space
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Symbolic
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
import Mathlib.Algebra.Field.ZMod

/-!
# First-order interpolation acceptance cases

Concrete dimension, support, membership, interpolation, rank, and graded matrix instances.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : Module.finrank ℚ (firstOrderSpace ℚ 2 3 1 0 1) = 4 := by
  rw [finrank_firstOrderSpace_eq_firstOrderDimensionCount ℚ (by norm_num)]
  decide

example : firstOrderColumnSlotCount 2 3 1 0 1 1 = 7 := by
  rw [firstOrderColumnSlotCount_eq_heightSlotCount (D := 2) (A := 3) (m := 1) (M := 0)
    (μ := 1) (h := 1) (by omega)]
  decide

private theorem firstOrderHeightOne : firstOrderCertificateHeight 2 3 1 0 1 1 = 1 := by
  have hcard : (firstOrderExponents 2 3 1 0 1).card = 4 := by
    rw [card_firstOrderExponents (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) (by omega)]
    decide
  have hslots : firstOrderColumnSlotCount 2 3 1 0 1 1 = 7 := by
    rw [firstOrderColumnSlotCount_eq_heightSlotCount (D := 2) (A := 3) (m := 1) (M := 0)
      (μ := 1) (h := 1) (by omega)]
    decide
  have hweight : (firstOrderExponents 2 3 1 0 1).sum (fun u ↦ u (some 0)) = 1 := by
    have h := firstOrderColumnSlotCount_add_y₀Weight (D := 2) (A := 3) (m := 1) (M := 0)
      (μ := 1) (h := 1) (by omega)
    rw [hslots, hcard] at h
    dsimp [firstOrderY₀Weight] at h
    omega
  change max 1 ((firstOrderExponents 2 3 1 0 1).sum (fun u ↦ u (some 0)) /
    ((firstOrderExponents 2 3 1 0 1).card - 1)) = 1
  rw [hweight, hcard]
  decide

example : 2 < firstOrderHeightSlotCount 2 3 1 0 1 1 := by
  have hcard : (firstOrderExponents 2 3 1 0 1).card = 4 := by
    rw [card_firstOrderExponents (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) (by omega)]
    decide
  have h := firstOrder_rowTotal_mul_height_lt_heightSlotCount (D := 2) (A := 3) (m := 1)
    (M := 0) (μ := 1) (rowTotal := 1) (by omega) (by rw [hcard]; decide)
  simpa [firstOrderHeightOne] using h

example : ∃ i j : Fin (Fintype.card ↑(firstOrderExponents 2 3 1 0 1)),
    i.val = 0 ∧ j.val = 1 ∧
      firstOrderColumns (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) i ≠
        firstOrderColumns (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) j := by
  have hcard : Fintype.card ↑(firstOrderExponents 2 3 1 0 1) = 4 := by
    rw [Fintype.card_coe,
      card_firstOrderExponents (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) (by omega)]
    decide
  let i : Fin (Fintype.card ↑(firstOrderExponents 2 3 1 0 1)) := ⟨0, by omega⟩
  let j : Fin (Fintype.card ↑(firstOrderExponents 2 3 1 0 1)) := ⟨1, by omega⟩
  refine ⟨i, j, by simp [i], by simp [j], ?_⟩
  intro h
  have hij := firstOrderColumns_injective (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) h
  have hval := congrArg Fin.val hij
  norm_num [i, j] at hval

private def firstOrderBoundaryColumns : Fin 2 → SourceColumn 1 := fun j =>
  if j = 0 then ⟨0, 0, fun _ => 0⟩ else ⟨0, 1, fun _ => 0⟩

example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 ↦ Polynomial.C (0 : ℚ))
      (fun _ ↦ (Polynomial.X ^ 2 : ℚ[X])) firstOrderBoundaryColumns).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 := by
  have heligible : ∀ j,
      (firstOrderBoundaryColumns j).exponent ∈ firstOrderExponents 0 1 1 0 1 := by
    intro j
    rw [mem_firstOrderExponents_iff_coordinates]
    fin_cases j <;> simp [firstOrderBoundaryColumns, SourceColumn.exponent]
  exact (rank_firstOrderLocalConstraintMatrix_le (D := 0) (A := 1) (m := 1) (M := 0)
    (μ := 1) (centers := fun _ ↦ (0 : ℚ))
    (received := fun _ ↦ (Polynomial.X ^ 2 : ℚ[X]))
    firstOrderBoundaryColumns heligible).trans (by decide)

example : Finsupp.single none 1 + Finsupp.single (some 0) 1 ∈
    firstOrderExponents 2 2 2 0 1 := by
  rw [mem_firstOrderExponents_iff_coordinates]
  simp

example : monomial (Finsupp.single (some 1) 1) (1 : ℚ) ∈ firstOrderSpace ℚ 2 2 1 1 1 ∧
    monomial (Finsupp.single (some 1) 1) (1 : ℚ) ∈
      exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num) := by
  have hmem : monomial (Finsupp.single (some 1) 1) (1 : ℚ) ∈ firstOrderSpace ℚ 2 2 1 1 1 := by
    rw [monomial_mem_firstOrderSpace, ← mem_firstOrderExponents,
      mem_firstOrderExponents_iff_coordinates]
    simp
  exact ⟨hmem, firstOrderSpace_le_exactInterpolationSpace (D := 2) (A := 2) (m := 1)
    (M := 1) (μ := 1) (W := 0) (by norm_num) hmem⟩

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ firstOrderSpace ℚ 2 3 1 0 1 ∧
      ∀ _ : Fin 3, SatisfiesLocalConstraints 1 0 0 Q := by
  apply exists_nonzero_firstOrder_interpolant_of_dimensionCount (by norm_num)
    (fun _ : Fin 3 => (0 : ℚ)) (fun _ => 0)
  decide

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ firstOrderSpace ℚ 2 3 1 0 1 ∧
      (Polynomial.X - Polynomial.C (0 : ℚ)) ^ 1 ∣
        differentialSpecialization Q (0 : Polynomial ℚ) := by
  have hdim : Fintype.card (Fin 3) * certifiedEnlargedRankBound 1 1 0 0 <
      (firstOrderExponents 2 3 1 0 1).card := by
    rw [card_firstOrderExponents (by norm_num)]
    decide
  obtain ⟨Q, hQ0, hQspace, hdiv⟩ :=
    exists_nonzero_firstOrder_interpolant_X_sub_C_pow_dvd
      (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1)
      (fun _ : Fin 3 => (0 : ℚ)) (fun _ => 0) hdim
  exact ⟨Q, hQ0, hQspace, hdiv 0 0 (by simp)⟩

private def constantSourceColumnsTwo : Fin 1 → SourceColumn 2 :=
  fun _ => ⟨0, 0, fun _ => 0⟩

private def constantSourceColumnsOne : Fin 1 → SourceColumn 1 :=
  fun _ => ⟨0, 0, fun _ => 0⟩

/-- The coefficient-height theorem applies to two derivative variables. -/
example :
    ∀ u, ((SourceColumn.interpolant constantSourceColumnsTwo
      (fun _ ↦ (1 : (ZMod 5)[X]))).coeff u).natDegree ≤ 0 := by
  exact SourceColumn.coeff_interpolant_natDegree_le constantSourceColumnsTwo
    (by intro i j _; exact Subsingleton.elim _ _) (fun _ ↦ (1 : (ZMod 5)[X]))
    (by intro j; norm_num)

/-- A constant source column assembles to a polynomial in the finite first-order support. -/
example :
    SourceColumn.interpolant constantSourceColumnsOne
      (fun _ ↦ (1 : (ZMod 5)[X])) ∈ firstOrderSpace (ZMod 5)[X] 1 1 1 0 0 := by
  apply interpolant_mem_firstOrderSpace
  · intro j
    rw [mem_firstOrderExponents_iff_coordinates]
    simp [constantSourceColumnsOne, SourceColumn.exponent]

/-- A nonzero multiple-root interpolant satisfies the one-point local constraint. -/
example :
    ∃ v : Fin (Fintype.card ↑(firstOrderExponents 1 2 1 0 0)) → (ZMod 5)[X],
      v ≠ 0 ∧
      SourceColumn.interpolant
        (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0)) v ≠ 0 ∧
      (firstOrderCurveGradedConstraintMatrix 1 2 1 0 0 1
        (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X])) *ᵥ v) = 0 ∧
      ∀ _i : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ZMod 5))
        (0 : (ZMod 5)[X])
        (SourceColumn.interpolant
          (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0)) v) := by
  classical
  let columns := firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0)
  let sourceX : SourceColumn 1 := ⟨1, 0, fun _ => 0⟩
  have hsourceX : sourceX.exponent ∈ firstOrderExponents 1 2 1 0 0 := by
    rw [mem_firstOrderExponents_iff_coordinates]
    simp [sourceX, SourceColumn.exponent]
  let indexX : Fin (Fintype.card ↑(firstOrderExponents 1 2 1 0 0)) :=
    Fintype.equivFin ↑(firstOrderExponents 1 2 1 0 0) ⟨sourceX.exponent, hsourceX⟩
  let v : Fin (Fintype.card ↑(firstOrderExponents 1 2 1 0 0)) → (ZMod 5)[X] :=
    fun j => if j = indexX then 1 else 0
  have hcolumn : columns indexX = sourceX := by
    apply SourceColumn.exponent_injective
    rw [firstOrderColumns_exponent]
    simp [indexX]
  have hv : v ≠ 0 := by
    intro hv
    have hvalue := congrFun hv indexX
    simp [v] at hvalue
  have hinterpolant : SourceColumn.interpolant columns v = sourceX.polynomial := by
    rw [SourceColumn.interpolant_eq_sum_smul]
    simp [v, hcolumn]
  have hnonzero : SourceColumn.interpolant columns v ≠ 0 := by
    intro hzero
    have hcolumns : Function.Injective columns := by
      simpa [columns] using
        (firstOrderColumns_injective (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0))
    exact hv ((SourceColumn.interpolant_eq_zero_iff hcolumns).mp hzero)
  have hsatisfies : ∀ _i : Fin 1, SatisfiesLocalConstraints 1
      (Polynomial.C (0 : ZMod 5)) (0 : (ZMod 5)[X])
      (SourceColumn.interpolant columns v) := by
    intro _i
    rw [SatisfiesLocalConstraints, hinterpolant]
    apply MvPolynomial.ext
    intro e
    rw [SourceColumn.polynomial_eq_sourceMonomial]
    by_cases hlow : localContactOrder 1 e < 1
    · have hT : e (localT 1) ≠ 1 := by
        change e none ≠ 1
        rw [localContactOrder_one] at hlow
        simp only [localT, localE] at hlow
        omega
      simpa [sourceX] using
        (coeff_localConstraintAt_zero_sourceMonomial_eq_zero_of_T_degree_ne
          (R := (ZMod 5)[X]) 1 1 0 (fun _ : Fin 1 ↦ 0) e hT)
    · simp [localConstraintAt, hlow]
  have hkernel :
      (firstOrderCurveGradedConstraintMatrix 1 2 1 0 0 1
        (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X])) *ᵥ v) = 0 :=
    (firstOrderCurveGradedConstraintMatrix_kernel_iff 1 2 1 0 0 1 (by decide)
      (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X])) v).2 hsatisfies
  exact ⟨v, hv, hnonzero, hkernel, hsatisfies⟩

/-- The small origin rank profile is bounded by its numerical profile. -/
example : firstOrderOriginGradedRank (F := ZMod 5) 1 1 1 0 0 ≤ 1 := by
  simpa [firstOrderGradedRankBound, firstOrderGradedSourceCount] using
    firstOrderOriginGradedRank_le_bound (F := ZMod 5) 1 1 1 0 0

/-- The shifted profile has eleven source slots and a numerical row bound of five. -/
example :
    firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 = 11 ∧
    firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 1 1 1 = 5 ∧
    firstOrderCurveShiftedColumnSlotCount 1 2 2 0 1 1 1 = 11 ∧
    firstOrderCurveShiftedRowSlotCount (F := ZMod 5) 1 2 2 0 1 1 1 1 ≤ 5 := by
  have hheight : firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 = 11 := by decide
  have hbound : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 1 1 1 = 5 := by decide
  refine ⟨hheight, hbound, ?_, ?_⟩
  · rw [firstOrderCurveShiftedColumnSlotCount_eq_heightSlotCount
      (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) (ℓ := 1) (h := 1) (by decide)]
    exact hheight
  · exact (firstOrderCurveShiftedRowSlotCount_le_bound
      (F := ZMod 5) 1 2 2 0 1 1 1 1).trans_eq hbound

/-- An exact shifted surplus produces a primitive first-order curve interpolant. -/
example :
    ∃ v : Fin (Fintype.card ↑(firstOrderExponents 1 2 2 0 1)) → (ZMod 5)[X],
      v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT (ZMod 5)
        (1 + 1 - 1 * totalJetDegree
          (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) j).exponent)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : ZMod 5 →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z)
          (SourceColumn.interpolant
            (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1)) v) ≠ 0) ∧
      ∀ _i : Fin 1, SatisfiesLocalConstraints 2 (Polynomial.C (0 : ZMod 5))
        (0 : (ZMod 5)[X])
        (SourceColumn.interpolant
          (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1)) v) := by
  have hnum : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 1 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 := by decide
  have hsurplus : FirstOrderCurveShiftedHeightSurplus (ZMod 5) 1 2 2 0 1 1 1 1 := by
    unfold FirstOrderCurveShiftedHeightSurplus
    rw [firstOrderCurveShiftedColumnSlotCount_eq_heightSlotCount
      (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) (ℓ := 1) (h := 1) (by decide)]
    exact (firstOrderCurveShiftedRowSlotCount_le_bound
      (F := ZMod 5) 1 2 2 0 1 1 1 1).trans_lt hnum
  exact exists_primitive_firstOrderCurve_interpolant_of_shifted_height
    (F := ZMod 5) 1 2 2 0 1 1 1 1 (by decide)
    (fun _ ↦ 0) (fun _ ↦ 0) (by intro _; norm_num) hsurplus

/-- A numerical shifted surplus also produces a primitive first-order curve interpolant. -/
example :
    ∃ v : Fin (Fintype.card ↑(firstOrderExponents 1 2 2 0 1)) → (ZMod 5)[X],
      v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT (ZMod 5)
        (1 + 1 - 1 * totalJetDegree
          (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) j).exponent)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : ZMod 5 →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z)
          (SourceColumn.interpolant
            (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1)) v) ≠ 0) ∧
      ∀ _i : Fin 1, SatisfiesLocalConstraints 2 (Polynomial.C (0 : ZMod 5))
        (0 : (ZMod 5)[X])
        (SourceColumn.interpolant
          (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1)) v) := by
  have hsurplus : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 1 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 := by decide
  exact exists_primitive_firstOrderCurve_interpolant_of_shifted_height_bound
    (F := ZMod 5) 1 2 2 0 1 1 1 1 (by decide)
    (fun _ ↦ 0) (fun _ ↦ 0) (by intro _; norm_num) hsurplus

/-- A strict shifted-slot surplus constructs a certificate on two distinct received points. -/
example :
    ∃ centers : Fin 2 ↪ ZMod 5,
      Nonempty (FirstOrderCurveCertificate (F := ZMod 5) 1 2 2 0 1 2 1 centers
        (fun _ ↦ (0 : (ZMod 5)[X]))
        (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1))) := by
  let centers : Fin 2 ↪ ZMod 5 := ⟨fun i ↦ i.val, by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  refine ⟨centers, ?_⟩
  have hheight : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 := by decide
  exact exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    (F := ZMod 5) (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) (k := 2)
    (h := 1) (n := 2) (ℓ := 1) (by decide) (by norm_num) (by norm_num) centers
    (fun _ ↦ 0) (by intro _; norm_num) hheight

private theorem originConstantSlice_rank :
    (firstOrderOriginGradedSliceMatrixOver ℚ 1 2 1 1 0 0).rank = 1 := by
  have hmatrix : firstOrderOriginGradedSliceMatrixOver ℚ 1 2 1 1 0 0 =
      fun _ _ ↦ (1 : ℚ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [firstOrderOriginGradedSliceMatrixOver, firstOrderGradedTargetExponent,
      firstOrderGradedSourceColumn, localConstraintAt, SourceColumn.polynomial,
      SourceColumn.exponent, localT, localE, localY, localContactOrder_one]
  rw [hmatrix]
  change Matrix.rank (fun (_ : Fin 1) (_ : Fin 1) ↦ (1 : ℚ)) = 1
  have hconst : (fun (_ : Fin 1) (_ : Fin 1) ↦ (1 : ℚ) : Matrix (Fin 1) (Fin 1) ℚ) =
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hconst]
  change Matrix.rank (1 : Matrix (Fin 1) (Fin 1) ℚ) = 1
  rw [Matrix.rank_one]
  simp

private theorem originJetSlice_rank :
    (firstOrderOriginGradedSliceMatrixOver ℚ 1 2 2 0 1 1).rank = 1 := by
  have hmatrix : firstOrderOriginGradedSliceMatrixOver ℚ 1 2 2 0 1 1 =
      fun _ _ ↦ (1 : ℚ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [firstOrderOriginGradedSliceMatrixOver, firstOrderGradedTargetExponent,
      firstOrderGradedSourceColumn, localConstraintAt, SourceColumn.polynomial,
      SourceColumn.exponent, ← MvPolynomial.X_pow_eq_monomial,
      unscaledLocalSubstitution_Y_zero, localCorrection, localT, localE, localY,
      localAux, localContactOrder_one, MvPolynomial.coeff_mul_X]
  rw [hmatrix]
  change Matrix.rank (fun (_ : Fin 1) (_ : Fin 1) ↦ (1 : ℚ)) = 1
  have hconst : (fun (_ : Fin 1) (_ : Fin 1) ↦ (1 : ℚ) : Matrix (Fin 1) (Fin 1) ℚ) =
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hconst]
  change Matrix.rank (1 : Matrix (Fin 1) (Fin 1) ℚ) = 1
  rw [Matrix.rank_one]
  simp

private noncomputable def degreeBoundExampleRow :
    FirstOrderCurveGradedRowIndex ℚ 1 2 1 1 1 1 := by
  refine ⟨0, ⟨⟨0, by decide⟩, ⟨⟨0, by decide⟩, ?_⟩⟩⟩
  refine ⟨0, ?_⟩
  rw [originConstantSlice_rank]
  decide

private noncomputable def zeroEntryExampleRow :
    FirstOrderCurveGradedRowIndex ℚ 1 2 2 0 1 1 := by
  refine ⟨0, ⟨⟨1, by decide⟩, ⟨⟨1, by decide⟩, ?_⟩⟩⟩
  refine ⟨0, ?_⟩
  rw [originJetSlice_rank]
  decide

/-- A degree-one received curve gives a degree-one flattened matrix entry. -/
example :
    ∃ i j,
      (firstOrderCurveGradedFinMatrix 1 2 1 1 1 1
        (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (Polynomial.X : ℚ[X])) i j) =
          Polynomial.X ∧
        (firstOrderCurveGradedFinMatrix 1 2 1 1 1 1
          (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (Polynomial.X : ℚ[X])) i j).natDegree ≤
          1 := by
  classical
  let row := degreeBoundExampleRow
  let i := Fintype.equivFin (FirstOrderCurveGradedRowIndex ℚ 1 2 1 1 1 1) row
  let u : JetVariable 1 →₀ ℕ := Finsupp.single (some 0) 1
  have hu : u ∈ firstOrderExponents 1 2 1 1 1 := by
    rw [mem_firstOrderExponents_iff_coordinates]
    simp [u]
  let j := Fintype.equivFin ↑(firstOrderExponents 1 2 1 1 1) ⟨u, hu⟩
  have hcolumn : firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1) j =
      ⟨0, 1, fun _ ↦ 0⟩ := by
    apply SourceColumn.exponent_injective
    rw [firstOrderColumns_exponent]
    simp [j, u, SourceColumn.exponent]
  have hi : (Fintype.equivFin
      (FirstOrderCurveGradedRowIndex ℚ 1 2 1 1 1 1)).symm i = row := by
    dsimp [i]
    exact Equiv.symm_apply_apply _ _
  have hs : row.2.2.1.val = 0 := by simp [row, degreeBoundExampleRow]
  have ht : row.2.1.val = 0 := by simp [row, degreeBoundExampleRow]
  have hselected : firstOrderOriginGradedSelectedRow ℚ 1 2 1 1
      row.2.2.1.val row.2.1.val
      row.2.2.2 = ⟨0, by rw [hs, ht]; decide⟩ := by
    have hsize : min (1 - row.2.2.1.val) (row.2.1.val + 1) = 1 := by
      rw [hs, ht]
      decide
    exact @Subsingleton.elim _ (by rw [hsize]; infer_instance) _ _
  have hw : ∀ k : Fin 1, ((Polynomial.X : ℚ[X])).natDegree ≤ 1 := by
    intro k
    simp
  have hentry :
    firstOrderCurveGradedFinMatrix 1 2 1 1 1 1
        (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (Polynomial.X : ℚ[X])) i j =
          Polynomial.X := by
    change firstOrderCurveGradedConstraintMatrix 1 2 1 1 1 1
      (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (Polynomial.X : ℚ[X]))
      ((Fintype.equivFin (FirstOrderCurveGradedRowIndex ℚ 1 2 1 1 1 1)).symm i) j = _
    rw [hi]
    rw [firstOrderCurveGradedConstraintMatrix, firstOrderCurveGradedRowLocalIndex,
      hselected]
    simp [firstOrderGradedTargetLowContactIndex, localConstraintMatrix_apply,
      SourceColumn.polynomial, SourceColumn.exponent, ← MvPolynomial.X_pow_eq_monomial,
      j, u, hcolumn, ht, MvPolynomial.coeff_mul_X', unscaledLocalSubstitution_Y_zero,
      localCorrection,
      firstOrderGradedTargetExponent, localT, localE, localY, localAux]
  have hdegree := firstOrderCurveGradedFinMatrix_degree_le
    (F := ℚ) 1 2 1 1 1 1 1 (fun _ ↦ (0 : ℚ))
    (fun _ ↦ (Polynomial.X : ℚ[X])) hw i j
  have hjet : totalJetDegree (firstOrderColumns j).exponent = 1 := by
    rw [SourceColumn.totalJetDegree_exponent, hcolumn]
    simp
  have hrow : firstOrderCurveGradedFinRowWeight ℚ 1 2 1 1 1 1 1 i = 0 := by
    rw [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight, hi]
    simp [row, degreeBoundExampleRow]
  rw [hjet, hrow, hentry] at hdegree
  rw [show 1 * 1 - 0 = 1 by decide] at hdegree
  rw [← hentry] at hdegree
  exact ⟨i, j, hentry, hdegree⟩

/-- A row of jet grade one vanishes on the constant source column. -/
example :
    ∃ i j,
      1 * totalJetDegree
          (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) j).exponent <
        firstOrderCurveGradedFinRowWeight ℚ 1 2 2 0 1 1 1 i ∧
      firstOrderCurveGradedFinMatrix 1 2 2 0 1 1
        (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (Polynomial.X : ℚ[X])) i j = 0 := by
  classical
  let row := zeroEntryExampleRow
  let i := Fintype.equivFin (FirstOrderCurveGradedRowIndex ℚ 1 2 2 0 1 1) row
  let u : JetVariable 1 →₀ ℕ := 0
  have hu : u ∈ firstOrderExponents 1 2 2 0 1 := by
    rw [mem_firstOrderExponents_iff_coordinates]
    simp [u]
  let j := Fintype.equivFin ↑(firstOrderExponents 1 2 2 0 1) ⟨u, hu⟩
  have hcolumn : firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) j =
      ⟨0, 0, fun _ ↦ 0⟩ := by
    apply SourceColumn.exponent_injective
    rw [firstOrderColumns_exponent]
    simp [j, u, SourceColumn.exponent]
  have hi : (Fintype.equivFin
      (FirstOrderCurveGradedRowIndex ℚ 1 2 2 0 1 1)).symm i = row := by
    dsimp [i]
    exact Equiv.symm_apply_apply _ _
  have hjet : totalJetDegree
      (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) j).exponent = 0 := by
    rw [SourceColumn.totalJetDegree_exponent, hcolumn]
    simp
  have hweight : 1 * totalJetDegree
      (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) j).exponent <
        firstOrderCurveGradedFinRowWeight ℚ 1 2 2 0 1 1 1 i := by
    rw [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight, hi, hjet]
    simp [zeroEntryExampleRow, row]
  exact ⟨i, j, hweight,
    firstOrderCurveGradedFinMatrix_eq_zero_of_weight_lt
      1 2 2 0 1 1 1 (fun _ ↦ (0 : ℚ)) (fun _ ↦ (Polynomial.X : ℚ[X])) i j hweight⟩

/-- A concrete shifted surplus gives a symbolic certificate for received lines. -/
example :
    ∃ centers : Fin 2 ↪ ZMod 5,
      Nonempty (FirstOrderSymbolicCertificate (F := ZMod 5) 1 2 2 0 1 1 1 centers
        (fun _ ↦ 0) (fun _ ↦ 0)
        (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1))) := by
  let centers : Fin 2 ↪ ZMod 5 := ⟨fun i ↦ i.val, by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  refine ⟨centers, ?_⟩
  have hheight : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 := by decide
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := ZMod 5) (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) (k := 1) (h := 1)
    (n := 2) (by decide) (by norm_num) (by norm_num) centers (fun _ ↦ 0) (fun _ ↦ 0)
    hheight
