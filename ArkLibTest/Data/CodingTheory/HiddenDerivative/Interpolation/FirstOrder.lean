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
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.ListBound
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Profile
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# First-order interpolation acceptance cases

Concrete dimension, support, membership, interpolation, rank, and graded matrix instances.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private noncomputable def smallFirstOrderRateParameters :
    FirstOrderFiniteRateParameters (1 / 2 : ℝ) 1 := by
  refine ⟨1, by norm_num, ?_⟩
  norm_num [FirstOrderFiniteRateTest, firstOrderRateDerivativeCap, firstOrderRateJetDegree,
    firstOrderRateBeta, firstOrderRankCount, firstOrderSourceCount, Finset.sum_range_succ]

private def smallFirstOrderCenters : Fin 2 ↪ ZMod 5 :=
  ⟨fun i ↦ i.val, by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

private noncomputable def smallFirstOrderRateCertificate :
    FirstOrderSymbolicCertificate (F := ZMod 5) 1 2
      smallFirstOrderRateParameters.multiplicity smallFirstOrderRateParameters.derivativeCap
      smallFirstOrderRateParameters.jetDegree 2 smallFirstOrderRateParameters.challengeDegree
      smallFirstOrderCenters (fun _ ↦ 0)
      (fun _ ↦ 0)
      (firstOrderColumns (D := 1) (A := 2)
        (m := smallFirstOrderRateParameters.multiplicity)
        (M := smallFirstOrderRateParameters.derivativeCap)
        (μ := smallFirstOrderRateParameters.jetDegree)) := by
  have hbudget : 0 < smallFirstOrderRateParameters.multiplicity * 2 :=
    Nat.mul_pos smallFirstOrderRateParameters.multiplicity_pos (by norm_num)
  exact Classical.choice (exists_firstOrderRate_symbolicCertificate
    (rate := (1 / 2 : ℝ)) (agreement := 1) (p := smallFirstOrderRateParameters)
    (F := ZMod 5) (n := 2) (D := 1) (A := 2) (k := 2)
    (by norm_num) (by norm_num) hbudget (by norm_num) (by norm_num) (by norm_num)
    smallFirstOrderCenters (fun _ ↦ 0) (fun _ ↦ 0))

/-- The concrete two-point rate choice has strict surplus over its interpolation dimension. -/
example :
    2 * smallFirstOrderRateParameters.rankCount < firstOrderDimensionCount 1 2
      smallFirstOrderRateParameters.multiplicity smallFirstOrderRateParameters.derivativeCap
      smallFirstOrderRateParameters.jetDegree := by
  exact smallFirstOrderRateParameters.rankCount_mul_lt_dimensionCount
    (by norm_num) (by norm_num) (by norm_num)

/-- The concrete two-point rate choice bounds its kernel-height quotient. -/
example :
    2 * smallFirstOrderRateParameters.rankCount * smallFirstOrderRateParameters.jetDegree /
      (firstOrderDimensionCount 1 2 smallFirstOrderRateParameters.multiplicity
        smallFirstOrderRateParameters.derivativeCap smallFirstOrderRateParameters.jetDegree -
        2 * smallFirstOrderRateParameters.rankCount) ≤
      smallFirstOrderRateParameters.challengeDegree := by
  exact smallFirstOrderRateParameters.kernelHeight_le_challengeDegree
    (by norm_num) (by norm_num)

/-- A finite first-order rate choice yields a line certificate and its curve form on two points. -/
example :
    Nonempty (FirstOrderCurveCertificate (F := ZMod 5) 1 2
      smallFirstOrderRateParameters.multiplicity smallFirstOrderRateParameters.derivativeCap
      smallFirstOrderRateParameters.jetDegree 2 smallFirstOrderRateParameters.challengeDegree
      smallFirstOrderCenters
      (fun _ ↦ receivedLine (0 : ZMod 5) 0)
      (firstOrderColumns (D := 1) (A := 2)
        (m := smallFirstOrderRateParameters.multiplicity)
        (M := smallFirstOrderRateParameters.derivativeCap)
        (μ := smallFirstOrderRateParameters.jetDegree))) := by
  exact ⟨smallFirstOrderRateCertificate.toCurve⟩

/-- The curve transfer applies to the two-point zero word and retains an agreeing candidate
outside its finite exceptional set. -/
example :
    ∃ exceptional : Finset (RatFunc (ZMod 5)),
      (exceptional.card : ℚ) ≤ firstOrderCurveBound 2 2 2 2 2
        smallFirstOrderRateParameters.jetDegree smallFirstOrderRateParameters.derivativeCap
        0 smallFirstOrderRateParameters.challengeDegree 0 1 ∧
      ∃ z ∉ exceptional, ∃ P : (RatFunc (ZMod 5))[X],
        P.degree < 2 ∧
        (∀ i ∈ (Finset.univ : Finset (Fin 2)),
          P.eval (algebraMap (ZMod 5) (RatFunc (ZMod 5)) (smallFirstOrderCenters i)) =
            (receivedLine (0 : ZMod 5) 0).eval₂
              (algebraMap (ZMod 5) (RatFunc (ZMod 5))) z) ∧
        P = 0 := by
  classical
  let cert := smallFirstOrderRateCertificate.toCurve
  have hnonzero : cert.Q ≠ 0 := by
    intro hzero
    have h := (cert.specialization_sound (E := ZMod 5) (RingHom.id _) 0).1
    rw [hzero, map_zero] at h
    exact h rfl
  have hjet : jetTotalDegree cert.Q ≤ smallFirstOrderRateParameters.jetDegree := by
    rw [jetTotalDegree_le_iff]
    exact cert.totalJetDegree_le
  have hchar : jetTotalDegree cert.Q < ringChar ((ZMod 5)[X]) := by
    calc
      jetTotalDegree cert.Q ≤ smallFirstOrderRateParameters.jetDegree := hjet
      _ < ringChar ((ZMod 5)[X]) := by
        rw [← Algebra.ringChar_eq (ZMod 5) ((ZMod 5)[X])]
        norm_num [smallFirstOrderRateParameters,
          FirstOrderFiniteRateParameters.jetDegree, firstOrderRateJetDegree,
          ZMod.ringChar_zmod_n]
  obtain ⟨stages, terminal, hchain⟩ :=
    PolynomialDifferential.exists_separantChain_of_ringChar hnonzero (Or.inr hchar)
  let ι : ZMod 5 →+* RatFunc (ZMod 5) := algebraMap _ _
  have hjoint : firstOrderCurveJointRatio 2 2 2 = 1 := by
    norm_num [firstOrderCurveJointRatio, firstOrderCurveIncidenceRatio]
  have hfiber : firstOrderCurveFiberRatio 2 2 2 = 1 := by
    norm_num [firstOrderCurveFiberRatio, firstOrderCurveIncidenceRatio]
  have hcharge (stage : SeparantStage (ZMod 5)[X] 1) :
      0 ≤ firstOrderCurveStageCharge 2 2 2 2 2 0
        smallFirstOrderRateParameters.challengeDegree stage 0 1 := by
    unfold firstOrderCurveStageCharge
    rw [hjoint, hfiber]
    change 0 ≤ firstOrderStageCharge
      (fun v ↦ orderZeroCurveStageCharge 0 smallFirstOrderRateParameters.challengeDegree
        1 0 v 0)
      (fun v r ↦ orderOneCurveStageCharge 2 0 smallFirstOrderRateParameters.challengeDegree
        1 1 0 v r 0 1) stage
    unfold firstOrderStageCharge
    split_ifs
    · exact orderZeroCurveStageCharge_nonneg (ell := 0)
        (h := smallFirstOrderRateParameters.challengeDegree) (s := 1) (c := 0)
        (by norm_num) (by norm_num) _ _
    · exact orderOneCurveStageCharge_nonneg (K := 2) (ell := 0)
        (h := smallFirstOrderRateParameters.challengeDegree) (s := 1) (η := 1) (t := 1)
        (c := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _
  have hregular : ∀ stage ∈ stages, ∃ exceptional : Finset (RatFunc (ZMod 5)),
      (exceptional.card : ℚ) ≤
        firstOrderCurveStageCharge 2 2 2 2 2 0
          smallFirstOrderRateParameters.challengeDegree stage 0 1 ∧
      ∀ z ∉ exceptional, ∀ (indices : Finset (Fin 2)) (P : (RatFunc (ZMod 5))[X]),
        P.degree < 2 → 2 ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (smallFirstOrderCenters i)) =
          (receivedLine (0 : ZMod 5) 0).eval₂ ι z) →
        differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 →
        differentialSpecialization
          (separant
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) stage.2) P ≠ 0 →
        P = 0 := by
    intro stage hstage
    refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, CharP.cast_eq_zero]
      exact hcharge stage
    · intro _ _ indices P hdegree hsize hagree _ _
      have hcard : indices.card = 2 := by
        have hle := Finset.card_le_univ indices
        simp only [Fintype.card_fin] at hle
        omega
      have hindices : indices = Finset.univ := by
        apply indices.card_eq_iff_eq_univ.mp
        simpa using hcard
      have hcenter0 : smallFirstOrderCenters 0 = 0 := by
        change ((0 : Fin 2).val : ZMod 5) = 0
        norm_num
      have hcenter1 : smallFirstOrderCenters 1 = 1 := by
        change ((1 : Fin 2).val : ZMod 5) = 1
        norm_num
      have hroot0 : P.eval (0 : RatFunc (ZMod 5)) = 0 := by
        simpa [hcenter0, receivedLine] using hagree 0 (by simp [hindices])
      have hroot1 : P.eval (1 : RatFunc (ZMod 5)) = 0 := by
        simpa [hcenter1, receivedLine] using hagree 1 (by simp [hindices])
      by_contra hP
      have hroots0 : (0 : RatFunc (ZMod 5)) ∈ P.roots :=
        (Polynomial.mem_roots hP).mpr hroot0
      have hroots1 : (1 : RatFunc (ZMod 5)) ∈ P.roots :=
        (Polynomial.mem_roots hP).mpr hroot1
      have hroots : 2 ≤ P.roots.card := by
        have hsubset : ({(0 : RatFunc (ZMod 5)), 1} : Finset (RatFunc (ZMod 5))) ⊆
            P.roots.toFinset := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Multiset.mem_toFinset.mpr hroots0
          · exact Multiset.mem_toFinset.mpr hroots1
        calc
          2 = ({(0 : RatFunc (ZMod 5)), 1} : Finset (RatFunc (ZMod 5))).card := by
            norm_num
          _ ≤ P.roots.toFinset.card := Finset.card_le_card hsubset
          _ ≤ P.roots.card := Multiset.toFinset_card_le _
      have hdegree' : P.natDegree < 2 :=
        (Polynomial.natDegree_lt_iff_degree_lt hP).mpr hdegree
      have hroots_le : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
      omega
  obtain ⟨exceptional, hbound, hgood⟩ :=
    cert.exists_exceptional_of_regular_stage_bounds_of_factors hchain ι
      2 2 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun _ P ↦ P = 0) hregular
  have hInfinite : Infinite (RatFunc (ZMod 5)) := by
    exact Infinite.of_injective (algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)))
      (IsFractionRing.injective _ _)
  have hcard : (exceptional.card : ENat) < ENat.card (RatFunc (ZMod 5)) := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.natCast_lt_top _
  obtain ⟨z, hz⟩ := Finset.exists_not_mem_of_card_lt_enatCard hcard
  refine ⟨exceptional, hbound, z, hz, 0, WithBot.bot_lt_coe 2, ?_, ?_⟩
  · intro i hi
    simp [receivedLine]
  · exact hgood z hz Finset.univ 0 (WithBot.bot_lt_coe 2) (by simp)
      (by intro i hi; simp [receivedLine])

/-- The shared specialization theorem applies directly to the nonzero two-point certificate. -/
example :
    ∃ Q : DifferentialPolynomial (ZMod 5)[X] 1,
      MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id (ZMod 5)) (0 : ZMod 5)) Q ≠ 0 ∧
        differentialSpecialization
          (MvPolynomial.map
            (Polynomial.eval₂RingHom (RingHom.id (ZMod 5)) (0 : ZMod 5)) Q)
          (0 : (ZMod 5)[X]) = 0 := by
  let cert := smallFirstOrderRateCertificate
  let ι : ZMod 5 →+* ZMod 5 := RingHom.id _
  refine ⟨cert.Q, cert.specialization_sound ι 0 |>.1, ?_⟩
  have hbudget : 0 < smallFirstOrderRateParameters.multiplicity * 2 :=
    Nat.mul_pos smallFirstOrderRateParameters.multiplicity_pos (by norm_num)
  have hagreements : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      (0 : (ZMod 5)[X]).eval (ι (smallFirstOrderCenters i)) =
        (receivedLine (0 : ZMod 5) 0).eval₂ ι 0 := by
    intro i hi
    simp [receivedLine]
  exact differentialSpecialization_eq_zero_of_firstOrderSpace
    (D := 1) (A := 2) (m := smallFirstOrderRateParameters.multiplicity)
    (M := smallFirstOrderRateParameters.derivativeCap)
    (μ := smallFirstOrderRateParameters.jetDegree) (k := 2) (n := 2)
    (by norm_num) hbudget smallFirstOrderCenters
    (fun _ ↦ receivedLine (0 : ZMod 5) 0) cert.Q cert.support cert.localConstraints ι 0
    Finset.univ 0 (by exact WithBot.bot_lt_coe 2) (by simp) hagreements

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

private def smallFirstOrderProfile :
    ReedSolomon.HiddenDerivative.CurveProfile.LineProfile :=
  { n := 2
    k := 2
    agreement := 2
    multiplicity := 2
    firstDerivativeCap := 0
    totalJetCap := 1
    batchingDegree := 1
    supportDimension := 7
    localRank := 3
    columnY₀Weight := 3
    height := 1
    heightSlots := 11 }

private theorem smallFirstOrderProfile_verified :
    smallFirstOrderProfile.Verification := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

private theorem smallFirstOrderProfile_curveVerified :
    smallFirstOrderProfile.CurveVerification := by
  decide

/-- A concrete profile verifies both line and curve certificates over a small finite field. -/
example :
    Nonempty (smallFirstOrderProfile.SymbolicCertificate
      smallFirstOrderCenters (fun _ ↦ 0) (fun _ ↦ 0)) ∧
    Nonempty (FirstOrderCurveCertificate (F := ZMod 5) 1 2 2 0 1 2 1
      smallFirstOrderCenters
      (fun _ ↦ (0 : (ZMod 5)[X])) smallFirstOrderProfile.columns) := by
  refine ⟨?_, ?_⟩
  · exact smallFirstOrderProfile_verified.exists_symbolicCertificate
      smallFirstOrderCenters (fun _ ↦ 0) (fun _ ↦ 0)
  · exact smallFirstOrderProfile_curveVerified.exists_certificate
      smallFirstOrderCenters (fun _ ↦ 0) (by intro i; simp)

/-- The profile's recorded dimension and column weight match its finite support. -/
example :
    (firstOrderExponents 1 2 2 0 1).card = 7 ∧
    firstOrderY₀Weight 1 2 2 0 1 = 3 := by
  exact ⟨by simpa [smallFirstOrderProfile,
      ReedSolomon.HiddenDerivative.CurveProfile.LineProfile.candidateDegree] using
      smallFirstOrderProfile_verified.support_card_eq,
    by simpa [smallFirstOrderProfile,
      ReedSolomon.HiddenDerivative.CurveProfile.LineProfile.candidateDegree] using
      smallFirstOrderProfile_verified.columnY₀Weight_eq.symm⟩

private noncomputable def smallFirstOrderAgreementList : Finset (ZMod 5)[X] := {0}

private theorem smallFirstOrderAgreementList_accepted :
    ∀ P ∈ smallFirstOrderAgreementList,
      P.degree < 1 ∧
        2 ≤ ({i : Fin 2 | P.eval (smallFirstOrderCenters i) = (0 : ZMod 5)} :
          Set (Fin 2)).ncard := by
  classical
  intro P hP
  have hPzero : P = 0 := by simpa [smallFirstOrderAgreementList] using hP
  subst P
  constructor
  · simp
  · simp [smallFirstOrderCenters]

private theorem smallFirstOrderAgreementCertificate :
    Nonempty (FirstOrderSymbolicCertificate (F := ZMod 5) 1 2 2 0 1 1 1
      smallFirstOrderCenters (fun _ ↦ 0) (fun _ ↦ 0)
      (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1))) := by
  have hheight : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 := by decide
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := ZMod 5) (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) (k := 1) (h := 1)
    (n := 2) (by decide) (by norm_num) (by norm_num) smallFirstOrderCenters
    (fun _ ↦ 0) (fun _ ↦ 0) hheight

/-- A concrete symbolic certificate gives the sharp cap-sensitive agreement bound. -/
example :
    (smallFirstOrderAgreementList.card : ℚ) ≤
      ((2 * firstOrderListWeight 2 1 0 : ℕ) : ℚ) / ((2 - 1 + 1 : ℕ) : ℚ) := by
  have hchar : ringChar (ZMod 5) = 0 ∨ max (2 - 1) 1 < ringChar (ZMod 5) := by
    right
    rw [ZMod.ringChar_zmod_n]
    norm_num
  obtain ⟨cert⟩ := smallFirstOrderAgreementCertificate
  exact firstOrder_finite_agreement_solutions_card_le_sharp
    smallFirstOrderCenters (fun _ ↦ 0)
    (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1)) cert
    (by decide) (by decide) (by decide) (by decide) (by decide) hchar
    smallFirstOrderAgreementList smallFirstOrderAgreementList_accepted

/-- A sufficient exponent gives the dimension-sensitive agreement bound. -/
example :
    (smallFirstOrderAgreementList.card : ℚ) ≤
      firstOrderTightListWeight 2 2 1 2 1 1 0 := by
  have hchar : ringChar (ZMod 5) = 0 ∨ max (2 - 1) 1 < ringChar (ZMod 5) := by
    right
    rw [ZMod.ringChar_zmod_n]
    norm_num
  obtain ⟨cert⟩ := smallFirstOrderAgreementCertificate
  exact firstOrder_finite_agreement_solutions_card_le_tight
    smallFirstOrderCenters (fun _ ↦ 0)
    (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1)) cert
    (by decide) (by decide) (by decide) (by decide) (by decide) hchar
    smallFirstOrderAgreementList smallFirstOrderAgreementList_accepted

/-- A nonstandard sufficient Taylor exponent gives the dimension-sensitive agreement bound. -/
example :
    (smallFirstOrderAgreementList.card : ℚ) ≤
      firstOrderTightListWeight 2 2 1 2 4 1 0 := by
  have hchar : ringChar (ZMod 5) = 0 ∨ max (2 - 1) 1 < ringChar (ZMod 5) := by
    right
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hτ : ∀ r ≤ 1, TaylorExponentSufficient r 2 4 := by
    intro r hr
    exact (taylorExponentSufficient_two_mul r 2).mono (by decide)
  obtain ⟨cert⟩ := smallFirstOrderAgreementCertificate
  exact firstOrder_finite_agreement_solutions_card_le_tight_of_exponent
    smallFirstOrderCenters (fun _ ↦ 0)
    (firstOrderColumns (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1)) cert hτ
    (by decide) (by decide) (by decide) (by decide) (by decide) hchar
    smallFirstOrderAgreementList smallFirstOrderAgreementList_accepted

/-- A concrete shifted-slot surplus gives the sharp cap-sensitive agreement bound. -/
example :
    (smallFirstOrderAgreementList.card : ℚ) ≤
      ((2 * firstOrderListWeight 2 1 0 : ℕ) : ℚ) / ((2 - 1 + 1 : ℕ) : ℚ) := by
  have hchar : ringChar (ZMod 5) = 0 ∨ max (2 - 1) 1 < ringChar (ZMod 5) := by
    right
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hheight : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 := by decide
  exact finite_firstOrder_list_bound_of_heightSlotCount_sharp
    (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) (k := 1) (h := 1) (n := 2)
    (K := 2) (by decide) (by norm_num) (by norm_num) smallFirstOrderCenters
    (fun _ ↦ 0) hheight (by decide) (by decide) (by decide) (by decide) (by decide)
    hchar smallFirstOrderAgreementList smallFirstOrderAgreementList_accepted

/-- A concrete shifted-slot surplus gives the dimension-sensitive agreement bound. -/
example :
    (smallFirstOrderAgreementList.card : ℚ) ≤
      firstOrderTightListWeight 2 2 1 2 1 1 0 := by
  have hchar : ringChar (ZMod 5) = 0 ∨ max (2 - 1) 1 < ringChar (ZMod 5) := by
    right
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hheight : firstOrderCurveShiftedRowSlotBound 1 2 2 0 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 2 0 1 1 1 := by decide
  exact finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight
    (D := 1) (A := 2) (m := 2) (M := 0) (μ := 1) (k := 1) (h := 1) (n := 2)
    (K := 2) (by decide) (by norm_num) (by norm_num) smallFirstOrderCenters
    (fun _ ↦ 0) hheight (by decide) (by decide) (by decide) (by decide) (by decide)
    hchar smallFirstOrderAgreementList smallFirstOrderAgreementList_accepted
