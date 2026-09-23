/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Counting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Certificates
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FreeOrderDimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Space
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SourceMonomial
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SpecializationDegree
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SolutionEmbedding

/-!
# Hidden-derivative interpolation acceptance cases

Small count, dimension, exponent, and homogeneous-monomial instances for the main interpolation
statements.
-/

open Finset MvPolynomial PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative
  ListDecoding

namespace CertificatesTest

private theorem satisfiesLocalConstraintsOneYZeroSub {R : Type*} [CommRing R] (center r : R) :
    SatisfiesLocalConstraints (d := 0) 1 center r (X (some 0) - C r) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply, projectLowContact,
    weightedTruncation_eq_zero_iff]
  have h : (unscaledLocalSubstitution 0 center r).toLinearMap (X (some 0) - C r) =
      X (localT 0) * (X (localE 0) + localJetSum 0) := by
    simp only [AlgHom.toLinearMap_apply, map_sub, unscaledLocalSubstitution_Y_zero, algHom_C,
      algebraMap_eq, mul_add, T_mul_localJetSum]
    ring
  rw [h]
  simpa using mul_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := R) (localContactWeight 0) (localT 0) le_rfl)
    (by simp : X (localE 0) + localJetSum 0 ∈
      restrictWeightedOrder (R := R) (localContactWeight 0) 0)

private theorem differentialWeightedDegreeYZeroSubLe {R : Type*} [CommRing R] (r : R) :
    differentialWeightedDegree 1 (X (some 0) - C r : DifferentialPolynomial R 0) ≤ 1 := by
  rw [differentialWeightedDegree, ← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  refine Submodule.sub_mem _ (X_mem_restrictWeightedDegree _ _ _ ?_) ?_
  · simp [differentialWeight]
  · rw [mem_restrictWeightedDegree_iff_weightedTotalDegree_le, weightedTotalDegree_C]
    exact Nat.zero_le _

private theorem YZeroSubNeZero {R : Type*} [CommRing R] [Nontrivial R] (r : R) :
    (X (some 0) - C r : DifferentialPolynomial R 0) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun _ ↦ r + 1)) h
  simp at this

private noncomputable def constantCertificate {R : Type*} [CommRing R] [Nontrivial R]
    (domain : Fin 2 ↪ R) (r : R) :
    InterpolationCertificate 2 2 0 1 domain (fun _ ↦ r) where
  ambientDim := 2
  messageDim_le := le_rfl
  ambientDim_le := by simp
  order_lt_degree := by decide
  interpolant := X (some 0) - C r
  nonzero := YZeroSubNeZero r
  weighted_degree_lt := (differentialWeightedDegreeYZeroSubLe r).trans_lt (by decide)
  local_constraints := fun i ↦ satisfiesLocalConstraintsOneYZeroSub (domain i) r

private noncomputable def zmodDomain : Fin 2 ↪ ZMod 5 :=
  ⟨fun i ↦ ((i : ℕ) : ZMod 5), by intro a b h; revert a b h; decide⟩

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem jetDegreeYZeroSubLe {R : Type*} [CommRing R] (r : R) (j : Fin 1) :
    jetDegree (X (some 0) - C r : DifferentialPolynomial R 0) j ≤ 1 := by
  rw [jetDegree]
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · exact (degreeOf_X_le _ _).trans le_rfl
  · simp

private noncomputable def zmodCertificate (r : ZMod 5) :
    HiddenDerivativeInterpolationCertificate (k := 2) (A := 2) 0 1 zmodDomain (fun _ ↦ r) where
  toInterpolationCertificate := constantCertificate zmodDomain r
  castsNeZero := fun j k hk hkj ↦ by
    have : k = 1 := by
      have := jetDegreeYZeroSubLe r j
      simp only [constantCertificate] at hkj
      omega
    subst this
    decide
  contact_budget_le := by decide

end CertificatesTest

open CertificatesTest

private theorem zeroMessageAgrees : 2 ≤ Code.agree
    (ReedSolomon.evalOnPoints zmodDomain (0 : MessagePolynomial (ZMod 5) 2))
    (fun _ : Fin 2 ↦ (0 : ZMod 5)) := by
  rw [Code.agree]
  simp

private theorem hdD₁₂ : (1 : ℕ) < 2 := by decide

private theorem XMemExactSpace : (X none : DifferentialPolynomial ℚ 1) ∈
    exactInterpolationSpace ℚ 2 2 1 1 0 0 hdD₁₂ := by
  change monomial (Finsupp.single none 1) (1 : ℚ) ∈ _
  rw [monomial_mem_exactInterpolationSpace]
  left
  simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
    Finsupp.weight_single, jetFirstWeight, jetHigherWeight]

example :
    (∑ r ∈ range 2, weightedHigherJetCount 1 (0 + r) * ambientContactCount r 1) -
      ∑ r ∈ range 2, weightedHigherJetCount 1 (0 + r) *
        exhibitedKernelContactCount r 1 (contactThreshold 1 2 r) = 5 := by
  rw [ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound]
  decide

example : (exactDimensionCoordinates 3 3 2 1 1 1).card = 6 := by
  rw [card_exactDimensionCoordinates]
  decide

example : Module.finrank ℚ (exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num)) = 3 := by
  rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
  decide

example : 32 ≤ Module.finrank ℚ (interpolationSpace ℚ 2 2 7 3 5 1 1) := by
  have h := finrank_interpolationSpace_lowerBound ℚ (d := 2) (m := 2) (A := 7) (K := 3)
    (B := 5) (W := 1) (C := 1) (H := 2) (by norm_num) le_rfl (by norm_num) (by norm_num)
  rw [card_goodHigherExponents_of_le le_rfl] at h
  exact le_of_eq_of_le (by decide) h

example : (goodHigherExponents 3 2 5).card = 4 := by
  rw [card_goodHigherExponents_of_le (by norm_num)]
  decide

example : certifiedEnlargedRankBound 1 (1 ^ 3) (1 ^ 3) 0 ≤
    4 * 1 ^ 8 * weightedHigherJetCount 1 (0 + 1 ^ 3) :=
  certifiedEnlargedRankBound_le_four_mul_d_pow_eight 1 0

example : shellExponent 1 + rankSavingExponent 1 = 1 :=
  shellExponent_add_rankSavingExponent (by norm_num)

example : (sourceMonomial (R := ℚ) (d := 1) 2 1 ![3]).IsWeightedHomogeneous
    jetDegreeWeight 4 := by
  simpa using sourceMonomial_isWeightedHomogeneous_jetDegreeWeight (R := ℚ) (d := 1) 2 1 ![3]

example : (sourceMonomial (R := ℚ) (d := 1) 2 1 ![3]).IsWeightedHomogeneous
    (fun _ : JetVariable 1 => (1 : ℕ)) 6 := by
  simpa using sourceMonomial_isWeightedHomogeneous (R := ℚ) (fun _ : JetVariable 1 => (1 : ℕ))
    2 1 ![3]

example : (zmodCertificate 0).ambientDim - 1 < 5 ∧
    ∀ j, jetDegree (zmodCertificate 0).interpolant j < 5 :=
  (zmodCertificate 0).below_characteristic

example : differentialSpecialization (constantCertificate zmodDomain 0).interpolant
    (0 : Polynomial (ZMod 5)) = 0 := by
  exact (constantCertificate zmodDomain 0).specializes_to_zero 0 zeroMessageAgrees

example :
    ∃ solution : BoundedSolution (zmodCertificate 0).interpolant 1,
      solution.polynomial = (0 : Polynomial (ZMod 5)) := by
  exact ReedSolomon.HiddenDerivative.InterpolationCertificate.exists_solution
    (zmodCertificate 0).toInterpolationCertificate ⟨0, zeroMessageAgrees⟩

example :
    (differentialSpecialization (X none : DifferentialPolynomial ℚ 1)
      (0 : Polynomial ℚ)).natDegree = 1 ∧
    (differentialSpecialization (X none : DifferentialPolynomial ℚ 1)
      (0 : Polynomial ℚ)).natDegree < 2 := by
  have hbound := natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace
    (by decide) hdD₁₂ XMemExactSpace 0 (by norm_num)
  have hspec : differentialSpecialization (X none : DifferentialPolynomial ℚ 1)
      (0 : Polynomial ℚ) = Polynomial.X := by
    exact differentialSpecialization_x (d := 1) (0 : Polynomial ℚ)
  rw [hspec] at hbound ⊢
  exact ⟨by simp, hbound⟩
