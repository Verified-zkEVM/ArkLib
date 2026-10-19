/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Interpolation
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.CertifiedRankBound
import ArkLibTest.Data.CodingTheory.HiddenDerivative.Interpolation

/-!
# Global interpolation acceptance case

One concrete point with zero center and received value admits a nonzero interpolant.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem hdD₀₁ : (0 : ℕ) < 1 := by decide

private theorem yZeroSubMemExact (r : ℤ) :
    (X (some 0) - C r : DifferentialPolynomial ℤ 0) ∈
      exactInterpolationSpace ℤ 1 2 0 1 0 0 hdD₀₁ := by
  refine Submodule.sub_mem _ ?_ ?_
  · change monomial (Finsupp.single (some 0) 1) (1 : ℤ) ∈ _
    rw [monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
      Finsupp.weight_single, jetFirstWeight, jetHigherWeight, differentialWeight]
  · rw [MvPolynomial.C_apply, monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight]

private theorem pointsInjective : Set.InjOn (fun i : Fin 2 => (i : ℤ))
    (↑(Finset.univ : Finset (Fin 2))) := by
  intro a _ b _ hab
  apply Fin.ext
  change (a : ℤ) = (b : ℤ) at hab
  exact_mod_cast hab

private theorem zeroAtTwoAgreedPoints : 2 ≤ (Finset.univ : Finset (Fin 2)).card := by
  simp

example :
    (X (some 0) - C (0 : ℤ) : DifferentialPolynomial ℤ 0) ≠ 0 ∧
      differentialSpecialization (X (some 0) - C (0 : ℤ) : DifferentialPolynomial ℤ 0)
        (0 : Polynomial ℤ) = 0 := by
  refine ⟨CertificatesTest.YZeroSubNeZero 0, ?_⟩
  have h := differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
    (ι := Fin 2) (R := ℤ) hdD₀₁ (fun i : Fin 2 => (i : ℤ)) (fun _ => 0) Finset.univ
    (yZeroSubMemExact 0) (fun i => CertificatesTest.satisfiesLocalConstraintsOneYZeroSub
      (i : ℤ) 0) (0 : Polynomial ℤ)
    (by norm_num) pointsInjective zeroAtTwoAgreedPoints (by simp)
  exact h

example :
    (X (some 0) - C (1 : ℤ) : DifferentialPolynomial ℤ 0) ≠ 0 ∧
      differentialSpecialization (X (some 0) - C (1 : ℤ) : DifferentialPolynomial ℤ 0)
        (Polynomial.C (1 : ℤ)) = 0 := by
  refine ⟨CertificatesTest.YZeroSubNeZero 1, ?_⟩
  have hdegree := differentialWeightedDegree_lt_of_mem_exactInterpolationSpace
    (m := 1) (A := 2) (D := 1) (d := 0) (by norm_num) hdD₀₁ (yZeroSubMemExact 1)
  have h := differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (D := 1) (A := 2) (m := 1) (ι := Fin 2) (R := ℤ)
    (fun i : Fin 2 => (i : ℤ)) (fun _ => 1) Finset.univ
    hdegree
    (fun i _ => CertificatesTest.satisfiesLocalConstraintsOneYZeroSub (i : ℤ) 1)
    (Polynomial.C (1 : ℤ)) (by norm_num)
    pointsInjective zeroAtTwoAgreedPoints (by simp)
  exact h

private theorem exactSpaceDimension :
    Module.finrank ℚ (exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num)) = 3 := by
  rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
  decide

private theorem localRankAtZero :
    Module.finrank ℚ (LinearMap.range
      (exactLocalConstraintAt (R := ℚ) (D := 2) (A := 2) (M := 1) (W := 0)
        (d := 1) (by norm_num) 1 (0 : ℚ) (0 : ℚ))) ≤ 2 :=
  (finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound
    (d := 1) (D := 2) (A := 2) (m := 1) (M := 1) (W := 0)
    (by norm_num) (by norm_num) (0 : ℚ) (0 : ℚ)).trans_eq (by decide)

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num) ∧
      ∀ _ : Fin 1, SatisfiesLocalConstraints 1 0 0 Q :=
  exists_nonzero_global_interpolant_of_uniform_local_rank_bound (by norm_num)
    (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0) 2 (fun _ => localRankAtZero)
    (by rw [exactSpaceDimension]; decide)
