/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Interpolation
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.CertifiedRankBound

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
  · rw [X, monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
      Finsupp.weight_single, jetFirstWeight, jetHigherWeight, differentialWeight]
  · rw [MvPolynomial.C_apply, monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight]

private theorem satisfiesYZeroSub (center r : ℤ) :
    SatisfiesLocalConstraints (d := 0) 1 center r (X (some 0) - C r) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply, projectLowContact,
    weightedTruncation_eq_zero_iff]
  have h : (unscaledLocalSubstitution 0 center r).toLinearMap
      (X (some 0) - C r) =
      X (localT 0) * (X (localE 0) + localJetSum 0) := by
    simp only [AlgHom.toLinearMap_apply, map_sub, unscaledLocalSubstitution_Y_zero, algHom_C,
      algebraMap_eq, mul_add, T_mul_localJetSum]
    ring
  rw [h]
  simpa using mul_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := ℤ) (localContactWeight 0) (localT 0) le_rfl)
    (by simp : X (localE 0) + localJetSum 0 ∈
      restrictWeightedOrder (R := ℤ) (localContactWeight 0) 0)

private theorem differentialWeightedDegreeYZeroSubLe (r : ℤ) :
    differentialWeightedDegree 1
      (X (some 0) - C r : DifferentialPolynomial ℤ 0) ≤ 1 := by
  rw [differentialWeightedDegree, ← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  refine Submodule.sub_mem _ (X_mem_restrictWeightedDegree _ _ _ ?_) ?_
  · simp [differentialWeight]
  · rw [mem_restrictWeightedDegree_iff_weightedTotalDegree_le, weightedTotalDegree_C]
    exact Nat.zero_le _

private theorem yZeroSubNeZero (r : ℤ) :
    (X (some 0) - C r : DifferentialPolynomial ℤ 0) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun _ ↦ r + 1)) h
  simp at this

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
  refine ⟨yZeroSubNeZero 0, ?_⟩
  have h := differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
    (ι := Fin 2) (R := ℤ) hdD₀₁ (fun i : Fin 2 => (i : ℤ)) (fun _ => 0) Finset.univ
    (yZeroSubMemExact 0) (fun i => satisfiesYZeroSub (i : ℤ) 0) (0 : Polynomial ℤ)
    (by norm_num) pointsInjective zeroAtTwoAgreedPoints (by simp)
  exact h

example :
    (X (some 0) - C (1 : ℤ) : DifferentialPolynomial ℤ 0) ≠ 0 ∧
      differentialSpecialization (X (some 0) - C (1 : ℤ) : DifferentialPolynomial ℤ 0)
        (Polynomial.C (1 : ℤ)) = 0 := by
  refine ⟨yZeroSubNeZero 1, ?_⟩
  have hdegree : differentialWeightedDegree 1
      (X (some 0) - C (1 : ℤ) : DifferentialPolynomial ℤ 0) < 2 := by
    exact (differentialWeightedDegreeYZeroSubLe 1).trans_lt (by decide)
  have h := differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (D := 1) (A := 2) (m := 1) (ι := Fin 2) (R := ℤ)
    (fun i : Fin 2 => (i : ℤ)) (fun _ => 1) Finset.univ
    hdegree
    (fun i _ => satisfiesYZeroSub (i : ℤ) 1) (Polynomial.C (1 : ℤ)) (by norm_num)
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
