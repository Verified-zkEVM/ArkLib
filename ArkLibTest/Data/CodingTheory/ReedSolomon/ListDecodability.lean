/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.DirectJetList
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.PairwiseJohnson
import ArkLibTest.Data.CodingTheory.HiddenDerivative.Interpolation

/-!
# Direct-jet and pairwise Johnson list-bound acceptance cases

The order-zero equation `Y₀` over `ZMod 5` has the zero polynomial as a regular agreeing root.
The examples apply the regular-stage estimate and the complete actual-stage chain bound. A last
example applies the pairwise Johnson gap bound at length `16`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative

namespace DirectJetListTest

private noncomputable def exampleEquation : DifferentialPolynomial (ZMod 5) 0 := X (some 0)

private noncomputable def exampleDomain : Fin 2 ↪ ZMod 5 := CertificatesTest.zmodDomain

private def exampleReceived : Fin 2 → ZMod 5 := fun _ ↦ 0

example : ∃ P : Polynomial (ZMod 5),
    P ∈ directJetAgreementSolutions exampleEquation exampleDomain exampleReceived 1 2 := by
  refine ⟨0, ?_⟩
  simp [directJetAgreementSolutions, exampleEquation, exampleReceived,
    ReedSolomon.closePolynomialSet, ReedSolomon.polynomialAgreementSet]

example :
    (({0} : Finset (Polynomial (ZMod 5))).card : ℚ) ≤
      directJetStageCharge 2 2 1 1 (exampleEquation, 0) := by
  apply finite_actualStage_regularSolutions_card_le_dimensionSensitive
    exampleEquation 0 (by
      classical
      have hmem : (0 : Fin 1) ∈ activeJets exampleEquation := by
        rw [mem_activeJets]
        change 0 < jetDegree (X (some 0) : DifferentialPolynomial (ZMod 5) 0) 0
        rw [jetDegree, degreeOf_X_self]
        decide
      rw [highestActiveJet_eq_some_max exampleEquation ⟨0, hmem⟩]
      apply congrArg some
      apply Fin.ext
      omega)
    1 1 (by decide) (by decide)
    exampleDomain exampleReceived (by decide) (by decide)
    (by
      intro r hr i hir hiK
      omega)
    ({0} : Finset (Polynomial (ZMod 5)))
  · intro P hP
    have hPzero : P = 0 := by simpa using hP
    subst P
    change differentialSpecialization
      (separant exampleEquation (0 : Fin 1)) (0 : Polynomial (ZMod 5)) ≠ 0
    have hsep : separant exampleEquation (0 : Fin 1) = 1 := by
      simp [exampleEquation, separant]
    rw [hsep]
    simp [differentialSpecialization, differentialSpecializationHom]
  · intro P hP
    have hPzero : P = 0 := by simpa using hP
    subst P
    simp [directJetAgreementSolutions, exampleEquation, exampleReceived,
      ReedSolomon.closePolynomialSet, ReedSolomon.polynomialAgreementSet]

example :
    ∃ stages terminal, SeparantChain exampleEquation stages terminal ∧
      (directJetAgreementSolutions exampleEquation exampleDomain exampleReceived 1 2).Finite ∧
      ((directJetAgreementSolutions exampleEquation exampleDomain
        exampleReceived 1 2).ncard : ℚ) ≤
        (stages.map (directJetStageCharge 2 2 1 1)).sum ∧
      (stages.map (directJetStageCharge 2 2 1 1)).sum ≤
        directJetCommonOrderSum 2 2 1 1 1 0 ∧
      directJetCommonOrderSum 2 2 1 1 1 0 ≤
        (1 : ℚ) ^ 2 *
          ((((2 * (1 + 2 * 1 * (1 - 1)) : ℕ) : ℚ) /
            ((2 - 1 + 1 : ℕ) : ℚ)) ^ 0) := by
  exact exists_directJetList_actualStages_and_bounds
    (Q := exampleEquation) (by simp [exampleEquation])
    (K := 1) (k := 1) (B := 1) (by decide) (by decide) (by decide)
    (by
      simp [exampleEquation, jetTotalDegree, MvPolynomial.weightedTotalDegree,
        MvPolynomial.support_X, Finsupp.weight_single, jetDegreeWeight])
    exampleDomain exampleReceived (by decide) (by decide)
    (by
      right
      rw [ZMod.ringChar_zmod_n]
      decide)

end DirectJetListTest

namespace PairwiseJohnsonTest

private def natDomain (n : ℕ) : Fin n ↪ ℚ := ⟨fun i ↦ (i : ℚ), fun i j h ↦ by
  apply Fin.ext
  change (i.val : ℚ) = (j.val : ℚ) at h
  exact_mod_cast h⟩

/-- At length `16`, dimension `2`, gap `1/2` and agreement `10`, the list has at most `8/3`
members. -/
example : ((ReedSolomon.closePolynomialSet (natDomain 16) 0 2 10).ncard : ℝ) ≤ 8 / 3 := by
  have h := (ReedSolomon.closePolynomialSet_finite_and_ncard_le_pairwiseJohnson_of_gap
    (natDomain 16) 0 (k := 2) (A := 10) (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2
  norm_num at h
  convert h

end PairwiseJohnsonTest
