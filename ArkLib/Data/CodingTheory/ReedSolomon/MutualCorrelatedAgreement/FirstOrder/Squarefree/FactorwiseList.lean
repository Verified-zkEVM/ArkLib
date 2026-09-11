/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Semantic
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.SingularTail
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FirstOrder.FirstOrderHybridList

/-!
# Factorwise first-order list counting

This file packages the semantic list-counting step after squarefree factorization.  The distinct
positive-`Y₁` product contributes one derivative-capped regular Taylor family.  Every remaining
source root is routed to one nonzero order-zero equation, which retains both the root-independent
content and the padded derivative resultant.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

universe u

/-- Data supplied by the content-resultant construction for a fixed-word first-order equation. -/
structure FixedWordSingularTail
    {F : Type u} [Field F] (Q : DifferentialPolynomial F 1) (B M : ℕ) where
  /-- The ordinary equation containing every solution not covered by the regular product. -/
  equation : DifferentialPolynomial F 0
  nonzero : equation ≠ 0
  degree_le : SymbolicSeparantChain.jetWeight equation ≤ ordinaryDegreeEnvelope B M
  /-- The original padded Sylvester sizes make this valid even when specialization lowers the
  actual `Y₁` degree. -/
  routes_nonregular : ∀ P : F[X], differentialSpecialization Q P = 0 →
    (differentialSpecialization (positiveEquation Q) P ≠ 0 ∨
      differentialSpecialization
        (separant (positiveEquation Q) (1 : Fin 2)) P = 0) →
    differentialSpecialization equation P = 0

private theorem natCast_ne_zero_of_factorwise_char_guard
    {F : Type*} [Field F] {D M i : ℕ}
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (hi : 0 < i) (hiD : i ≤ D) : (i : F) ≠ 0 := by
  intro hz
  have hdiv := (ringChar.spec F i).mp hz
  rcases hchar with hzero | hpositive
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hi
      ((hiD.trans (Nat.le_max_left D M)).trans_lt hpositive) hdiv

open Classical in
/-- One regular derivative-capped family plus the content-resultant ordinary tail bounds every
fixed-word solution.  The exact regular charge retains the `(j,r)` derivative cap through
`firstOrderCurveFiberStageOne`; no full-triangle replacement is made here. -/
theorem finite_factorwise_agreement_solutions_card_le
    {F : Type u} [Field F] {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hB : 0 < B) (hM : 0 < M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (tail : FixedWordSingularTail Q B M)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
  let regularRoots := S.filter fun P ↦
    differentialSpecialization (positiveEquation Q) P = 0 ∧
      differentialSpecialization
        (separant (positiveEquation Q) (1 : Fin 2)) P ≠ 0
  let tailRoots := S.filter fun P ↦ ¬ (
    differentialSpecialization (positiveEquation Q) P = 0 ∧
      differentialSpecialization
        (separant (positiveEquation Q) (1 : Fin 2)) P ≠ 0)
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : F) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_factorwise_char_guard hchar (by omega) (by omega)
  have htau : TaylorExponentSufficient 1 (D + 1) (2 * D - 1) := by
    convert taylorExponentSufficient_two_mul_sub_three 1 (K := D + 1) (by omega) using 1
    omega
  have hpositiveJet : jetTotalDegree (positiveEquation Q) ≤ B :=
    (positiveEquation_jetTotalDegree_le Q hQ).trans hjet
  have hpositiveDerivative : jetDegree (positiveEquation Q) 1 ≤ M :=
    (positiveEquation_yOneDegree_le Q hQ).trans hderiv
  have hregularCardQ : (regularRoots.card : ℚ) ≤
      firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) *
        (((n - (D + 1) + 1 : ℕ) : ℚ) / ((A - (D + 1) + 1 : ℕ) : ℚ)) := by
    apply finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
      (positiveEquation Q) (D + 1) (D + 1) B M (2 * D - 1)
      htau (by omega) (by omega) le_rfl hB hM hMB hpositiveJet hpositiveDerivative
      domain received (by omega) hkA hAn regularRoots
    · intro P hP
      exact (haccept P (Finset.mem_filter.mp hP).1).1
    · intro P hP
      exact (Finset.mem_filter.mp hP).2.1
    · intro P hP
      simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using
        (Finset.mem_filter.mp hP).2.2
    · exact hbin
    · intro P hP
      exact (haccept P (Finset.mem_filter.mp hP).1).2
  have hregularCard : (regularRoots.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) *
        ((n - D : ℕ) : ℝ) / (A - D : ℕ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hregularCardQ
    have hnum : n - (D + 1) + 1 = n - D := by omega
    have hden : A - (D + 1) + 1 = A - D := by omega
    simpa only [hnum, hden, Rat.cast_natCast, Rat.cast_mul, Rat.cast_div, mul_div_assoc]
      using hcast
  have htailBound : HasOrderZeroTailListBound (D := D) (A := A)
      (b := ordinaryDegreeEnvelope B M) domain received tail.equation :=
    hasOrderZeroTailListBound_of_nonzero domain received tail.nonzero tail.degree_le
  have htailCard : (tailRoots.card : ℝ) ≤ ordinaryDegreeEnvelope B M := by
    apply htailBound tailRoots
    · intro P hP
      exact haccept P (Finset.mem_filter.mp hP).1
    · intro P hP
      have hPmem := (Finset.mem_filter.mp hP).1
      have hnot := (Finset.mem_filter.mp hP).2
      apply tail.routes_nonregular P (hsol P hPmem)
      by_cases hroot : differentialSpecialization (positiveEquation Q) P = 0
      · exact Or.inr (not_ne_iff.mp (fun hsep ↦ hnot ⟨hroot, hsep⟩))
      · exact Or.inl hroot
  have hcover : S ⊆ regularRoots ∪ tailRoots := by
    intro P hP
    by_cases hregular :
        differentialSpecialization (positiveEquation Q) P = 0 ∧
          differentialSpecialization
            (separant (positiveEquation Q) (1 : Fin 2)) P ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, hregular⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP, hregular⟩)
  have hcard : (S.card : ℝ) ≤ regularRoots.card + tailRoots.card := by
    exact_mod_cast (show S.card ≤ regularRoots.card + tailRoots.card by
      calc
        S.card ≤ (regularRoots ∪ tailRoots).card := Finset.card_le_card hcover
        _ ≤ regularRoots.card + tailRoots.card := Finset.card_union_le _ _)
  calc
    (S.card : ℝ) ≤ regularRoots.card + tailRoots.card := hcard
    _ ≤ (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M :=
      add_le_add hregularCard htailCard

end

end ReedSolomon.FirstOrder.Squarefree
