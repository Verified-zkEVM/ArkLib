/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedGraphCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.DerivativeCappedCounting

/-!
# Derivative-capped counting for admissible polynomial tuple graphs

Specializing an admissible tuple at one common challenge injects it into a regular first-order
Taylor chart. Bounding the total jet degree and the derivative degree separately then bounds every
finite family of admissible tuples by the first-order fixed-fiber degree and the sharp agreement
ratio.

## Main statements

* `admissibleChartTuples_card_le_derivativeCapped_of_exponent`: the derivative-capped bound for
  every finite family of admissible tuple graphs.
* `admissibleChartTupleFamilyAtExponent_card_le_derivativeCapped`: the bound for the complete
  finite family of admissible tuple graphs.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

noncomputable section

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- Every finite family of admissible first-order tuple graphs has size at most the fixed-fiber
degree from the total and derivative degree bounds, times the sharp agreement ratio. -/
theorem admissibleChartTuples_card_le_derivativeCapped_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLn : L ≤ n)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    (tuples.card : ℚ) ≤ firstOrderCurveFiberStageOne K v u τ *
      (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : tuples = ∅
  · subst tuples
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let auxiliary := tuples.image fun P ↦
    chartTuplePullback iota center P (jointInitialJetSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ :=
    exists_polynomialTuple_specialization_injective_avoiding_roots (ℓ := ℓ)
      iota tuples ∅ auxiliary (by
      intro R hR
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hR
      exact (htuples P hP).regular)
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jets : Finset (Fin 2 → E) := tuples.image (chartTupleJet iota center z)
  have hspec (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (htuples P hP).specialize hτ hkK z
      (havoid _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩))
  have hjetinj : Set.InjOn (chartTupleJet (r := 1) iota center z)
      (tuples : Set (Fin (ℓ + 1) → F[X])) := by
    intro P hP R hR heq
    apply hinj hP hR
    change powerBatchedPolynomial (fun t ↦ (P t).map iota) z =
      powerBatchedPolynomial (fun t ↦ (R t).map iota) z
    rw [← (hspec P hP).2.2.2, ← (hspec R hR).2.2.2, heq]
  have hcard : jets.card = tuples.card := Finset.card_image_of_injOn hjetinj
  let domainE : Fin n ↪ E :=
    ⟨fun i ↦ iota (domain i), iota.injective.comp domain.injective⟩
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    exact (le_weightedTotalDegree _
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hjet
  have hderivz : Qz.degreeOf (some 1) ≤ u := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    exact (monomial_le_degreeOf (some 1)
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hderiv
  have hbound := finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
    center Qz K k v u τ hτ hτpos hK hu huv hvle hderivz
    domainE received hkL hLn jets (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      exact ⟨(hspec P hP).1, (hspec P hP).2.1,
        fun l ↦ (hspec P hP).2.2.1 l.val l.property⟩) (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      have hsubset : (commonCurveAgreementSet domain w P : Set (Fin n)) ⊆
          {i | aeval (chartTupleJet iota center z P)
            (taylorAgreementEquation center Qz K τ (domainE i) (received i)) = 0} := by
        intro i hi
        have hi' : ∀ t, (P t).eval (domain i) = w t i :=
          (mem_commonCurveAgreementSet domain w P i).mp hi
        have hbatch :
            (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
              (domainE i) = received i := by
          change (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
              (iota (domain i)) = ∑ t, z ^ t.val * iota (w t i)
          rw [powerBatchedPolynomial_eval]
          apply Finset.sum_congr rfl
          intro t _
          congr 1
          rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hi' t]
        have heval :
            (rationalTaylorPolynomial center Qz K (chartTupleJet iota center z P)).eval
              (domainE i) = received i := by
          rw [(hspec P hP).2.2.2]
          exact hbatch
        exact (taylorAgreementEquation_eq_zero_iff center Qz hτ
          (chartTupleJet iota center z P) (hspec P hP).2.1 (domainE i) (received i)).mpr
            heval
      calc
        L ≤ (commonCurveAgreementSet domain w P).card := (htuples P hP).common
        _ = (commonCurveAgreementSet domain w P : Set (Fin n)).ncard :=
          (Set.ncard_coe_finset _).symm
        _ ≤ _ := Set.ncard_le_ncard hsubset)
  rw [hcard] at hbound
  exact hbound

/-- The complete finite family of admissible first-order tuple graphs has the derivative-capped
bound from the total and derivative degree bounds. -/
theorem admissibleChartTupleFamilyAtExponent_card_le_derivativeCapped
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLn : L ≤ n)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ u) :
    ((admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ).card : ℚ) ≤
      firstOrderCurveFiberStageOne K v u τ *
        (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
  apply admissibleChartTuples_card_le_derivativeCapped_of_exponent
    domain w iota center Q K k L v u τ hτ hτpos hK hkK hkL hLn hu huv hjet hderiv
  intro P hP
  exact (mem_admissibleChartTupleFamilyAtExponent_iff
    domain w iota center Q K k L τ hkL P).mp hP

end ReedSolomon
