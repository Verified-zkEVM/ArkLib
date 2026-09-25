/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
public import ArkLib.Data.Polynomial.Differential.JetDegree
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import ArkLib.ToMathlib.MvPolynomial.RadicalSplit
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AgreementCounting
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridAgreementCounting
import ArkLib.Data.MvPolynomial.WeightedDegree.Products

/-!
# Factorwise first-order agreement counting

The positive-degree radical part of a first-order equation accounts for solutions on its regular
branch. A supplied order-zero equation accounts for the remaining solutions. The resulting list
bound uses the actual jet and `Y₁` degrees of the radical part, with a degree envelope for
the tail.

## Main statements

* `FixedWordSingularTail`: the equation and root-routing data for a fixed received word.
* `finite_factorwise_agreement_solutions_card_le_actual`: the list bound at the actual degrees of
  the positive-degree radical part.
* `finite_factorwise_agreement_solutions_card_le`: the list bound at declared degree caps.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

universe u

/-- A nonzero order-zero equation bounds every solution routed away from the regular radical part.
-/
structure FixedWordSingularTail
    {F : Type u} [Field F] (Q : DifferentialPolynomial F 1) (B M : ℕ) where
  /-- The ordinary equation containing every solution not covered by the regular radical part. -/
  equation : DifferentialPolynomial F 0
  /-- The equation does not vanish identically. -/
  nonzero : equation ≠ 0
  /-- Its total jet degree fits the ordinary-degree tail envelope. -/
  degree_le : jetTotalDegree equation ≤ ordinaryDegreeEnvelope B M
  /-- Every root outside the regular positive-degree radical part is a root of `equation`. -/
  routes_nonregular : ∀ P : F[X], differentialSpecialization Q P = 0 →
    (differentialSpecialization (radicalPrimPart (some (1 : Fin 2)) Q) P ≠ 0 ∨
      differentialSpecialization
        (separant (radicalPrimPart (some (1 : Fin 2)) Q) (1 : Fin 2)) P = 0) →
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

private theorem radicalPrimPart_eq_one_of_degreeOf_eq_zero
    {F : Type*} [Field F] (Q : DifferentialPolynomial F 1)
    (hdegree : degreeOf (some (1 : Fin 2)) (radicalPrimPart (some 1) Q) = 0) :
    radicalPrimPart (some 1) Q = 1 := by
  classical
  have hempty : positiveDegreeFactorClasses (some (1 : Fin 2)) Q = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hpos := (mem_positiveDegreeFactorClasses.mp ha).2
    have hle : degreeOf (some (1 : Fin 2)) a.rep ≤
        degreeOf (some (1 : Fin 2)) (radicalPrimPart (some 1) Q) := by
      rw [radicalPrimPart, degreeOf_prod_eq]
      · exact Finset.single_le_sum
          (fun b _ ↦ Nat.zero_le (degreeOf (some (1 : Fin 2)) b.rep)) ha
      · intro b hb
        exact (irreducible_rep_of_mem_positiveDegreeFactorClasses hb).ne_zero
    omega
  rw [radicalPrimPart, hempty]
  simp

open Classical in
/-- One regular derivative-capped family and a supplied order-zero equation bound every accepted
solution. The regular charge uses the actual jet and `Y₁` degrees of the positive-degree radical
part. -/
theorem finite_factorwise_agreement_solutions_card_le_actual
    {F : Type u} [Field F] {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (tail : FixedWordSingularTail Q B M)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1)
          (jetTotalDegree (radicalPrimPart (some (1 : Fin 2)) Q))
          (jetDegree (radicalPrimPart (some (1 : Fin 2)) Q) 1)
          (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
  let regularRoots := S.filter fun P ↦
    differentialSpecialization (radicalPrimPart (some (1 : Fin 2)) Q) P = 0 ∧
      differentialSpecialization
        (separant (radicalPrimPart (some (1 : Fin 2)) Q) (1 : Fin 2)) P ≠ 0
  let tailRoots := S.filter fun P ↦ ¬ (
    differentialSpecialization (radicalPrimPart (some (1 : Fin 2)) Q) P = 0 ∧
      differentialSpecialization
        (separant (radicalPrimPart (some (1 : Fin 2)) Q) (1 : Fin 2)) P ≠ 0)
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : F) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_factorwise_char_guard hchar (by omega) (by omega)
  have htau : TaylorExponentSufficient 1 (D + 1) (regularTaylorExponent D) := by
    simpa only [regularTaylorExponent] using taylorExponentSufficient_firstOrder_tight D
  let j := jetTotalDegree (radicalPrimPart (some (1 : Fin 2)) Q)
  let r := jetDegree (radicalPrimPart (some (1 : Fin 2)) Q) 1
  have hrj : r ≤ j := jetDegree_le_total (radicalPrimPart (some (1 : Fin 2)) Q) 1
  have hpositiveJet : j ≤ B := by
    have hdvd : radicalPrimPart (some (1 : Fin 2)) Q ∣ Q :=
      radicalPrimPart_dvd_self (some (1 : Fin 2)) Q
    have hdegree : jetTotalDegree (radicalPrimPart (some (1 : Fin 2)) Q) ≤
        jetTotalDegree Q := by
      unfold jetTotalDegree
      exact weightedTotalDegree_le_of_dvd jetDegreeWeight hdvd hQ
    exact hdegree.trans hjet
  have hpositiveDerivative : r ≤ M := by
    have hdegree : jetDegree (radicalPrimPart (some (1 : Fin 2)) Q) 1 ≤ jetDegree Q 1 := by
      simpa [jetDegree] using
        degreeOf_radicalPrimPart_le (some (1 : Fin 2)) (some (1 : Fin 2)) Q
    exact hdegree.trans hderiv
  have hregularCardQ : (regularRoots.card : ℚ) ≤
      firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) *
        (((n - (D + 1) + 1 : ℕ) : ℚ) / ((A - (D + 1) + 1 : ℕ) : ℚ)) := by
    by_cases hr : r = 0
    · have hempty : regularRoots = ∅ := by
        ext P
        constructor
        · intro hP
          obtain ⟨_, hroot, _⟩ := Finset.mem_filter.mp hP
          have hone := radicalPrimPart_eq_one_of_degreeOf_eq_zero Q (by
            simpa only [r, jetDegree] using hr)
          have hrootOne :
              differentialSpecialization (radicalPrimPart (some (1 : Fin 2)) Q) P = 1 := by
            rw [hone]
            exact map_one _
          rw [hrootOne] at hroot
          exact (one_ne_zero hroot).elim
        · simp
      rw [hempty]
      positivity
    · by_cases hDone : D = 1
      · subst D
        have hn : n - 2 + 1 = n - 1 := by omega
        have hA' : A - 2 + 1 = A - 1 := by omega
        simpa only [Nat.reduceAdd, regularTaylorExponent, Nat.reduceMul, Nat.reduceSub,
          hn, hA'] using
          finite_regular_agreement_solutions_card_le_identityPair
            (radicalPrimPart (some (1 : Fin 2)) Q) j r le_rfl domain received (by omega)
            hAn regularRoots
            (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).1)
            (fun P hP ↦ (Finset.mem_filter.mp hP).2.1)
            (fun P hP ↦ by
              simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using
                (Finset.mem_filter.mp hP).2.2)
            (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).2)
      · apply finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
          (radicalPrimPart (some (1 : Fin 2)) Q) (D + 1) (D + 1) j r
          (regularTaylorExponent D) htau (by unfold regularTaylorExponent; omega)
          (by omega) le_rfl (by omega) hrj le_rfl le_rfl domain received
          hkA hAn regularRoots
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
      (firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) : ℝ) *
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
      by_cases hroot :
          differentialSpecialization (radicalPrimPart (some (1 : Fin 2)) Q) P = 0
      · exact Or.inr (not_ne_iff.mp (fun hsep ↦ hnot ⟨hroot, hsep⟩))
      · exact Or.inl hroot
  have hcover : S ⊆ regularRoots ∪ tailRoots := by
    intro P hP
    by_cases hregular :
        differentialSpecialization (radicalPrimPart (some (1 : Fin 2)) Q) P = 0 ∧
          differentialSpecialization
            (separant (radicalPrimPart (some (1 : Fin 2)) Q) (1 : Fin 2)) P ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, hregular⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP, hregular⟩)
  have hcard : (S.card : ℝ) ≤ regularRoots.card + tailRoots.card := by
    exact_mod_cast (show S.card ≤ regularRoots.card + tailRoots.card by
      calc
        S.card ≤ (regularRoots ∪ tailRoots).card := Finset.card_le_card hcover
        _ ≤ regularRoots.card + tailRoots.card := Finset.card_union_le _ _)
  calc
    (S.card : ℝ) ≤ regularRoots.card + tailRoots.card := hcard
    _ ≤ (firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M :=
      add_le_add hregularCard htailCard

open Classical in
/-- Replacing the actual radical-part degrees by the declared caps gives a closed list bound. -/
theorem finite_factorwise_agreement_solutions_card_le
    {F : Type u} [Field F] {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hMB : M ≤ B) (hjet : jetTotalDegree Q ≤ B) (hderiv : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (tail : FixedWordSingularTail Q B M)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
  let j := jetTotalDegree (radicalPrimPart (some (1 : Fin 2)) Q)
  let r := jetDegree (radicalPrimPart (some (1 : Fin 2)) Q) 1
  have hrj : r ≤ j := jetDegree_le_total (radicalPrimPart (some (1 : Fin 2)) Q) 1
  have hjB : j ≤ B := by
    have hdvd : radicalPrimPart (some (1 : Fin 2)) Q ∣ Q :=
      radicalPrimPart_dvd_self (some (1 : Fin 2)) Q
    have hdegree : jetTotalDegree (radicalPrimPart (some (1 : Fin 2)) Q) ≤
        jetTotalDegree Q := by
      unfold jetTotalDegree
      exact weightedTotalDegree_le_of_dvd jetDegreeWeight hdvd hQ
    exact hdegree.trans hjet
  have hrM : r ≤ M := by
    have hdegree : jetDegree (radicalPrimPart (some (1 : Fin 2)) Q) 1 ≤ jetDegree Q 1 := by
      simpa [jetDegree] using
        degreeOf_radicalPrimPart_le (some (1 : Fin 2)) (some (1 : Fin 2)) Q
    exact hdegree.trans hderiv
  have hstage : firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) ≤
      firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) :=
    (firstOrderCurveFiberStageOne_mono_total hjB).trans
      (firstOrderCurveFiberStageOne_mono_derivative hrM hMB)
  have hactual := finite_factorwise_agreement_solutions_card_le_actual domain received Q hQ
    hD hkA hAn hjet hderiv hchar tail S hsol haccept
  calc
    (S.card : ℝ) ≤
        (firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) : ℝ) *
            ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := hactual
    _ ≤ (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
      gcongr

end

end ReedSolomon.FirstOrder.Squarefree
