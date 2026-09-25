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
import ArkLib.ToMathlib.MvPolynomial.PDeriv

/-!
# Factorwise first-order agreement counting

The positive-degree radical part of a first-order equation accounts for solutions on its regular
branch. A supplied order-zero equation accounts for the remaining solutions. The resulting list
bound uses the actual jet and `Y₁` degrees of the radical part, with a degree envelope for
the tail.

## Main statements

* `FixedWordSingularTail`: the equation and root-routing data for a fixed received word.
* `FixedWordRegularTail`: the equation and root-routing data for a chosen regular factor.
* `finite_factorwise_agreement_solutions_card_le_actual`: the list bound at the actual degrees of
  the positive-degree radical part.
* `finite_factorwise_agreement_solutions_card_le_actual_of_regular_equation`: the actual-degree
  bound for a chosen regular equation.
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

/-- Tail data for any chosen first-order regular equation whose roots are counted by the
factorwise regular-branch bound. -/
structure FixedWordRegularTail
    {F : Type u} [Field F] (Q R : DifferentialPolynomial F 1) (B M : ℕ) where
  /-- A regular equation of `Y₁` degree zero is the constant one. -/
  regular_degree_zero : jetDegree R 1 = 0 → R = 1
  /-- The order-zero equation containing every solution outside the regular branch. -/
  equation : DifferentialPolynomial F 0
  /-- The order-zero equation does not vanish identically. -/
  nonzero : equation ≠ 0
  /-- The order-zero equation fits the ordinary-degree tail envelope. -/
  degree_le : jetTotalDegree equation ≤ ordinaryDegreeEnvelope B M
  /-- Every root outside the regular branch is a root of the order-zero equation. -/
  routes_nonregular : ∀ P : F[X], differentialSpecialization Q P = 0 →
    (differentialSpecialization R P ≠ 0 ∨
      differentialSpecialization (separant R (1 : Fin 2)) P = 0) →
    differentialSpecialization equation P = 0

open Classical in
/-- One regular derivative-capped family and a supplied order-zero equation bound every accepted
solution. The regular charge uses the actual jet and `Y₁` degrees of the chosen regular equation.
-/
theorem finite_factorwise_agreement_solutions_card_le_actual_of_regular_equation
    {F : Type u} [Field F] {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q R : DifferentialPolynomial F 1)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (tail : FixedWordRegularTail Q R B M)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1)
          (jetTotalDegree R)
          (jetDegree R 1)
          (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
  let regularRoots := S.filter fun P ↦
    differentialSpecialization R P = 0 ∧
      differentialSpecialization
        (separant R (1 : Fin 2)) P ≠ 0
  let tailRoots := S.filter fun P ↦ ¬ (
    differentialSpecialization R P = 0 ∧
      differentialSpecialization
        (separant R (1 : Fin 2)) P ≠ 0)
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : F) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    apply natCast_ne_zero_of_ringChar_eq_zero_or_lt hchar (by omega)
    exact (show i ≤ D by omega).trans (Nat.le_max_left D M)
  let j := jetTotalDegree R
  let r := jetDegree R 1
  have hrj : r ≤ j := jetDegree_le_total R 1
  have hregularCard : (regularRoots.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) : ℝ) *
        ((n - D : ℕ) : ℝ) / (A - D : ℕ) := by
    by_cases hr : r = 0
    · have hempty : regularRoots = ∅ := by
        ext P
        constructor
        · intro hP
          obtain ⟨_, hroot, _⟩ := Finset.mem_filter.mp hP
          have hone := tail.regular_degree_zero (by simpa only [r] using hr)
          have hrootOne :
              differentialSpecialization R P = 1 := by
            rw [hone]
            exact map_one _
          rw [hrootOne] at hroot
          exact (one_ne_zero hroot).elim
        · simp
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      have hAd : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast (by omega : 0 < A - D)
      have hstage : (0 : ℝ) ≤
          (firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) : ℝ) :=
        Nat.cast_nonneg _
      have hn : (0 : ℝ) ≤ ((n - D : ℕ) : ℝ) := Nat.cast_nonneg _
      exact div_nonneg (mul_nonneg hstage hn) hAd.le
    · have hregularQ := finite_regular_agreement_solutions_card_le_regularTaylor
        R D j r
        (by
          by_cases hDone : D = 1
          · exact Or.inl hDone
          · exact Or.inr ⟨by omega, Nat.pos_of_ne_zero hr⟩)
        le_rfl le_rfl hrj domain received hkA hAn regularRoots
        (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).1)
        (fun P hP ↦ (Finset.mem_filter.mp hP).2.1)
        (fun P hP ↦ by
          simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using
            (Finset.mem_filter.mp hP).2.2)
        hbin
        (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).2)
      have hcast := (Rat.cast_le (K := ℝ)).mpr hregularQ
      simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div, mul_div_assoc] using hcast
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
      by_cases hroot : differentialSpecialization R P = 0
      · exact Or.inr (not_ne_iff.mp (fun hsep ↦ hnot ⟨hroot, hsep⟩))
      · exact Or.inl hroot
  have hcover : S ⊆ regularRoots ∪ tailRoots := by
    intro P hP
    by_cases hregular :
        differentialSpecialization R P = 0 ∧
          differentialSpecialization (separant R (1 : Fin 2)) P ≠ 0
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
/-- One regular radical-part family and a supplied order-zero equation bound every accepted
solution. The regular charge uses the actual jet and `Y₁` degrees of the radical part. -/
theorem finite_factorwise_agreement_solutions_card_le_actual
    {F : Type u} [Field F] {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
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
  let R := radicalPrimPart (some (1 : Fin 2)) Q
  let genericTail : FixedWordRegularTail Q R B M := {
    regular_degree_zero := by
      intro hdegree
      exact radicalPrimPart_eq_one_of_degreeOf_eq_zero (some (1 : Fin 2)) Q hdegree
    equation := tail.equation
    nonzero := tail.nonzero
    degree_le := tail.degree_le
    routes_nonregular := tail.routes_nonregular
  }
  simpa only [R] using finite_factorwise_agreement_solutions_card_le_actual_of_regular_equation
    domain received Q R hD hkA hAn hchar genericTail S hsol haccept

open Classical in
/-- Replacing the actual degrees of a chosen regular equation by declared caps gives a closed
factorwise list bound. -/
theorem finite_factorwise_agreement_solutions_card_le_of_regular_equation
    {F : Type u} [Field F] {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q R : DifferentialPolynomial F 1)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hMB : M ≤ B) (hRjet : jetTotalDegree R ≤ B) (hRderiv : jetDegree R 1 ≤ M)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (tail : FixedWordRegularTail Q R B M)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
  let j := jetTotalDegree R
  let r := jetDegree R 1
  have hrj : r ≤ j := jetDegree_le_total R 1
  have hjB : j ≤ B := hRjet
  have hrM : r ≤ M := hRderiv
  have hstage : firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) ≤
      firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) :=
    (firstOrderCurveFiberStageOne_mono_total hjB).trans
      (firstOrderCurveFiberStageOne_mono_derivative hrM hMB)
  have hactual := finite_factorwise_agreement_solutions_card_le_actual_of_regular_equation
    domain received Q R hD hkA hAn hchar tail S hsol haccept
  calc
    (S.card : ℝ) ≤
        (firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) : ℝ) *
            ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := hactual
    _ ≤ (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
      gcongr

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
  let R := radicalPrimPart (some (1 : Fin 2)) Q
  have hRjet : jetTotalDegree R ≤ B := by
    have hdvd : R ∣ Q := radicalPrimPart_dvd_self (some (1 : Fin 2)) Q
    have hdegree : jetTotalDegree R ≤ jetTotalDegree Q := by
      unfold jetTotalDegree
      exact weightedTotalDegree_le_of_dvd jetDegreeWeight hdvd hQ
    exact hdegree.trans hjet
  have hRderiv : jetDegree R 1 ≤ M := by
    have hdegree : jetDegree R 1 ≤ jetDegree Q 1 := by
      simpa [jetDegree] using
        degreeOf_radicalPrimPart_le (some (1 : Fin 2)) (some (1 : Fin 2)) Q
    exact hdegree.trans hderiv
  let regularTail : FixedWordRegularTail Q R B M := {
    regular_degree_zero := by
      intro hdegree
      exact radicalPrimPart_eq_one_of_degreeOf_eq_zero (some (1 : Fin 2)) Q hdegree
    equation := tail.equation
    nonzero := tail.nonzero
    degree_le := tail.degree_le
    routes_nonregular := tail.routes_nonregular
  }
  exact finite_factorwise_agreement_solutions_card_le_of_regular_equation
    domain received Q R hD hkA hAn hMB hRjet hRderiv hchar regularTail S hsol haccept

end

end ReedSolomon.FirstOrder.Squarefree
