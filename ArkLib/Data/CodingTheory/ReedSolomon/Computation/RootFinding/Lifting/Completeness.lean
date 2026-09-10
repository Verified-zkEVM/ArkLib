/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.ExecutableRegularLift
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.Iteration
/-!
# Completeness of the executable regular lifting scan

The coefficient scan retains every bounded solution with the supplied initial jet. Completeness
uses explicit finite coefficient prefixes and does not require regularity. Nonsingularity and the
characteristic bound ensure that each surviving prefix has exactly one next coefficient. The final
full residual and degree checks remain necessary, including when the requested degree is below the
initial jet order. Predicate-call counters are not interpreted as runtime bounds here.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open Polynomial CompPoly

variable {F : Type*} [Field F] [DecidableEq F] {r : ℕ}

/-- Retain exactly the centered coefficients strictly below `n`. -/
def effectiveCoefficientPrefix (P : CPolynomial F) (n : ℕ) : CPolynomial F :=
  CPolynomial.ofArray (Array.ofFn fun i : Fin n => P.coeff i.val)

/-- Normalization preserves each retained coefficient and removes all higher coefficients. -/
theorem coeff_effectiveCoefficientPrefix (P : CPolynomial F) (n i : ℕ) :
    (effectiveCoefficientPrefix P n).coeff i = if i < n then P.coeff i else 0 := by
  rw [effectiveCoefficientPrefix, CPolynomial.coeff_ofArray]
  by_cases hi : i < n <;> simp [Array.getD, hi]

/-- Extending the retained array by one entry is precisely the executable lift operation. -/
theorem effectiveCoefficientPrefix_succ (P : CPolynomial F) (k r : ℕ) :
    effectiveCoefficientPrefix P (k + r + 1) =
      effectiveRegularCandidate k r (effectiveCoefficientPrefix P (k + r)) (P.coeff (k + r)) := by
  apply CPolynomial.ringEquiv.injective
  ext i
  simp only [CPolynomial.ringEquiv_apply, ← CPolynomial.coeff_toPoly,
    coeff_effectiveCoefficientPrefix, coeff_effectiveRegularCandidate]
  split_ifs <;> first | omega | simp_all

/-- A prefix above the polynomial's degree is the complete concrete polynomial. -/
theorem effectiveCoefficientPrefix_eq_self (P : CPolynomial F) (n : ℕ)
    (hn : P.natDegree < n) : effectiveCoefficientPrefix P n = P := by
  apply CPolynomial.ringEquiv.injective
  ext i
  rw [CPolynomial.ringEquiv_apply, CPolynomial.ringEquiv_apply,
    ← CPolynomial.coeff_toPoly, coeff_effectiveCoefficientPrefix]
  split_ifs with hi
  · exact CPolynomial.coeff_toPoly _ _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    exact (CPolynomial.natDegree_toPoly P ▸ hn).trans_le (Nat.le_of_not_gt hi)

omit [DecidableEq F] in
/-- Centering an unshifted concrete polynomial recovers its actual coefficient polynomial. -/
@[simp] theorem taylor_unshift (center : F) (P : CPolynomial F) :
    taylor center (unshift center P) = P.toPoly := by
  simp [unshift, taylor_taylor]

omit [DecidableEq F] in
/-- Initial Hasse jet entries are exactly the stored centered coefficients. -/
theorem polynomialJet_unshift_apply (center : F) (P : CPolynomial F) (j : Fin (r + 1)) :
    polynomialJet center (unshift center P) j = P.coeff j.val := by
  classical
  change hasseCoeffAt center j.val (taylor (-center) P.toPoly) = _
  rw [hasseCoeffAt_taylor, add_neg_cancel, hasseCoeffAt_zero_eq_coeff,
    ← CPolynomial.coeff_toPoly]

/-- The supplied initial jet is precisely the first `r+1` centered coefficients. -/
theorem effectiveCoefficientPrefix_eq_initial (center : F) (P : CPolynomial F)
    (jet : Fin (r + 1) → F) (hjet : polynomialJet center (unshift center P) = jet) :
    effectiveCoefficientPrefix P (r + 1) = effectiveInitialPrefix jet := by
  apply CPolynomial.ringEquiv.injective
  ext i
  simp only [CPolynomial.ringEquiv_apply, ← CPolynomial.coeff_toPoly,
    coeff_effectiveCoefficientPrefix]
  split_ifs with hi
  · have h := congrFun hjet ⟨i, hi⟩
    rw [polynomialJet_unshift_apply] at h
    exact h.trans (coeff_effectiveInitialPrefix jet ⟨i, hi⟩).symm
  · exact (coeff_effectiveInitialPrefix_of_lt jet i (by omega)).symm

/-- Matching `n+r` centered coefficients makes the residuals agree below order `n`. -/
theorem effectiveCoefficientPrefix_residual_dvd
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F) (n : ℕ)
    (hsolution : differentialSpecialization (semanticEquation Q) (unshift center P) = 0) :
    X ^ n ∣ shiftedJetSubstitution center
      (unshift center (effectiveCoefficientPrefix P (n + r))) (semanticEquation Q) := by
  have hprefix : X ^ (n + r) ∣
      taylor center (unshift center (effectiveCoefficientPrefix P (n + r))) -
        taylor center (unshift center P) := by
    rw [taylor_unshift, taylor_unshift, X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, ← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly,
      coeff_effectiveCoefficientPrefix, if_pos hi, sub_self]
  have h := X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd
    (semanticEquation Q) (unshift center (effectiveCoefficientPrefix P (n + r)))
      (unshift center P) center n hprefix
  simpa [← taylor_differentialSpecialization, hsolution] using h

variable [Fintype F]

/-- Every truncation of an actual solution survives its corresponding scan depth. -/
theorem effectiveCoefficientPrefix_mem_iteration
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (jet : Fin (r + 1) → F) (hjet : polynomialJet center (unshift center P) = jet)
    (hsolution : differentialSpecialization (semanticEquation Q) (unshift center P) = 0)
    (steps : ℕ) :
    effectiveCoefficientPrefix P (steps + r + 1) ∈
      (effectiveRegularIteration Q center (effectiveInitialPrefix jet) steps).candidates := by
  induction steps with
  | zero =>
      simp [effectiveCoefficientPrefix_eq_initial center P jet hjet]
  | succ steps ih =>
      rw [mem_effectiveRegularIteration_succ_candidates]
      refine ⟨effectiveCoefficientPrefix P (steps + r + 1), ih, P.coeff (steps + 1 + r), ?_, ?_⟩
      · apply (mem_effectiveRegularCoefficients_iff_dvd Q center _ _ (Nat.succ_pos steps)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            effectiveCoefficientPrefix_residual_dvd Q center P (steps + 1) hsolution)).2
        have heq := effectiveCoefficientPrefix_succ P (steps + 1) r
        have h := effectiveCoefficientPrefix_residual_dvd Q center P (steps + 2) hsolution
        rw [show steps + 2 + r = steps + 1 + r + 1 by omega, heq] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (effectiveCoefficientPrefix_succ P (steps + 1) r).symm

omit [Fintype F] in
/-- Each lift preserves all initial jet entries, independently of whether it is accepted. -/
theorem polynomialJet_unshift_effectiveRegularCandidate (center : F) (P : CPolynomial F)
    (gamma : F) (k : ℕ) (hk : 0 < k) :
    polynomialJet center (unshift center (effectiveRegularCandidate k r P gamma)) =
      (polynomialJet center (unshift center P) : Fin (r + 1) → F) := by
  funext j
  rw [polynomialJet_unshift_apply, polynomialJet_unshift_apply, coeff_effectiveRegularCandidate]
  simp [show j.val ≠ k + r by omega]

/-- Every surviving prefix still realizes the supplied initial jet. -/
theorem effectiveRegularIteration_polynomialJet
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (steps : ℕ) {P : CPolynomial F}
    (hP : P ∈ (effectiveRegularIteration Q center (effectiveInitialPrefix jet) steps).candidates) :
    polynomialJet center (unshift center P) = jet := by
  induction steps generalizing P with
  | zero =>
      have heq := (mem_effectiveRegularIteration_zero_iff Q center _ P).1 hP
      subst P
      exact polynomialJet_taylor_effectiveInitialPrefix center jet
  | succ steps ih =>
      obtain ⟨previous, hprevious, gamma, _, rfl⟩ :=
        (mem_effectiveRegularIteration_succ_candidates Q center _ P steps).1 hP
      rw [polynomialJet_unshift_effectiveRegularCandidate center previous gamma _
        (Nat.succ_pos steps)]
      exact ih hprevious

omit [Fintype F] in
/-- The complete residual test is equivalent to the canonical differential equation. -/
theorem effectiveResidual_eq_zero_iff
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F) :
    effectiveResidual Q center P = 0 ↔
      differentialSpecialization (semanticEquation Q) (unshift center P) = 0 := by
  constructor
  · intro h
    have hsem := congrArg CPolynomial.toPoly h
    rw [effectiveResidual_toPoly, ← taylor_differentialSpecialization,
      CPolynomial.toPoly_zero] at hsem
    have h := congrArg (taylor (-center)) hsem
    simpa [taylor_taylor] using h
  · intro h
    apply CPolynomial.ringEquiv.injective
    simp [CPolynomial.ringEquiv_apply, effectiveResidual_toPoly,
      ← taylor_differentialSpecialization, h, CPolynomial.toPoly_zero]

/-- Exact soundness and completeness of the final executable filter, including `D < r`.
Regularity is not needed for completeness of exhaustive coefficient scanning. -/
theorem mem_effectiveRegularSolutions_iff_solution_jet
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (P : CPolynomial F) (D : ℕ) :
    P ∈ effectiveRegularSolutions Q center (effectiveInitialPrefix jet) D ↔
      P.natDegree ≤ D ∧
        differentialSpecialization (semanticEquation Q) (unshift center P) = 0 ∧
          polynomialJet center (unshift center P) = jet := by
  rw [mem_effectiveRegularSolutions_iff, effectiveResidual_eq_zero_iff]
  constructor
  · rintro ⟨hP, hdegree, hsolution⟩
    exact ⟨hdegree, hsolution, effectiveRegularIteration_polynomialJet Q center jet (D - r) hP⟩
  · rintro ⟨hdegree, hsolution, hjet⟩
    refine ⟨?_, hdegree, hsolution⟩
    have h := effectiveCoefficientPrefix_mem_iteration Q center P jet hjet hsolution (D - r)
    rwa [effectiveCoefficientPrefix_eq_self P _ (by omega)] at h

/-- Under a genuine regular jet and the characteristic bound, an actual surviving prefix has
exactly one accepted next coefficient. The existing residual invariant supplies the lift premise. -/
theorem existsUnique_effectiveRegularCoefficientScan_of_survivor
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (D steps : ℕ) (hdegree : steps + 1 + r ≤ D) (hD : D < ringChar F)
    (P : CPolynomial F)
    (hP : P ∈ (effectiveRegularIteration Q center (effectiveInitialPrefix jet) steps).candidates) :
    ∃! gamma : F, gamma ∈ (effectiveRegularCoefficientScan Q center P (steps + 1)).accepted := by
  have hresidual := effectiveRegularIteration_residual_dvd Q center (effectiveInitialPrefix jet)
    (X_dvd_shiftedJetSubstitution_effectiveInitialPrefix (semanticEquation Q) center jet hregular)
    steps P hP
  have hjet := effectiveRegularIteration_polynomialJet Q center jet steps hP
  have hsep : jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
      (polynomialJet center (unshift center P)) ≠ 0 := by
    rw [hjet]
    exact hregular.2
  obtain ⟨gamma, hgamma, hunique⟩ :=
    existsUnique_regularLiftCoefficient_of_le_of_lt_ringChar (Nat.succ_pos steps)
      (semanticEquation Q) center (unshift center P) D hdegree hD hresidual hsep
  have haccept : ∀ a : F,
      a ∈ (effectiveRegularCoefficientScan Q center P (steps + 1)).accepted ↔
        X ^ (steps + 1 + 1) ∣ shiftedJetSubstitution center
          (regularLiftCandidate center a (steps + 1) r (unshift center P))
            (semanticEquation Q) := by
    intro a
    rw [mem_effectiveRegularCoefficientScan_accepted, ← mem_effectiveRegularCoefficients,
      mem_effectiveRegularCoefficients_iff_dvd Q center P a (Nat.succ_pos steps) hresidual,
      unshift_effectiveRegularCandidate]
  exact ⟨gamma, (haccept gamma).2 hgamma, fun a ha => hunique a ((haccept a).1 ha)⟩

/-- Every permitted regular scan depth has exactly one surviving prefix. This ensures that
one-step uniqueness is not vacuous; the final exact residual filter may still reject that prefix. -/
theorem existsUnique_effectiveRegularIteration_survivor
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (D : ℕ) (hD : D < ringChar F) (steps : ℕ) (hsteps : steps ≤ D - r) :
    ∃! P : CPolynomial F,
      P ∈ (effectiveRegularIteration Q center (effectiveInitialPrefix jet) steps).candidates := by
  induction steps with
  | zero =>
      refine ⟨effectiveInitialPrefix jet, ?_, ?_⟩
      · simp
      · intro P hP
        exact (mem_effectiveRegularIteration_zero_iff Q center _ P).1 hP
  | succ steps ih =>
      obtain ⟨previous, hprevious, hpreviousUnique⟩ := ih (by omega)
      obtain ⟨gamma, hgamma, hgammaUnique⟩ :=
        existsUnique_effectiveRegularCoefficientScan_of_survivor Q center jet hregular
          D steps (by omega) hD previous hprevious
      have hcoeff : gamma ∈ effectiveRegularCoefficients Q center previous (steps + 1) := by
        simpa only [mem_effectiveRegularCoefficients,
          mem_effectiveRegularCoefficientScan_accepted] using hgamma
      refine ⟨effectiveRegularCandidate (steps + 1) r previous gamma, ?_, ?_⟩
      · exact (mem_effectiveRegularIteration_succ_candidates Q center _ _ steps).2
          ⟨previous, hprevious, gamma, hcoeff, rfl⟩
      · intro P hP
        obtain ⟨previous', hprevious', gamma', hgamma', rfl⟩ :=
          (mem_effectiveRegularIteration_succ_candidates Q center _ P steps).1 hP
        have heq := hpreviousUnique previous' hprevious'
        subst previous'
        have heq := hgammaUnique gamma' (by
          simpa only [mem_effectiveRegularCoefficients,
            mem_effectiveRegularCoefficientScan_accepted] using hgamma')
        subst gamma'
        rfl

end ReedSolomon.HiddenDerivative
