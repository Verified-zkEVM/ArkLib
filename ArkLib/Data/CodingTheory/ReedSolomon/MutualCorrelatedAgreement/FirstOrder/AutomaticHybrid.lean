/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.OrdinaryTail
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.AutomaticCertificate
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Automatic first-order hybrid transfer

This file combines the actual first-order descent, its ordinary tail, and the optimized hybrid
arithmetic.  It first gives a transfer for any nonzero equation with the required support bounds,
then constructs that equation from the automatic interpolation recipe.  The base-field theorem
uses an algebraic closure only inside its proof and descends both the equation-restricted result
and its exceptional set.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon

open HiddenDerivative MvPolynomial HiddenDerivative.SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

open Classical in
/-- A nonzero first-order equation with the advertised support bounds has the optimized hybrid
exceptional set.  The characteristic guard is exactly the guard needed by the regular stages:
characteristic zero, or characteristic larger than `max D M`. -/
theorem exists_exceptional_firstOrder_hybrid
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n D A h mu M : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1)
    (hQ : Q ≠ 0) (hweight : jetWeight Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M) (hheight : ChallengeHeightLE Q h)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hmu : 1 ≤ mu) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
          hybridEOptimizedRaw (hybridTheta n D A) n D A h mu M ∧
      exceptional.card ≤
          hybridEOptimizedCeil (hybridTheta n D A) n D A h mu M ∧
      (exceptional.card : ℝ) ≤
          hybridEClosed (hybridTheta n D A) n D h mu M ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  classical
  have hcharE : ringChar E = 0 ∨ M < ringChar E := by
    rw [ringChar_eq_of_injective_fieldHom iota]
    exact hchar.imp_right (fun hp ↦ (Nat.le_max_right D M).trans_lt hp)
  obtain ⟨descent⟩ := exists_firstOrderHybridDescent Q hQ hweight hdegree hheight
    (hcharE.imp_right (hdegree.trans_lt ·))
  exact exists_exceptional_firstOrder_hybrid_optimized_of_tail
    domain f g iota Q descent hD hDA hAn hmu hMmu hchar
      (descent.hasOrdinaryTailTransfer domain f g iota Q hD hDA hAn)

open Classical in
/-- The automatic interpolation recipe constructs an extension-field equation and discharges
the complete hybrid transfer, including optimized real, ceiling, and closed-form bounds. -/
theorem exists_automaticFirstOrder_hybridEquation
    {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E]
    (hchar : ringChar F = 0 ∨
      max D (automaticDerivativeCap rho a) < ringChar F)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E) :
    ∃ Q : DifferentialPolynomial E[X] 1,
      Q ≠ 0 ∧
      jetWeight Q ≤ automaticJetDegree rho a ∧
      jetDegree Q (1 : Fin 2) ≤ automaticDerivativeCap rho a ∧
      ChallengeHeightLE Q (automaticChallengeHeight rho a) ∧
      (∀ z : E, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0) ∧
      ∃ exceptional : Finset E,
        (exceptional.card : ℝ) ≤
          hybridEOptimizedRaw (hybridTheta n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        exceptional.card ≤
          hybridEOptimizedCeil (hybridTheta n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        (exceptional.card : ℝ) ≤
          hybridEClosed (hybridTheta n D A) n D
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
          HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  classical
  have hDA : D < A := by
    have hrhoa : rho < a :=
      (rho_lt_automaticAgreement hrho hrhoOne ha).trans_le automaticAgreement_le
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hDk : D < k := by omega
    have hreal : (D : ℝ) < A := by
      calc
        (D : ℝ) < k := by exact_mod_cast hDk
        _ ≤ rho * n := hkRate
        _ < a * n := mul_lt_mul_of_pos_right hrhoa hnR
        _ ≤ A := hA
    exact_mod_cast hreal
  have hDone : 1 ≤ D := by omega
  have hmu : 1 ≤ automaticJetDegree rho a :=
    automaticJetDegree_pos hrho hrhoOne ha haOne
  have hMmu : automaticDerivativeCap rho a ≤ automaticJetDegree rho a := by
    unfold automaticDerivativeCap
    exact min_le_right _ _
  obtain ⟨cert⟩ := exists_automaticFirstOrder_symbolicCertificate
    hrho hrhoOne ha haOne hn hD hk hkRate hA
    (mappedDomain domain iota) (fun i ↦ iota (f i)) (fun i ↦ iota (g i))
  let curve := cert.toCurve
  obtain ⟨exceptional, hraw, hceil, hclosed, hgood⟩ :=
    exists_exceptional_firstOrder_hybrid domain f g iota curve.Q curve.nonzero
      curve.jetWeight_le curve.jetDegree_one_le curve.challengeDegree_le
      hDone hDA hAn hmu hMmu hchar
  have hsound : ∀ z : E, ∀ P : E[X], P.degree < D + 1 →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
      differentialSpecialization (challengeSpecialization curve.Q z) P = 0 := by
    intro z P hP hagree
    have hline : powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z =
        (fun i ↦ iota (f i) + z * iota (g i)) :=
      powerBatchedWord_pair_eq f g iota z
    have hPk : P.degree < k := by
      have hDk : D + 1 = k := by omega
      have hP' : P.degree < ((D + 1 : ℕ) : WithBot ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hP
      rw [hDk] at hP'
      exact hP'
    have hagreeLine : A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card := by
      rwa [hline] at hagree
    have hs := (cert.specialization_sound (RingHom.id E) z).2
      (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P) P hPk hagreeLine
      (fun i hi ↦ by simpa using (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id E) z =
        (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro x
        simp
      · simp
    have hcurveQ : curve.Q = cert.Q := rfl
    rw [challengeSpecialization, ← heval, hcurveQ]
    exact hs
  exact ⟨curve.Q, curve.nonzero, curve.jetWeight_le, curve.jetDegree_one_le,
    curve.challengeDegree_le, hsound, exceptional, hraw, hceil, hclosed,
    fun z hz P hP hagree ↦ hgood z hz P hP hagree (hsound z P hP hagree)⟩

private theorem jetWeight_map_eq
    {F E : Type*} [Field F] [Field E] (iota : F →+* E)
    (Q : DifferentialPolynomial F[X] 1) :
    jetWeight (MvPolynomial.map (Polynomial.mapRingHom iota) Q) = jetWeight Q := by
  unfold jetWeight MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective Q
    (Polynomial.map_injective iota iota.injective)]

open Classical in
/-- The automatic first-order equation theorem over an arbitrary field.  The algebraic closure
and all Frobenius choices are internal; the returned equation, exceptional challenges,
polynomials, and exact power agreement all live over the base field. -/
theorem exists_automaticFirstOrder_hybridEquation_base
    {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F]
    (hchar : ringChar F = 0 ∨
      max D (automaticDerivativeCap rho a) < ringChar F)
    (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ Q : DifferentialPolynomial F[X] 1,
      Q ≠ 0 ∧
      jetWeight Q ≤ automaticJetDegree rho a ∧
      jetDegree Q (1 : Fin 2) ≤ automaticDerivativeCap rho a ∧
      ChallengeHeightLE Q (automaticChallengeHeight rho a) ∧
      (∀ z : F, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord ![f, g] z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          hybridEOptimizedRaw (hybridTheta n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        exceptional.card ≤
          hybridEOptimizedCeil (hybridTheta n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        (exceptional.card : ℝ) ≤
          hybridEClosed (hybridTheta n D A) n D
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
          A ≤ (polynomialAgreementSet domain
            (powerBatchedWord ![f, g] z) P).card →
          HasExactPowerAgreement domain ![f, g] (RingHom.id F) (D + 1) z P := by
  classical
  obtain ⟨cert⟩ := exists_automaticFirstOrder_symbolicCertificate
    hrho hrhoOne ha haOne hn hD hk hkRate hA domain f g
  let curve := cert.toCurve
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  let QE := MvPolynomial.map (Polynomial.mapRingHom iota) curve.Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply curve.nonzero
    exact MvPolynomial.map_injective (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective) (by simpa only [map_zero] using hz)
  have hweightE : jetWeight QE ≤ automaticJetDegree rho a := by
    simpa only [QE, jetWeight_map_eq] using curve.jetWeight_le
  have hdegreeE : jetDegree QE (1 : Fin 2) ≤ automaticDerivativeCap rho a := by
    simpa only [QE, jetDegree_map_eq (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective)] using curve.jetDegree_one_le
  have hheightE : ChallengeHeightLE QE (automaticChallengeHeight rho a) :=
    HiddenDerivative.ChallengeHeightLE.map_coefficients iota curve.challengeDegree_le
  have hDone : 1 ≤ D := by omega
  have hDA : D < A := by
    have hrhoa : rho < a :=
      (rho_lt_automaticAgreement hrho hrhoOne ha).trans_le automaticAgreement_le
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hDk : D < k := by omega
    have hreal : (D : ℝ) < A := by
      calc
        (D : ℝ) < k := by exact_mod_cast hDk
        _ ≤ rho * n := hkRate
        _ < a * n := mul_lt_mul_of_pos_right hrhoa hnR
        _ ≤ A := hA
    exact_mod_cast hreal
  have hmu : 1 ≤ automaticJetDegree rho a :=
    automaticJetDegree_pos hrho hrhoOne ha haOne
  have hMmu : automaticDerivativeCap rho a ≤ automaticJetDegree rho a := by
    unfold automaticDerivativeCap
    exact min_le_right _ _
  obtain ⟨extensionExceptional, hraw, hceil, hclosed, hgood⟩ :=
    exists_exceptional_firstOrder_hybrid domain f g iota QE hQE hweightE hdegreeE
      hheightE hDone hDA hAn hmu hMmu hchar
  obtain ⟨exceptional, hcard, hbase⟩ :=
    exists_exceptional_equation_correlatedAgreement_descend
      domain f g iota curve.Q (D + 1) A extensionExceptional (by
        intro z hz P hP hagree hroot
        apply exactCorrelatedPair_of_powerAgreement_one domain ![f, g] iota z P
        apply hgood z hz P hP
        · rw [powerBatchedWord_pair_eq]
          exact hagree
        · exact hroot)
  have hsound : ∀ z : F, ∀ P : F[X], P.degree < D + 1 →
      A ≤ (polynomialAgreementSet domain (powerBatchedWord ![f, g] z) P).card →
      differentialSpecialization (challengeSpecialization curve.Q z) P = 0 := by
    intro z P hP hagree
    have hline : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have hPk : P.degree < k := by
      have hDk : D + 1 = k := by omega
      have hP' : P.degree < ((D + 1 : ℕ) : WithBot ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hP
      rw [hDk] at hP'
      exact hP'
    have hagreeLine : A ≤
        (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card := by
      rwa [hline] at hagree
    have hs := (cert.specialization_sound (RingHom.id F) z).2
      (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) P hPk hagreeLine
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z =
        (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro x
        simp
      · simp
    have hcurveQ : curve.Q = cert.Q := rfl
    rw [challengeSpecialization, ← heval, hcurveQ]
    exact hs
  refine ⟨curve.Q, curve.nonzero, curve.jetWeight_le, curve.jetDegree_one_le,
    curve.challengeDegree_le, hsound, exceptional, ?_, ?_, ?_, ?_⟩
  · exact
      (by exact_mod_cast hcard : (exceptional.card : ℝ) ≤ extensionExceptional.card).trans hraw
  · exact hcard.trans hceil
  · exact (by exact_mod_cast hcard : (exceptional.card : ℝ) ≤ extensionExceptional.card).trans
      hclosed
  · intro z hz P hP hagree
    apply powerAgreement_one_of_exactCorrelatedPair domain f g (RingHom.id F) z P
    apply hbase z hz P hP
    · have hline : powerBatchedWord ![f, g] z =
          (fun i ↦ f i + z * g i) := by
        funext i
        simp [powerBatchedWord, Fin.sum_univ_two]
      rwa [hline] at hagree
    · exact hsound z P hP hagree

end

end ReedSolomon
