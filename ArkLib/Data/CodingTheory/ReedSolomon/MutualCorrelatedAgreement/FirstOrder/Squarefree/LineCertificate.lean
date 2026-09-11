/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CurveBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine

/-!
# Retained squarefree line MCA from a symbolic certificate

This is the finite-length line specialization of the general curve theorem.  It consumes an actual
`FirstOrderSymbolicCertificate`; its interpolation degree `Dcert` is not identified with the
recovery degree `k - 1`.  The balanced split gives the displayed finite-length envelope, and the
power-agreement conclusion is converted to a correlated pair without losing full agreement-set
equality.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

noncomputable section

universe u

private theorem line_degreeOf_extendSymbolicCoefficients_le
    {F E : Type*} [Field F] [Field E]
    (iota : F →+* E) (Q : DifferentialPolynomial F[X] 1) (j : Fin 2) :
    (extendSymbolicCoefficients iota Q).degreeOf (some j) ≤ Q.degreeOf (some j) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro mon hmon
  exact MvPolynomial.monomial_le_degreeOf _
    (MvPolynomial.support_map_subset (Polynomial.mapRingHom iota) Q hmon)

open Classical in
private theorem hasRetainedOrdinaryLineTransfer_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u}
      Dcert A m M B k H domain f g columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    HasRetainedOrdinaryCurveTransfer (D := k - 1) (A := A)
      (B := B) (M := M) (H := H) domain ![f, g] iota
        (singularCurveEquation (extendSymbolicCoefficients iota cert.Q)) := by
  let Q := extendSymbolicCoefficients iota cert.Q
  let curve := cert.toCurve
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : HiddenDerivative.SymbolicSeparantChain.jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans curve.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M :=
    (line_degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans curve.jetDegree_one_le
  have hheight : ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  exact hasRetainedOrdinaryCurveTransfer_of_unified domain ![f, g] iota Q hQ
    (by omega) (by omega) (by omega) hAn hM hMB hjet hderiv hheight hchar

/-- Extension-field form of the retained squarefree line theorem from an actual certificate. -/
theorem exists_extensionExceptional_retainedSquarefreeLineMCA_of_certificate_of_tail
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n N Dcert A m M B k H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u}
      Dcert A m M B k H domain f g columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (htail : HasRetainedOrdinaryCurveTransfer (D := k - 1) (A := A)
      (B := B) (M := M) (H := H) domain ![f, g] iota
        (singularCurveEquation (extendSymbolicCoefficients iota cert.Q))) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeLineMCAEnvelope
        (hybridTheta n (k - 1) A) n (k - 1) B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactPowerAgreement domain ![f, g] iota k z P := by
  classical
  let Q := extendSymbolicCoefficients iota cert.Q
  let curve := cert.toCurve
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : HiddenDerivative.SymbolicSeparantChain.jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans curve.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M := by
    apply (line_degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans
    exact curve.jetDegree_one_le
  have hheight : ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveMCA_of_tail
      domain ![f, g] iota Q hQ (by omega)
        (hybridBalancedL_bounds (D := k - 1) (A := A) (by omega)).1
        (hybridBalancedL_bounds (D := k - 1) (A := A) (by omega)).2 hAn
        (by omega) hM hMB hjet hderiv hheight hchar (by simpa only [Q] using htail)
  refine ⟨exceptional, hcard.trans ?_, ?_⟩
  · exact retainedSquarefreeCurveMCARaw_balanced_line_le
      (D := k - 1) (A := A) (by omega) (by omega) hAn hM hMB
  · intro z hz P hdegree hagree
    have hline : powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z =
        (fun i ↦ iota (f i) + z * iota (g i)) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have hdegree' : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
      have hkEq : ((k - 1 : ℕ) : WithBot ℕ) + 1 = (k : WithBot ℕ) := by
        change WithBot.some (k - 1) + WithBot.some 1 = WithBot.some k
        rw [← WithBot.coe_add, Nat.sub_add_cancel (by omega : 1 ≤ k)]
      rwa [hkEq]
    let indices := polynomialAgreementSet (mappedDomain domain iota)
      (fun i ↦ iota (f i) + z * iota (g i)) P
    have hroot := (cert.specialization_sound iota z).2
      indices P hdegree hagree (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    have hroot' : differentialSpecialization (challengeSpecialization Q z) P = 0 := by
      change differentialSpecialization
        (MvPolynomial.map (Polynomial.aeval z).toRingHom Q) P = 0
      have heval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
        ext <;> simp
      rw [heval]
      change differentialSpecialization
        (MvPolynomial.map (Polynomial.evalRingHom z)
          (extendSymbolicCoefficients iota cert.Q)) P = 0
      rw [specialize_extendSymbolicCoefficients]
      exact hroot
    have hpower := hgood z hz P hdegree' (by rwa [hline]) hroot'
    have hkEq : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    rw [hkEq] at hpower
    exact hpower

open Classical in
/-- Completed extension-field line theorem from an actual certificate. The shared ordinary
factor theorem supplies the retained tail in every characteristic allowed by the explicit guard. -/
theorem exists_extensionExceptional_retainedSquarefreeLineMCA_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u}
      Dcert A m M B k H domain f g columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeLineMCAEnvelope
        (hybridTheta n (k - 1) A) n (k - 1) B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactPowerAgreement domain ![f, g] iota k z P := by
  apply exists_extensionExceptional_retainedSquarefreeLineMCA_of_certificate_of_tail
    domain f g iota columns cert hk hkA hAn hM hMB hchar
  exact hasRetainedOrdinaryLineTransfer_of_certificate
    domain f g iota columns cert hk hkA hAn hM hMB hchar

/-- Descending the extension result gives a base-field correlated pair with full agreement. -/
theorem exists_baseExceptional_retainedSquarefreeLineMCA_of_certificate_of_tail
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n N Dcert A m M B k H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u}
      Dcert A m M B k H domain f g columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (htail : HasRetainedOrdinaryCurveTransfer (D := k - 1) (A := A)
      (B := B) (M := M) (H := H) domain ![f, g] iota
        (singularCurveEquation (extendSymbolicCoefficients iota cert.Q))) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ retainedSquarefreeLineMCAEnvelope
        (hybridTheta n (k - 1) A) n (k - 1) B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeLineMCA_of_certificate_of_tail
      domain f g iota columns cert hk hkA hAn hM hMB hchar htail
  have hgoodPower : ∀ z ∉ extensionExceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
      HasExactPowerAgreement domain ![f, g] iota k z P := by
    intro z hz P hdegree hagree
    apply hgood z hz P hdegree
    have hline : powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z =
        (fun i ↦ iota (f i) + z * iota (g i)) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    rwa [hline] at hagree
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend
      domain ![f, g] iota k A extensionExceptional hgoodPower
  refine ⟨exceptional, ?_, ?_⟩
  · exact (show (exceptional.card : ℝ) ≤ (extensionExceptional.card : ℝ) by
      exact_mod_cast hcardBase).trans hcard
  · intro z hz P hdegree hagree
    have hline : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have hpower := hgoodBase z hz P hdegree (by rwa [hline])
    exact exactCorrelatedPair_of_powerAgreement_one
      domain ![f, g] (RingHom.id F) z P hpower

open Classical in
/-- Completed base-field line theorem from an actual certificate, with exact agreement-set
equality for the recovered correlated pair. -/
theorem exists_baseExceptional_retainedSquarefreeLineMCA_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u}
      Dcert A m M B k H domain f g columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ retainedSquarefreeLineMCAEnvelope
        (hybridTheta n (k - 1) A) n (k - 1) B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  apply exists_baseExceptional_retainedSquarefreeLineMCA_of_certificate_of_tail
    domain f g iota columns cert hk hkA hAn hM hMB hchar
  exact hasRetainedOrdinaryLineTransfer_of_certificate
    domain f g iota columns cert hk hkA hAn hM hMB hchar

end

end ReedSolomon.FirstOrder.Squarefree
