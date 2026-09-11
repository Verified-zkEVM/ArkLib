/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveStages
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.CoefficientExtension
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CurveUnified
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent

/-!
# Certificate bridge for retained squarefree MCA

This module connects the retained squarefree geometric count to the actual finite interpolation
certificate.  The interpolation degree `Dcert` remains separate from the recovery degree `k - 1`.
The received word is an arbitrary polynomial curve, so the result applies to every batching degree,
not just affine lines.

The extension-field theorem chooses one exceptional set before the challenge and candidate.  Its
base-field corollary descends the same exact full-agreement conclusion.  The ordinary-tail premise
is explicit so that the shared ordinary-factor budget can be connected without duplicating that
theorem family here.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

noncomputable section

set_option autoImplicit false

universe u

private theorem degreeOf_extendSymbolicCoefficients_le
    {F E : Type*} [Field F] [Field E] {d : ℕ}
    (iota : F →+* E) (Q : DifferentialPolynomial F[X] d) (j : Fin (d + 1)) :
    (extendSymbolicCoefficients iota Q).degreeOf (some j) ≤ Q.degreeOf (some j) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro mon hmon
  exact MvPolynomial.monomial_le_degreeOf _
    (MvPolynomial.support_map_subset (Polynomial.mapRingHom iota) Q hmon)

/-- An actual finite curve certificate supplies the equation-root premise of the retained
squarefree theorem.  The certificate's interpolation weight `Dcert` is independent of the
recovery degree `k - 1`. -/
theorem exists_extensionExceptional_retainedSquarefreeCurveMCA_of_certificate_of_tail
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hcurve : 0 < ell + H) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (htail : HasRetainedOrdinaryCurveTransfer (D := k - 1) (A := A)
      (B := B) (M := M) (H := H) domain values iota
        (singularCurveEquation (extendSymbolicCoefficients iota cert.Q))) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveMCARaw
        (HiddenDerivative.hybridTheta n (k - 1) A) n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  let Q := extendSymbolicCoefficients iota cert.Q
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : HiddenDerivative.SymbolicSeparantChain.jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans cert.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M :=
    (degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans cert.jetDegree_one_le
  have hheight : HiddenDerivative.ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveMCA_of_tail
      domain values iota Q hQ (by omega) (by omega) hLA hAn hcurve hM hMB
        hjet hderiv hheight hchar htail
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hdegree hagree
  let indices := polynomialAgreementSet (mappedDomain domain iota)
    (powerBatchedWord (fun t i ↦ iota (values t i)) z) P
  have hroot := (cert.specialization_sound iota z).2 indices P hdegree hagree (by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simpa [mappedDomain, powerBatchedCoordinate, powerBatchedWord,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial, mul_comm] using hj')
  have hdegree' : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
    have hkEq : ((k - 1 : ℕ) : WithBot ℕ) + 1 = (k : WithBot ℕ) := by
      change WithBot.some (k - 1) + WithBot.some 1 = WithBot.some k
      rw [← WithBot.coe_add, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rwa [hkEq]
  have hout := hgood z hz P hdegree' hagree (by
    change differentialSpecialization
      (MvPolynomial.map (Polynomial.aeval z).toRingHom Q) P = 0
    have heval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
      ext <;> simp
    rw [heval]
    change differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom z)
        (extendSymbolicCoefficients iota cert.Q)) P = 0
    rw [specialize_extendSymbolicCoefficients]
    exact hroot)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hout

/-- Descend the retained squarefree polynomial-curve result to the original field.  The returned
tuple has coefficients in that field and its power-batched word has exactly the candidate's full
agreement set. -/
theorem exists_baseExceptional_retainedSquarefreeCurveMCA_of_certificate_of_tail
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hcurve : 0 < ell + H) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (htail : HasRetainedOrdinaryCurveTransfer (D := k - 1) (A := A)
      (B := B) (M := M) (H := H) domain values iota
        (singularCurveEquation (extendSymbolicCoefficients iota cert.Q))) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveMCARaw
        (HiddenDerivative.hybridTheta n (k - 1) A) n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeCurveMCA_of_certificate_of_tail
      domain values iota columns cert hk hkL hLA hAn hcurve hM hMB hchar htail
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend
      domain values iota k A extensionExceptional hgood
  refine ⟨exceptional, ?_, hgoodBase⟩
  exact (show (exceptional.card : ℝ) ≤ (extensionExceptional.card : ℝ) by
    exact_mod_cast hcardBase).trans hcard

open Classical in
/-- The all-characteristic ordinary theorem closes the retained tail of an actual curve
certificate, leaving no assumed recovery interface in the public result. -/
theorem exists_extensionExceptional_retainedSquarefreeCurveMCA_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveMCARaw
        (HiddenDerivative.hybridTheta n (k - 1) A) n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  let Q := extendSymbolicCoefficients iota cert.Q
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : HiddenDerivative.SymbolicSeparantChain.jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans cert.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M :=
    (degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans cert.jetDegree_one_le
  have hheight : HiddenDerivative.ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  have htail : HasRetainedOrdinaryCurveTransfer (D := k - 1) (A := A)
      (B := B) (M := M) (H := H) domain values iota (singularCurveEquation Q) :=
    hasRetainedOrdinaryCurveTransfer_of_unified domain values iota Q hQ
      (by omega) hell (by omega) hAn hM hMB hjet hderiv hheight hchar
  exact exists_extensionExceptional_retainedSquarefreeCurveMCA_of_certificate_of_tail
    domain values iota columns cert hk hkL hLA hAn (by omega) hM hMB hchar
      (by simpa only [Q] using htail)

open Classical in
/-- Base-field form of the completed retained squarefree certificate theorem. Recovered power
constituents and the candidate's complete agreement set descend to the original field. -/
theorem exists_baseExceptional_retainedSquarefreeCurveMCA_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveMCARaw
        (HiddenDerivative.hybridTheta n (k - 1) A) n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  let Q := extendSymbolicCoefficients iota cert.Q
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : HiddenDerivative.SymbolicSeparantChain.jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans cert.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M :=
    (degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans cert.jetDegree_one_le
  have hheight : HiddenDerivative.ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  have htail : HasRetainedOrdinaryCurveTransfer (D := k - 1) (A := A)
      (B := B) (M := M) (H := H) domain values iota (singularCurveEquation Q) :=
    hasRetainedOrdinaryCurveTransfer_of_unified domain values iota Q hQ
      (by omega) hell (by omega) hAn hM hMB hjet hderiv hheight hchar
  exact exists_baseExceptional_retainedSquarefreeCurveMCA_of_certificate_of_tail
    domain values iota columns cert hk hkL hLA hAn (by omega) hM hMB hchar
      (by simpa only [Q] using htail)

end

end ReedSolomon.FirstOrder.Squarefree
