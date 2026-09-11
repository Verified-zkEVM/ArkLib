/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Certificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Profile

/-!
# Sharp retained-squarefree polynomial-curve certificates

The squarefree first-order decomposition leaves one regular chart and one ordinary
content-resultant equation.  This module keeps the exact degree budgets of both pieces:

* the ordinary root degree is `max B ((2 * M - 1) * B - M ^ 2)`;
* its challenge height is `(2 * M - 1) * H`;
* the regular chart keeps the separate total and first-derivative degrees.

This is the finite expression used by the polynomial-curve application certificates.  In
particular, it does not replace the exact content-resultant budgets by the coarser products
`B * (2 * M + 1)` and `H * (2 * M + 1)`.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicSeparantChain
open ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

noncomputable section

set_option autoImplicit false

universe u

/-- The exact unified ordinary charge for the retained content-resultant equation. -/
def retainedSquarefreeOrdinaryCurveMCARaw
    (theta : ℚ) (n D ell B M H : ℕ) : ℚ :=
  ordinaryUnifiedPowerFactorRaw theta n D ell
    (ordinaryDegreeEnvelope B M) (resultantChallengeEnvelope H M)

/-- The exact one-chart squarefree curve charge at the chosen retention split. -/
def retainedSquarefreeCurveMCASharpRaw
    (theta : ℚ) (n D ell L A B M H : ℕ) : ℚ :=
  retainedSquarefreeOrdinaryCurveMCARaw theta n D ell B M H +
    regularSymbolicCurveMCADerivativeBoundTwo n ell (D + 1) (D + 1)
      L A B M H (2 * D - 1)

private theorem natCast_ne_zero_of_sharp_char_guard
    {E : Type*} [Field E] {D M i : ℕ}
    (hchar : ringChar E = 0 ∨ max D M < ringChar E)
    (hi : 0 < i) (hiD : i ≤ D) : (i : E) ≠ 0 := by
  intro hz
  have hdiv := (ringChar.spec E i).mp hz
  rcases hchar with hzero | hpos
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hi
      ((hiD.trans (Nat.le_max_left D M)).trans_lt hpos) hdiv

open Classical in
/-- The retained squarefree decomposition with the exact ordinary content-resultant budget.
The exceptional set is fixed before the challenge and candidate, and recovery preserves the
candidate's complete agreement set. -/
theorem exists_exceptional_retainedSquarefreeCurveMCA_sharp
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E]
    {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetWeight Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : ChallengeHeightLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ))
        n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hcharE : ringChar E = 0 ∨ max D M < ringChar E := by
    rwa [ringChar_eq_of_injective_fieldHom iota]
  have htailQ : singularCurveEquation Q ≠ 0 :=
    singularCurveEquation_ne_zero Q hQ hderiv
      (hcharE.imp_right fun hmax => (Nat.le_max_right D M).trans_lt hmax)
  have htailDegree : (singularCurveEquation Q).degreeOf (some 0) ≤
      ordinaryDegreeEnvelope B M :=
    singularCurveEquation_degree_le Q hQ hjet hderiv hMB
  have htailHeight : ChallengeHeightLE (singularCurveEquation Q)
      (resultantChallengeEnvelope H M) :=
    singularCurveEquation_challengeHeightLE Q hQ hheight (by omega) hderiv
  have htailDegreePos : 1 ≤ ordinaryDegreeEnvelope B M :=
    (hM.trans hMB).trans (ordinaryDegreeEnvelope_ge_total B M)
  obtain ⟨tailExceptional, htailCard, htailGood⟩ :=
    exists_exceptional_ordinaryPowerEquation_unified domain values iota
      (singularCurveEquation Q) D (resultantChallengeEnvelope H M)
      (ordinaryDegreeEnvelope B M) A htailQ hD hell htailDegreePos
      (hDL.trans hLA) hAn htailHeight htailDegree
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiD
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_sharp_char_guard hcharE (by omega) (by omega)
  have htaylor : TaylorExponentSufficient 1 (D + 1) (2 * D - 1) := by
    convert taylorExponentSufficient_two_mul_sub_three 1
      (K := D + 1) (by omega) using 1
    all_goals omega
  obtain ⟨regularExceptional, hregularCard, hregularGood⟩ :=
    exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent
      domain values iota (positiveCurveEquation Q)
      (D + 1) (D + 1) L A B M H (2 * D - 1)
      htaylor (by omega) (by omega) le_rfl (by omega) hDL hLA hAn
      (Nat.add_pos_left hell H) (hM.trans hMB) hM hMB
      ((positiveCurveEquation_jetWeight_le Q hQ).trans hjet)
      (fun d ↦ (positiveCurveEquation_challengeHeightLE Q d).trans
        ((Nat.le_add_left _ _).trans
          (flattened_content_add_positive_challengeDegree_le Q hQ hheight)))
      ((positiveCurveEquation_yOneDegree_le Q hQ).trans hderiv) hbin
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : (exceptional.card : ℚ) ≤
        (tailExceptional.card : ℚ) + regularExceptional.card := by
      exact_mod_cast Finset.card_union_le tailExceptional regularExceptional
    apply hcard.trans
    unfold retainedSquarefreeCurveMCASharpRaw
    exact add_le_add htailCard hregularCard
  · intro z hz P hdegree hagree hroot
    have hzTail : z ∉ tailExceptional := fun hmem ↦
      hz (Finset.mem_union_left regularExceptional hmem)
    have hzRegular : z ∉ regularExceptional := fun hmem ↦
      hz (Finset.mem_union_right tailExceptional hmem)
    by_cases hpositive : differentialSpecialization
        (challengeSpecialization (positiveCurveEquation Q) z) P = 0
    · by_cases hseparant : differentialSpecialization
          (challengeSpecialization
            (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P = 0
      · have htailResult := htailGood z hzTail P hdegree
          (singularCurveEquation_routes_nonregular Q hQ z P hroot
            (Or.inr hseparant)) (by simpa only using hagree)
        simpa only using htailResult
      · apply hregularGood z hzRegular P hdegree hagree hpositive
        simpa only [challengeSpecialization, separant, MvPolynomial.pderiv_map,
          show (Fin.last 1 : Fin 2) = 1 by decide] using hseparant
    · have htailResult := htailGood z hzTail P hdegree
        (singularCurveEquation_routes_nonregular Q hQ z P hroot
          (Or.inl hpositive)) (by simpa only using hagree)
      simpa only using htailResult

private theorem degreeOf_extendSymbolicCoefficients_le
    {F E : Type*} [Field F] [Field E] {d : ℕ}
    (iota : F →+* E) (Q : DifferentialPolynomial F[X] d) (j : Fin (d + 1)) :
    (extendSymbolicCoefficients iota Q).degreeOf (some j) ≤ Q.degreeOf (some j) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro mon hmon
  exact MvPolynomial.monomial_le_degreeOf _
    (MvPolynomial.support_map_subset (Polynomial.mapRingHom iota) Q hmon)

open Classical in
/-- A finite interpolation certificate supplies the sharp retained-squarefree curve theorem over
the algebraic closure.  The certificate degree and recovery degree remain independent. -/
theorem exists_extensionExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
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
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpRaw
        (((n - (k - 1) : ℕ) : ℚ) / ((A - (k - 1) : ℕ) : ℚ))
        n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  let Q := extendSymbolicCoefficients iota cert.Q
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans cert.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M :=
    (degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans cert.jetDegree_one_le
  have hheight : ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveMCA_sharp
      domain values iota Q hQ (by omega) (by omega) hLA hAn hell hM hMB
        hjet hderiv hheight hchar
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

open Classical in
/-- Base-field form of the sharp certificate theorem, including full agreement-set equality. -/
theorem exists_baseExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
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
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpRaw
        (((n - (k - 1) : ℕ) : ℚ) / ((A - (k - 1) : ℕ) : ℚ))
        n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
      domain values iota columns cert hk hkL hLA hAn hell hM hMB hchar
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend
      domain values iota k A extensionExceptional hgood
  refine ⟨exceptional, ?_, hgoodBase⟩
  exact (show (exceptional.card : ℚ) ≤ (extensionExceptional.card : ℚ) by
    exact_mod_cast hcardBase).trans hcard

end

end ReedSolomon.FirstOrder.Squarefree

namespace ReedSolomon.CurveCertificate

open CurveProfile ReedSolomon.FirstOrder.Squarefree

noncomputable section

universe u

/-- The sharp retained-squarefree curve expression attached to one finite profile and split. -/
def squarefreeSharpCurveEnvelope (p : LineProfile) (split : ℕ) : ℚ :=
  retainedSquarefreeCurveMCASharpRaw
    (((p.n - p.D : ℕ) : ℚ) / ((p.agreement - p.D : ℕ) : ℚ))
    p.n p.D p.batchingDegree split p.agreement p.totalJetCap
      p.firstDerivativeCap p.height

open Classical in
/-- A verified finite profile inherits the exact one-chart/content-resultant curve theorem. -/
theorem exists_exceptional_exact_powerAgreement_squarefree_sharp
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    (split : ℕ) (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ squarefreeSharpCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  let curveWord : Fin p.n → F[X] := fun i ↦
    powerBatchedCoordinate fun t ↦ values t i
  have hw : ∀ i, (curveWord i).natDegree ≤ p.batchingDegree := by
    intro i
    exact powerBatchedCoordinate_natDegree_le fun t ↦ values t i
  obtain ⟨cert⟩ := hp.exists_certificate domain curveWord hw
  have hresult :=
    exists_baseExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
      domain values iota p.columns cert hk hsplit.1 hsplit.2.1 hsplit.2.2
        hell hM hMB hchar
  simpa only [squarefreeSharpCurveEnvelope, LineProfile.D] using hresult

open Classical in
/-- A checked integer ceiling can be placed directly on the sharp semantic exceptional set. -/
theorem exists_exceptional_exact_powerAgreement_squarefree_sharp_le
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    (split budget : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (hbound : squarefreeSharpCurveEnvelope p split ≤ budget)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F, (exceptional.card : ℚ) ≤ budget ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exact_powerAgreement_squarefree_sharp
      hp split hsplit hk hell hM hMB domain values iota hchar
  exact ⟨exceptional, hcard.trans hbound, hgood⟩

end

end ReedSolomon.CurveCertificate
