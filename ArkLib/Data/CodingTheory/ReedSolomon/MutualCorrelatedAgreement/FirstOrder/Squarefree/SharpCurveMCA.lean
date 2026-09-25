/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CurveMCA

/-!
# Sharp retained squarefree first-order curve agreement

The squarefree first-order decomposition leaves one regular chart and one ordinary
content-resultant equation. This module keeps the exact degree budgets of both pieces:

* the ordinary root degree is `ordinaryDegreeEnvelope B M = max B ((2 M - 1) B - M²)`;
* its challenge height is `resultantChallengeEnvelope H M = (2 M - 1) H`;
* the regular chart keeps the separate total and first-derivative degrees.

The ordinary charge is the free-retention charge at a retention threshold `L₀` chosen
independently of the regular threshold `L`. Its minimum over `D < L₀ ≤ A` is attained, so the
optimized charge is itself the size of one exceptional set fixed before the challenge.

## Main statements

* `retainedSquarefreeCurveSharpChargeAt` is the sharp charge at thresholds `L₀` and `L`, and
  `retainedSquarefreeCurveSharpOptimizedCharge` minimizes its ordinary part over `L₀` with
  `curveRetentionMinimum`.
* `retainedSquarefreeCurveSharpOptimizedCharge_le_chargeAt` compares the optimized charge with
  every threshold.
* `exists_exceptional_retainedSquarefreeCurveAgreement_sharpAt` and
  `exists_exceptional_retainedSquarefreeCurveAgreement_sharpOptimized` bound the exceptional set
  of a retained squarefree equation by these charges.
* `exists_extensionExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate`
  and `exists_baseExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate`
  apply the optimized bound to a finite first-order curve certificate.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative

noncomputable section

/-- The ordinary content-resultant charge at retention threshold `L₀`: the free-retention charge
with root degree `ordinaryDegreeEnvelope B M` and height `resultantChallengeEnvelope H M`. -/
def retainedSquarefreeOrdinaryCurveChargeAt (n D ell L₀ A B M H : ℕ) : ℝ :=
  (ordinaryUnifiedPowerFactorAt n D ell
    (ordinaryDegreeEnvelope B M) (resultantChallengeEnvelope H M) A L₀ : ℝ)

/-- The sharp retained squarefree charge with ordinary threshold `L₀` and regular threshold `L`.
-/
def retainedSquarefreeCurveSharpChargeAt (n D ell L₀ L A B M H : ℕ) : ℝ :=
  retainedSquarefreeOrdinaryCurveChargeAt n D ell L₀ A B M H +
    (regularPowerBatchedDerivativeCappedBoundTwo n ell (D + 1) (D + 1)
      L A B M H (regularTaylorExponent D) : ℝ)

/-- The sharp retained squarefree charge with the ordinary threshold minimized over
`D < L₀ ≤ A`, independently of the regular threshold `L`. -/
def retainedSquarefreeCurveSharpOptimizedCharge (n D ell L A B M H : ℕ) : ℝ :=
  curveRetentionMinimum D A (retainedSquarefreeOrdinaryCurveChargeAt n D ell · A B M H) +
    (regularPowerBatchedDerivativeCappedBoundTwo n ell (D + 1) (D + 1)
      L A B M H (regularTaylorExponent D) : ℝ)

/-- The optimized sharp charge is at most the sharp charge at every admissible ordinary
threshold `D < L₀ ≤ A`. -/
theorem retainedSquarefreeCurveSharpOptimizedCharge_le_chargeAt {n D ell L₀ L A B M H : ℕ}
    (hDL₀ : D < L₀) (hL₀A : L₀ ≤ A) :
    retainedSquarefreeCurveSharpOptimizedCharge n D ell L A B M H ≤
      retainedSquarefreeCurveSharpChargeAt n D ell L₀ L A B M H :=
  add_le_add_left (curveRetentionMinimum_le _ hDL₀ hL₀A) _

/-- A retained squarefree first-order equation with jet degree at most `B`, `Y₁` degree at most
`1 ≤ M ≤ B` and coefficient height at most `H` has one exceptional set of size at most
`retainedSquarefreeCurveSharpChargeAt n D ell L₀ L A B M H`, for ordinary threshold
`D < L₀ ≤ A` and regular threshold `D < L ≤ A ≤ n`. Outside it, every root of degree `< D + 1`
with at least `A` agreements has exact power agreement, in every characteristic above
`max D M`. -/
theorem exists_exceptional_retainedSquarefreeCurveAgreement_sharpAt
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D ell L₀ L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL₀ : D < L₀) (hL₀A : L₀ ≤ A)
    (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : CoeffNatDegreeLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveSharpChargeAt n D ell L₀ L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hcharE : ringChar E = 0 ∨ M < ringChar E := by
    have heq : ringChar E = ringChar F := by
      let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
      exact ringChar.eq E (ringChar F)
    rw [heq]
    exact hchar.imp_right fun hmax ↦ (Nat.le_max_right D M).trans_lt hmax
  obtain ⟨tailExceptional, htailCard, htailGood⟩ :=
    exists_exceptional_ordinaryPowerEquation_unifiedAt domain values iota
      (singularCurveEquation Q) D (resultantChallengeEnvelope H M) (ordinaryDegreeEnvelope B M)
      L₀ A (singularCurveEquation_ne_zero Q hderiv hcharE) hD hell
      ((hM.trans hMB).trans (le_max_left _ _)) hDL₀ hL₀A
      (singularCurveEquation_coeffNatDegreeLE Q hheight hM hderiv)
      (singularCurveEquation_degree_le Q hjet hderiv hMB)
  have htail : ∃ exceptional : Finset E, (exceptional.card : ℝ) ≤
      retainedSquarefreeOrdinaryCurveChargeAt n D ell L₀ A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization (singularCurveEquation Q) z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P :=
    ⟨tailExceptional, by unfold retainedSquarefreeOrdinaryCurveChargeAt; exact_mod_cast htailCard,
      fun z hz P hdegree hagree hroot ↦ by
        convert htailGood z hz P hdegree hroot (by convert hagree)⟩
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveAgreement_of_singularTail domain values iota Q hQ
      hD hDL hLA hAn (by omega) hM hMB hjet hderiv hheight hchar _ htail
  exact ⟨exceptional, hcard, hgood⟩

/-- The bound of `exists_exceptional_retainedSquarefreeCurveAgreement_sharpAt` at the attained
ordinary minimum: one exceptional set of size at most
`retainedSquarefreeCurveSharpOptimizedCharge n D ell L A B M H`. -/
theorem exists_exceptional_retainedSquarefreeCurveAgreement_sharpOptimized
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : CoeffNatDegreeLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveSharpOptimizedCharge n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  obtain ⟨L₀, hDL₀, hL₀A, hL₀⟩ := exists_curveRetentionMinimum
    (retainedSquarefreeOrdinaryCurveChargeAt n D ell · A B M H) (show D < A by omega)
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveAgreement_sharpAt domain values iota Q hQ hD
      hDL₀ hL₀A hDL hLA hAn hell hM hMB hjet hderiv hheight hchar
  refine ⟨exceptional, ?_, hgood⟩
  rwa [retainedSquarefreeCurveSharpChargeAt, hL₀] at hcard

universe u

/-- A finite first-order curve certificate with recovery degree `k - 1 ≥ 1`, jet-degree cap `B`,
derivative cap `1 ≤ M ≤ B` and challenge height `H` gives an extension-field exceptional set of
size at most `retainedSquarefreeCurveSharpOptimizedCharge n (k - 1) ell L A B M H` for
`k ≤ L ≤ A ≤ n`. Outside it, every polynomial of degree `< k` with at least `A` agreements has
exact power agreement. -/
theorem exists_extensionExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderCurveCertificate.{u, u} Dcert A m M B k H domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        retainedSquarefreeCurveSharpOptimizedCharge n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveAgreement_sharpOptimized
      domain values iota _ (cert.map_Q_ne_zero iota) (by omega) (by omega) hLA hAn hell hM
      hMB (cert.jetTotalDegree_map_Q_le iota) (cert.degreeOf_map_Q_le iota)
      (CoeffNatDegreeLE.map_coefficients iota cert.Q cert.challengeDegree_le) hchar
  exact ⟨exceptional, hcard, cert.exactPowerAgreement_of_map_Q iota (by omega) hgood⟩

/-- The certificate bound of
`exists_extensionExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate`
over the base field: the exceptional set lies in the base field, and exact power agreement holds
there. -/
theorem exists_baseExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderCurveCertificate.{u, u} Dcert A m M B k H domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        retainedSquarefreeCurveSharpOptimizedCharge n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate
      domain values iota columns cert hk hkL hLA hAn hell hM hMB hchar
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    uniformExactPowerAgreement_of_extension domain values iota k A extensionExceptional hgood
  exact ⟨exceptional, (show (exceptional.card : ℝ) ≤ extensionExceptional.card by
    exact_mod_cast hcardBase).trans hcard, hgoodBase⟩

end

end ReedSolomon.FirstOrder.Squarefree
