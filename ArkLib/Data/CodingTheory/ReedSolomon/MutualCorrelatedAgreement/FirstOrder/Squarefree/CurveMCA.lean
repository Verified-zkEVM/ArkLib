/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.RetainedTail
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedDerivativeImage
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveTransfer
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine

/-!
# Retained squarefree first-order curve agreement

The regular positive-factor locus and its retained singular tail give one exceptional set for
exact power agreement with a retained squarefree first-order curve. The singular tail is an
order-zero equation, and the ordinary equation bound discharges it in every characteristic. A
finite first-order curve certificate supplies the equation, and exact power agreement descends
from the extension field to the base field. On a line, a symbolic line certificate at the balanced
split gives exact correlated pairs outside a set bounded by the closed line envelope.

## Main statements

* `retainedOrdinaryCurveAgreementCharge` defines the ordinary-tail charge.
* `retainedSquarefreeCurveAgreementCharge` adds the regular derivative-capped charge.
* `exists_exceptional_retainedSquarefreeCurveAgreement_of_singularTail` combines the regular
  locus with a singular tail of any charge into one exceptional set, and
  `exists_exceptional_retainedSquarefreeCurveAgreement_of_tail` is its instance at the
  ordinary-tail charge.
* `hasRetainedOrdinaryCurveAgreementTransfer_singularCurveEquation` discharges the singular tail.
* `exists_exceptional_retainedSquarefreeCurveAgreement` gives the bound without a tail premise.
* `exists_extensionExceptional_retainedSquarefreeCurveAgreement_of_certificate` and
  `exists_baseExceptional_retainedSquarefreeCurveAgreement_of_certificate` apply it to a finite
  first-order curve certificate over the extension and the base field.
* `FirstOrderCurveCertificate.map_Q_specialization_eq_zero` states that the extended certificate
  equation vanishes at every sufficiently agreeing polynomial, and
  `FirstOrderCurveCertificate.exactPowerAgreement_of_map_Q` turns recovery for its roots into
  recovery for every sufficiently agreeing polynomial.
* `retainedSquarefreeLineAgreementEnvelope` is the closed line envelope, and
  `retainedSquarefreeCurveAgreementCharge_balancedSplit_le` bounds the line charge at the
  balanced split by it.
* `exists_extensionExceptional_retainedSquarefreeLineAgreement_of_certificate` and
  `exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate` give exact correlated
  pairs from a symbolic line certificate over the extension and the base field.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- The ordinary-tail charge for a retained curve with `ell + 1` received words. -/
def retainedOrdinaryCurveAgreementCharge (theta : ℝ) (n D ell B M H : ℕ) : ℝ :=
  let b := B * (2 * M + 1)
  let h := H * (2 * M + 1)
  ((2 * b - 1) * h : ℕ) +
    theta * (h + ell * b + 4 * D * b * h : ℕ) +
      (ell * ((n - D - 1) * b) : ℕ)

/-- The retained squarefree charge before an optimized exceptional-set comparison. -/
def retainedSquarefreeCurveAgreementCharge
    (theta : ℝ) (n D ell L A B M H : ℕ) : ℝ :=
  retainedOrdinaryCurveAgreementCharge theta n D ell B M H +
    (regularPowerBatchedDerivativeCappedBoundTwo n ell (D + 1) (D + 1)
      L A B M H (regularTaylorExponent D) : ℝ)

/-- The order-zero interface used for the retained singular tail. -/
def HasRetainedOrdinaryCurveAgreementTransfer
    {F E : Type*} [Field F] [Field E] [instF : DecidableEq F]
    [instE : DecidableEq E]
    {n D ell A B M H : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E) (Q₀ : DifferentialPolynomial E[X] 0) : Prop :=
  ∃ exceptional : Finset E,
    (exceptional.card : ℝ) ≤
      retainedOrdinaryCurveAgreementCharge
        (HiddenDerivative.agreementIncidenceRatio n D A) n D ell B M H ∧
    ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
      differentialSpecialization (challengeSpecialization Q₀ z) P = 0 →
      HasExactPowerAgreement domain values iota (D + 1) z P

open Classical in
/-- A retained squarefree equation whose singular tail has an exceptional set of size at most
`tailBound` has one exceptional set of size at most `tailBound` plus the regular
derivative-capped charge. Outside it, every qualifying root of the equation has exact power
agreement. -/
theorem exists_exceptional_retainedSquarefreeCurveAgreement_of_singularTail
    {F E : Type*} [Field F] [Field E] [instF : DecidableEq F]
    [instE : DecidableEq E]
    [IsAlgClosed E] {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hellH : 0 < ell + H)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : CoeffNatDegreeLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) (tailBound : ℝ)
    (htail : ∃ exceptional : Finset E, (exceptional.card : ℝ) ≤ tailBound ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization (singularCurveEquation Q) z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ tailBound +
        (regularPowerBatchedDerivativeCappedBoundTwo n ell (D + 1) (D + 1)
          L A B M H (regularTaylorExponent D) : ℝ) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
    HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hdecF : instF = (fun a b : F ↦ Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  have hdecE : instE = (fun a b : E ↦ Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  have hcharE : ringChar E = 0 ∨ D < ringChar E := by
    have heq : ringChar E = ringChar F := by
      let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
      exact ringChar.eq E (ringChar F)
    rw [heq]
    rcases hchar with hzero | hpos
    · exact Or.inl hzero
    · exact Or.inr ((Nat.le_max_left D M).trans_lt hpos)
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiD
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_ringChar_eq_zero_or_lt
      (by simpa using hcharE) (by omega) (by omega)
  have htaylor :
      TaylorExponentSufficient 1 (D + 1) (regularTaylorExponent D) := by
    simpa only [regularTaylorExponent] using taylorExponentSufficient_firstOrder_tight D
  have hpositiveJet : jetTotalDegree (positiveCurveEquation Q) ≤ B :=
    (positiveCurveEquation_jetTotalDegree_le Q).trans hjet
  have hpositiveHeight : CoeffNatDegreeLE (positiveCurveEquation Q) H :=
    positiveCurveEquation_coeffNatDegreeLE_of_input Q hheight
  have hpositiveDerivative : (positiveCurveEquation Q).degreeOf (some 1) ≤ M :=
    (positiveCurveEquation_yOneDegree_le Q).trans hderiv
  obtain ⟨regularExceptional, hregularCard, hregular⟩ :
      ∃ regularExceptional : Finset E,
        (regularExceptional.card : ℚ) ≤
          regularPowerBatchedDerivativeCappedBoundTwo n ell (D + 1) (D + 1)
            L A B M H (regularTaylorExponent D) ∧
        ∀ z ∉ regularExceptional, ∀ P : E[X], P.degree < D + 1 →
          A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          differentialSpecialization
            (challengeSpecialization (positiveCurveEquation Q) z) P = 0 →
          differentialSpecialization
            (separant (challengeSpecialization (positiveCurveEquation Q) z)
              (Fin.last 1)) P ≠ 0 →
          HasExactPowerAgreement domain values iota (D + 1) z P := by
    by_cases hDone : D = 1
    · subst D
      have hresult :=
        exists_exceptional_regularPowerBatchedAgreement_identityPair
          domain values iota (positiveCurveEquation Q) L A B M H hDL hLA hAn
          (by omega) hpositiveJet hpositiveHeight
      rw [← hdecF, ← hdecE] at hresult
      convert hresult using 1
      norm_num [regularTaylorExponent]
    · have hresult :=
        exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent
          domain values iota (positiveCurveEquation Q)
          (D + 1) (D + 1) L A B M H (regularTaylorExponent D)
          htaylor (by unfold regularTaylorExponent; omega) (by omega) le_rfl hDL
          hLA hAn hellH (by omega) hM hMB hpositiveJet hpositiveHeight
          hpositiveDerivative hbin
      rw [← hdecF, ← hdecE] at hresult
      simpa only [Nat.cast_add, Nat.cast_one] using hresult
  obtain ⟨tailExceptional, htailCard, htailGood⟩ := htail
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : (exceptional.card : ℝ) ≤
        (tailExceptional.card : ℝ) + regularExceptional.card := by
      exact_mod_cast Finset.card_union_le tailExceptional regularExceptional
    apply hcard.trans
    exact add_le_add htailCard (by exact_mod_cast hregularCard)
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
      · apply htailGood z hzTail P hdegree hagree
        exact singularCurveEquation_routes_nonregular Q hQ z P hroot
          (Or.inr hseparant)
      · apply hregular z hzRegular P hdegree hagree hpositive
        simpa only [challengeSpecialization, separant, MvPolynomial.pderiv_map,
          show (Fin.last 1 : Fin 2) = 1 by decide] using hseparant
    · apply htailGood z hzTail P hdegree hagree
      exact singularCurveEquation_routes_nonregular Q hQ z P hroot
        (Or.inl hpositive)

/-- A retained squarefree equation and its singular-tail transfer give one exceptional set.
Outside it, every qualifying root of the equation has exact power agreement. -/
theorem exists_exceptional_retainedSquarefreeCurveAgreement_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    [IsAlgClosed E] {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hellH : 0 < ell + H)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : CoeffNatDegreeLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasRetainedOrdinaryCurveAgreementTransfer (D := D) (A := A)
      (B := B) (M := M) (H := H) domain values iota (singularCurveEquation Q)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveAgreementCharge
        (HiddenDerivative.agreementIncidenceRatio n D A) n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
    HasExactPowerAgreement domain values iota (D + 1) z P :=
  exists_exceptional_retainedSquarefreeCurveAgreement_of_singularTail domain values iota Q hQ
    hD hDL hLA hAn hellH hM hMB hjet hderiv hheight hchar _ htail

open Classical in
/-- For `1 ≤ D`, `0 < ell`, `D + 1 ≤ A ≤ n` and `1 ≤ M ≤ B`, the singular tail of a first-order
equation with jet degree at most `B`, `Y₁` degree at most `M` and coefficient height at most `H`
satisfies the retained ordinary transfer, provided `M` is below a positive characteristic. -/
theorem hasRetainedOrdinaryCurveAgreementTransfer_singularCurveEquation
    {F E : Type*} [Field F] [Field E] [instF : DecidableEq F] [instE : DecidableEq E]
    [IsAlgClosed E] {n D ell A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1)
    (hD : 1 ≤ D) (hell : 0 < ell) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : CoeffNatDegreeLE Q H)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    HasRetainedOrdinaryCurveAgreementTransfer (D := D) (A := A) (B := B) (M := M) (H := H)
      domain values iota (singularCurveEquation Q) := by
  have hdecF : instF = (fun a b : F ↦ Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  have hdecE : instE = (fun a b : E ↦ Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  subst hdecF hdecE
  let b := B * (2 * M + 1)
  let h := H * (2 * M + 1)
  have hcharE : ringChar E = 0 ∨ M < ringChar E := by
    have heq : ringChar E = ringChar F := by
      let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
      exact ringChar.eq E (ringChar F)
    rwa [heq]
  have hb : 1 ≤ b := Nat.mul_pos (hM.trans hMB) (by omega)
  have htailDegree : (singularCurveEquation Q).degreeOf (some 0) ≤ b :=
    (singularCurveEquation_degree_le Q hjet hderiv hMB).trans
      ((ordinaryDegreeEnvelope_le B M).trans (by dsimp only [b]; nlinarith))
  have htailHeight : CoeffNatDegreeLE (singularCurveEquation Q) h :=
    (singularCurveEquation_coeffNatDegreeLE Q hheight hM hderiv).mono
      ((resultantChallengeEnvelope_le H M).trans (by dsimp only [h]; nlinarith))
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryPowerEquation
    domain values iota (singularCurveEquation Q) D h b A
    (singularCurveEquation_ne_zero Q hderiv hcharE) hD hell hb hDA hAn htailHeight htailDegree
  refine ⟨exceptional, ?_, fun z hz P hdegree hagree hroot ↦ hgood z hz P hdegree hroot hagree⟩
  have hcardReal : (exceptional.card : ℝ) ≤ (ordinaryCurveFactorRaw
      (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell b h : ℚ) := by
    exact_mod_cast hcard
  apply hcardReal.trans_eq
  simp [ordinaryCurveFactorRaw, retainedOrdinaryCurveAgreementCharge,
    HiddenDerivative.agreementIncidenceRatio, b, h]

/-- A retained squarefree first-order equation gives one exceptional set bounded by
`retainedSquarefreeCurveAgreementCharge`. Outside it, every qualifying root of the equation has
exact power agreement, in every characteristic above `max D M`. -/
theorem exists_exceptional_retainedSquarefreeCurveAgreement
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    [IsAlgClosed E] {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) (hell : 0 < ell)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : CoeffNatDegreeLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveAgreementCharge
        (HiddenDerivative.agreementIncidenceRatio n D A) n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P :=
  exists_exceptional_retainedSquarefreeCurveAgreement_of_tail domain values iota Q hQ
    hD hDL hLA hAn (by omega) hM hMB hjet hderiv hheight hchar
    (hasRetainedOrdinaryCurveAgreementTransfer_singularCurveEquation domain values iota Q hD hell
      (by omega) hAn hM hMB hjet hderiv hheight
      (hchar.imp_right fun hmax ↦ (Nat.le_max_right D M).trans_lt hmax))

universe u

/-- After extending its coefficients along `iota` and specializing the challenge at `z`, the
equation of a first-order curve certificate for a power-batched word vanishes at every
polynomial of degree `< k` with at least `A` agreements with the batched word at `z`. -/
theorem _root_.ReedSolomon.HiddenDerivative.FirstOrderCurveCertificate.map_Q_specialization_eq_zero
    {F E : Type u} [Field F] [Field E] [DecidableEq E] {n N Dcert A m M B k H ell : ℕ}
    {domain : Fin n ↪ F} {values : Fin (ell + 1) → Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderCurveCertificate.{u, u} Dcert A m M B k H domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (iota : F →+* E) (z : E) (P : E[X]) (hdegree : P.degree < k)
    (hagree : A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
      (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card) :
    differentialSpecialization
      (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom iota) cert.Q) z) P =
        0 := by
  have hroot := (cert.specialization_sound iota z).2 _ P hdegree hagree fun i hi ↦ by
    rw [eval₂_powerBatchedCoordinate_eq_powerBatchedWord]
    exact (Finset.mem_filter.mp hi).2
  have hEval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
    ext <;> simp
  rw [challengeSpecialization, hEval, MvPolynomial.eval_map_coefficients]
  exact hroot

/-- For `1 ≤ k`, if outside `exceptional` every root of degree `< (k - 1) + 1` of the extended
certificate equation with at least `A` agreements has exact power agreement, then outside
`exceptional` every polynomial of degree `< k` with at least `A` agreements has exact power
agreement. -/
theorem _root_.ReedSolomon.HiddenDerivative.FirstOrderCurveCertificate.exactPowerAgreement_of_map_Q
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    {n N Dcert A m M B k H ell : ℕ}
    {domain : Fin n ↪ F} {values : Fin (ell + 1) → Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderCurveCertificate.{u, u} Dcert A m M B k H domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (iota : F →+* E) (hk : 1 ≤ k) {exceptional : Finset E}
    (hgood : ∀ z ∉ exceptional, ∀ P : E[X], P.degree < (k - 1 : ℕ) + 1 →
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
      differentialSpecialization
        (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom iota) cert.Q) z) P =
          0 →
      HasExactPowerAgreement domain values iota (k - 1 + 1) z P) :
    ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
      HasExactPowerAgreement domain values iota k z P := by
  intro z hz P hdegree hagree
  have hk1 : k - 1 + 1 = k := by omega
  have hdegree' : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
    rwa [show ((k - 1 : ℕ) : WithBot ℕ) + 1 = k by exact_mod_cast hk1]
  have hout := hgood z hz P hdegree' hagree
    (cert.map_Q_specialization_eq_zero iota z P hdegree hagree)
  rwa [hk1] at hout

/-- A finite first-order curve certificate with recovery degree `k - 1 ≥ 1`, jet-degree cap `B`,
derivative cap `1 ≤ M ≤ B` and challenge height `H` gives an extension-field exceptional set
bounded by `retainedSquarefreeCurveAgreementCharge`. Outside it, every polynomial of degree
`< k` with at least `A` agreements has exact power agreement. -/
theorem exists_extensionExceptional_retainedSquarefreeCurveAgreement_of_certificate
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
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveAgreementCharge
        (HiddenDerivative.agreementIncidenceRatio n (k - 1) A) n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_retainedSquarefreeCurveAgreement
    domain values iota _ (cert.map_Q_ne_zero iota) (by omega) (by omega) hLA hAn hell hM hMB
    (cert.jetTotalDegree_map_Q_le iota) (cert.degreeOf_map_Q_le iota)
    (CoeffNatDegreeLE.map_coefficients iota cert.Q cert.challengeDegree_le) hchar
  exact ⟨exceptional, hcard, cert.exactPowerAgreement_of_map_Q iota (by omega) hgood⟩

/-- The certificate bound of
`exists_extensionExceptional_retainedSquarefreeCurveAgreement_of_certificate` over the base
field: the exceptional set lies in the base field, and exact power agreement holds there. -/
theorem exists_baseExceptional_retainedSquarefreeCurveAgreement_of_certificate
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
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveAgreementCharge
        (HiddenDerivative.agreementIncidenceRatio n (k - 1) A) n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeCurveAgreement_of_certificate
      domain values iota columns cert hk hkL hLA hAn hell hM hMB hchar
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    uniformExactPowerAgreement_of_extension domain values iota k A extensionExceptional hgood
  exact ⟨exceptional, (show (exceptional.card : ℝ) ≤ extensionExceptional.card by
    exact_mod_cast hcardBase).trans hcard, hgoodBase⟩

/-- The closed finite-length envelope of the retained squarefree charge on a line, with the
ordinary tail kept separate: the tail charge plus `(48 D² H + 16 D) λ² B M` plus
`8 D (n - D - 1) λ B M`. -/
def retainedSquarefreeLineAgreementEnvelope (lambda : ℝ) (n D B M H : ℕ) : ℝ :=
  retainedOrdinaryCurveAgreementCharge lambda n D 1 B M H +
    (48 * D ^ 2 * H + 16 * D : ℕ) * lambda ^ 2 * B * M +
      (8 * D * (n - D - 1) : ℕ) * lambda * B * M

/-- At the balanced split, the retained squarefree charge on a line is at most
`retainedSquarefreeLineAgreementEnvelope`. -/
theorem retainedSquarefreeCurveAgreementCharge_balancedSplit_le
    {n D A B M H : ℕ} (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B) :
    retainedSquarefreeCurveAgreementCharge (HiddenDerivative.agreementIncidenceRatio n D A)
        n D 1 (balancedSplit D A) A B M H ≤
      retainedSquarefreeLineAgreementEnvelope
        (HiddenDerivative.agreementIncidenceRatio n D A) n D B M H := by
  let theta := HiddenDerivative.agreementIncidenceRatio n D A
  let L := balancedSplit D A
  let τ := regularTaylorExponent D
  have htheta : 0 ≤ theta := zero_le_one.trans (one_le_agreementIncidenceRatio hDA hAn)
  have hretained : retainedCoordinateRatio n A L ≤ 2 * theta :=
    retainedCoordinateRatio_balancedSplit_le hDA (by omega)
  have hfixed : fixedCoordinateRatio n D L ≤ 2 * theta :=
    fixedCoordinateRatio_balancedSplit_le n D A
  have htail : ((n - L : ℕ) : ℝ) ≤ (n - D - 1 : ℕ) := by
    exact_mod_cast sub_balancedSplit_le hDA
  have hmoment : M * (2 * B - M) ≤ 2 * B * M := by
    calc
      M * (2 * B - M) ≤ M * (2 * B) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * B * M := by ring
  have hjoint : (firstOrderCurveJointStageOne (D + 1) 1 H B M τ : ℝ) ≤
      (24 * D ^ 2 * H + 8 * D : ℕ) * B * M := by
    have hjointNat := (firstOrderCurveJointStageOne_regularTaylorExponent_le
      (h := H) hD hM hMB).trans (Nat.mul_le_mul_left (12 * D ^ 2 * H + 4 * D) hmoment)
    calc
      (firstOrderCurveJointStageOne (D + 1) 1 H B M τ : ℝ) ≤
          ((12 * D ^ 2 * H + 4 * D) * (2 * B * M) : ℕ) := by exact_mod_cast hjointNat
      _ = (24 * D ^ 2 * H + 8 * D : ℕ) * B * M := by push_cast; ring
  have hfiberNat : firstOrderCurveFiberStageOne (D + 1) B M τ ≤ 4 * D * B * M :=
    calc
      _ ≤ 2 * D * M * (2 * B - M) :=
        firstOrderCurveFiberStageOne_regularTaylorExponent_le hD hM hMB
      _ = 2 * D * (M * (2 * B - M)) := by ring
      _ ≤ 2 * D * (2 * B * M) := Nat.mul_le_mul_left _ hmoment
      _ = 4 * D * B * M := by ring
  have hfiber : (firstOrderCurveFiberStageOne (D + 1) B M τ : ℝ) ≤ (4 * D * B * M : ℕ) := by
    exact_mod_cast hfiberNat
  have hregularEq := regularPowerBatchedDerivativeCappedBoundTwo_eq_hybridCurveStage
    (n := n) (D := D) (A := A) (L := L) (h := H) (mu := B) (e := M) (j := 0) (ell := 1)
    (lt_balancedSplit hDA) (balancedSplit_le hDA.le) hAn
  simp only [Nat.sub_zero, Nat.cast_one, one_mul] at hregularEq
  have hregular :
      (regularPowerBatchedDerivativeCappedBoundTwo n 1 (D + 1) (D + 1) L A B M H τ : ℝ) ≤
        (48 * D ^ 2 * H + 16 * D : ℕ) * theta ^ 2 * B * M +
          (8 * D * (n - D - 1) : ℕ) * theta * B * M := by
    rw [hregularEq]
    have hretained0 : 0 ≤ retainedCoordinateRatio n A L := by
      unfold retainedCoordinateRatio
      positivity
    have hfixed0 : 0 ≤ fixedCoordinateRatio n D L := by
      unfold fixedCoordinateRatio
      positivity
    calc
      retainedCoordinateRatio n A L * theta * firstOrderCurveJointStageOne (D + 1) 1 H B M τ +
            (n - L : ℕ) * fixedCoordinateRatio n D L *
              firstOrderCurveFiberStageOne (D + 1) B M τ ≤
          (2 * theta) * theta * ((24 * D ^ 2 * H + 8 * D : ℕ) * B * M) +
            (n - D - 1 : ℕ) * (2 * theta) * (4 * D * B * M : ℕ) := by
        gcongr
      _ = (48 * D ^ 2 * H + 16 * D : ℕ) * theta ^ 2 * B * M +
          (8 * D * (n - D - 1) : ℕ) * theta * B * M := by
        push_cast
        ring
  unfold retainedSquarefreeCurveAgreementCharge retainedSquarefreeLineAgreementEnvelope
  linarith

/-- A symbolic line certificate for `f` and `g` is a curve certificate for the degree-one
power-batched coordinates of `![f, g]`. -/
private theorem nonempty_lineCurveCertificate
    {F : Type u} [Field F] {n N Dcert A m M B k H : ℕ}
    {domain : Fin n ↪ F} {f g : Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A m M B k H domain f g columns) :
    Nonempty (FirstOrderCurveCertificate.{u, u} Dcert A m M B k H domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ ![f, g] t i) columns) := by
  have hword : (fun i ↦ receivedLine (f i) (g i)) =
      fun i ↦ powerBatchedCoordinate fun t ↦ ![f, g] t i := by
    funext i
    rw [receivedLine, powerBatchedCoordinate, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Polynomial.monomial_zero_left, Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial]
  exact ⟨hword ▸ cert.toCurve⟩

/-- A finite first-order symbolic certificate for the line through `f` and `g`, with recovery
degree `k - 1 ≥ 1`, `k ≤ A ≤ n`, jet-degree cap `B` and derivative cap `1 ≤ M ≤ B`, gives an
extension-field exceptional set bounded by `retainedSquarefreeLineAgreementEnvelope`. Outside it,
every polynomial of degree `< k` with at least `A` agreements with `f + z g` has an exact
correlated pair. -/
theorem exists_extensionExceptional_retainedSquarefreeLineAgreement_of_certificate
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n N Dcert A m M B k H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A m M B k H domain f g columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeLineAgreementEnvelope
        (HiddenDerivative.agreementIncidenceRatio n (k - 1) A) n (k - 1) B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota k z P := by
  obtain ⟨curveCert⟩ := nonempty_lineCurveCertificate cert
  have hkL : k ≤ balancedSplit (k - 1) A :=
    Nat.le_of_pred_lt (lt_balancedSplit (D := k - 1) (by omega))
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeCurveAgreement_of_certificate
      (ell := 1) domain ![f, g] iota columns curveCert hk hkL (balancedSplit_le (by omega)) hAn
      one_pos hM hMB hchar
  refine ⟨exceptional, hcard.trans (retainedSquarefreeCurveAgreementCharge_balancedSplit_le
    (by omega) (by omega) hAn hM hMB), fun z hz P hdegree hagree ↦ ?_⟩
  exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g] iota z P
    (hgood z hz P hdegree (by rwa [powerBatchedWord_pair_eq]))

/-- The line bound of
`exists_extensionExceptional_retainedSquarefreeLineAgreement_of_certificate` over the base field:
the exceptional set lies in the base field, and the exact correlated pair is found there. -/
theorem exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {n N Dcert A m M B k H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A m M B k H domain f g columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ retainedSquarefreeLineAgreementEnvelope
        (HiddenDerivative.agreementIncidenceRatio n (k - 1) A) n (k - 1) B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨curveCert⟩ := nonempty_lineCurveCertificate cert
  have hkL : k ≤ balancedSplit (k - 1) A :=
    Nat.le_of_pred_lt (lt_balancedSplit (D := k - 1) (by omega))
  have hword (z : F) : powerBatchedWord ![f, g] z = fun i ↦ f i + z * g i :=
    powerBatchedWord_pair_eq f g (RingHom.id F) z
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_retainedSquarefreeCurveAgreement_of_certificate
      (ell := 1) domain ![f, g] iota columns curveCert hk hkL (balancedSplit_le (by omega)) hAn
      one_pos hM hMB hchar
  refine ⟨exceptional, hcard.trans (retainedSquarefreeCurveAgreementCharge_balancedSplit_le
    (by omega) (by omega) hAn hM hMB), fun z hz P hdegree hagree ↦ ?_⟩
  exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
    (hgood z hz P hdegree (by rwa [hword]))

end

end ReedSolomon.FirstOrder.Squarefree
