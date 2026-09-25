/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedDerivativeImage
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedSharpRegularAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation
public import ArkLib.Data.Polynomial.Differential.RationalTaylor
public import ArkLib.Data.Polynomial.Differential.SeparantChain
public import ArkLib.Data.Polynomial.Differential.WitnessCount
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# First-order power-batched curve agreement

A finite first-order curve certificate gives one finite exceptional set outside which every
sufficiently agreeing low-degree polynomial has exact power-batched agreement. The bound charges
each separant stage at its actual order and derivative degree. A shifted-height surplus constructs
the certificate, and uniform exact agreement descends the extension-field result to the base
field.

## Main statements

* `exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent` gives the extension
  field bound from a finite first-order curve certificate.
* `exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent` descends that bound.
* The height-slot theorems construct the certificate from a strict shifted-height surplus.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential
open PolynomialDifferential.SeparantChain

namespace ReedSolomon

open HiddenDerivative

noncomputable section

universe u

/-- A finite first-order curve certificate gives an extension-field exceptional set bounded by
the cap-sensitive polynomial-curve envelope. -/
theorem exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
    {F E : Type u} [Field F] [Field E]
    [decEqE : DecidableEq E] [IsAlgClosed E]
    {D A m M μ k h n N K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderCurveCertificate.{u, u} (F := F) D A m M μ k h domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A μ M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        let decEqF : DecidableEq F := Classical.decEq F
        @HasExactPowerAgreement F E (Fin n) _ _ _ decEqF decEqE ell domain values iota k z P := by
  classical
  let curveWord : Fin n → F[X] := fun i ↦
    powerBatchedCoordinate fun t ↦ values t i
  have hnonzero : cert.Q ≠ 0 := by
    intro hzero
    have h := (cert.specialization_sound iota 0).1
    apply h
    rw [hzero, map_zero]
  have hweight : jetTotalDegree cert.Q ≤ μ := by
    rw [jetTotalDegree_le_iff]
    exact cert.totalJetDegree_le
  have hcharWeight : ringChar F = 0 ∨ μ < ringChar F :=
    hchar.imp_right fun hpos ↦ (Nat.le_max_right (K - 1) μ).trans_lt hpos
  have hcharWeight' : ringChar F[X] = 0 ∨ μ < ringChar F[X] := by
    rw [← Algebra.ringChar_eq F F[X]]
    exact hcharWeight
  obtain ⟨stages, terminal, chain⟩ :=
    exists_separantChain_of_ringChar hnonzero (hcharWeight'.imp_right hweight.trans_lt)
  have hcharK : ringChar F = 0 ∨ K ≤ ringChar F := by
    apply hchar.imp_right
    intro hpos
    have hpred : K - 1 < ringChar F :=
      (Nat.le_max_left (K - 1) μ).trans_lt hpos
    omega
  have hcharChoose : ringChar F = 0 ∨ K - 1 < ringChar F :=
    hcharK.imp_right (by omega)
  have hbin : ∀ r ≤ 1, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hi
    have hchoose := natCast_choose_ne_zero_of_ringChar (D := K - 1) (s := r)
      hcharChoose (i - r) (by omega) (by omega)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hri)] using hchoose
  have hregular : ∀ stage ∈ stages, ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
          firstOrderCurveStageCharge n K k L A ell h stage
            (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (iota (domain i)) = (curveWord i).eval₂ iota z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1)
              stage.2) P ≠ 0 →
          HasExactPowerAgreement domain values iota k z P := by
    rintro ⟨stageQ, stageOrder⟩ hstage
    fin_cases stageOrder
    · obtain ⟨pres, _, hpresWeight, _⟩ :=
        chain.exists_jetPrefixPresentation_of_mem (stage := (stageQ, 0)) hstage
      have hstageWeightPos : 0 < jetTotalDegree stageQ := by
        have hhighest := chain.highestActiveJet_eq_of_mem hstage
        exact ((isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1).trans_le
          (jetDegree_le_total stageQ 0)
      let equation : DifferentialPolynomial E[X] 0 :=
        MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation
      have hweightExtended : jetTotalDegree equation ≤ jetTotalDegree stageQ := by
        exact (jetTotalDegree_map_le (Polynomial.mapRingHom iota) pres.equation).trans_eq
          hpresWeight
      have hcoeff : MvPolynomial.CoeffNatDegreeLE pres.equation h := by
        intro u
        exact pres.natDegree_coeff_equation_le
          (chain.natDegree_coeff_le_of_mem cert.challengeDegree_le hstage) u
      have hheight : MvPolynomial.CoeffNatDegreeLE equation h := by
        exact MvPolynomial.CoeffNatDegreeLE.map_coefficients iota pres.equation hcoeff
      have hbinExtended : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin 0 (by omega) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      obtain ⟨exceptional, hcard, hgoodStage⟩ :=
        exists_exceptional_regularPowerBatchedAgreement_sharp_of_exponent
          domain values iota equation K k L A (jetTotalDegree stageQ) h τ hτ0 hτpos
          (by omega) hkK hkL hLA hAn hcurve hstageWeightPos hweightExtended hheight
          hbinExtended
      refine ⟨exceptional, ?_, ?_⟩
      · apply hcard.trans_eq
        simp [firstOrderCurveStageCharge, firstOrderStageCharge, orderZeroCurveStageCharge,
          regularPowerBatchedAgreementSharpBound, regularPowerBatchedInitialMixedDegree,
          regularPowerBatchedCutChallengeDegree, regularPowerBatchedCutJetDegree,
          firstOrderTaylorTotalCap, firstOrderCurveJointRatio, firstOrderCurveIncidenceRatio,
          dimensionSensitiveIncidenceProduct]
        ring_nf
      · intro z hz indices P hdegree hagree hvalues hsolution hseparant
        have hgoodClassical :
            @HasExactPowerAgreement F E (Fin n) _ _ _ (Classical.decEq F)
              (Classical.decEq E) ell domain values iota k z P := by
          apply hgoodStage z hz P hdegree
          · apply hagree.trans
            apply Finset.card_le_card
            intro i hi
            simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← eval₂_powerBatchedCoordinate_eq_powerBatchedWord values iota z i]
            exact hvalues i hi
          · have hspecialize (Q : DifferentialPolynomial F[X] 0) :=
              MvPolynomial.eval_map_coefficients iota z Q
            let mappedPres := pres.map (Polynomial.eval₂RingHom iota z)
            change differentialSpecialization
              (MvPolynomial.map (Polynomial.evalRingHom z)
                (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation)) P = 0
            rw [hspecialize pres.equation]
            change differentialSpecialization mappedPres.equation P = 0
            rw [mappedPres.differentialSpecialization_equation P]
            exact hsolution
          · have hspecialize (Q : DifferentialPolynomial F[X] 0) :=
              MvPolynomial.eval_map_coefficients iota z Q
            let mappedPres := pres.map (Polynomial.eval₂RingHom iota z)
            change differentialSpecialization
              (separant
                (MvPolynomial.map (Polynomial.evalRingHom z)
                  (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation))
                (Fin.last 0)) P ≠ 0
            rw [← map_separant, ← map_separant,
              hspecialize (separant pres.equation (Fin.last 0))]
            rw [map_separant]
            change differentialSpecialization
              (separant mappedPres.equation (Fin.last 0)) P ≠ 0
            have hpresSep :
                differentialSpecialization
                    (separant mappedPres.equation (Fin.last 0)) P =
                  differentialSpecialization
                    (separant (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stageQ)
                      (0 : Fin 2)) P := by
              simpa using mappedPres.differentialSpecialization_separant_equation P
            rw [hpresSep]
            exact hseparant
        have hdecEqE : decEqE = Classical.decEq E := Subsingleton.elim _ _
        rw [← hdecEqE] at hgoodClassical
        exact hgoodClassical
    · have hstage' : (stageQ, (1 : Fin 2)) ∈ stages := by
        simpa using hstage
      obtain ⟨pres, _, hpresWeight, _⟩ :=
        chain.exists_jetPrefixPresentation_of_mem (stage := (stageQ, 1)) hstage'
      have hstageWeightPos : 0 < jetTotalDegree stageQ := by
        have hhighest := chain.highestActiveJet_eq_of_mem hstage
        exact ((isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1).trans_le
          (jetDegree_le_total stageQ 1)
      have hweightExtended :
          jetTotalDegree (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation) ≤
            jetTotalDegree stageQ :=
        (jetTotalDegree_map_le (Polynomial.mapRingHom iota) pres.equation).trans_eq hpresWeight
      have hstageDerivativePos : 0 < jetDegree stageQ 1 := by
        have hhighest := chain.highestActiveJet_eq_of_mem hstage
        exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
      have hstageDerivativeWeight : jetDegree stageQ 1 ≤ jetTotalDegree stageQ :=
        jetDegree_le_total stageQ 1
      have hderivExtended :
          (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation).degreeOf (some 1) ≤
            jetDegree stageQ 1 := by
        change jetDegree (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation) 1 ≤
          jetDegree stageQ 1
        have hmap := jetDegree_map_le (Polynomial.mapRingHom iota) pres.equation
          (1 : Fin 2)
        have hpresDegree : jetDegree pres.equation (1 : Fin 2) = jetDegree stageQ 1 := by
          simpa using pres.jetDegree_equation_last
        exact hmap.trans_eq hpresDegree
      have hbinExtended : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin 1 (by omega) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      have hheight : MvPolynomial.CoeffNatDegreeLE
          (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation) h := by
        apply MvPolynomial.CoeffNatDegreeLE.map_coefficients iota pres.equation
        intro u
        exact pres.natDegree_coeff_equation_le
          (chain.natDegree_coeff_le_of_mem cert.challengeDegree_le hstage) u
      obtain ⟨exceptional, hcard, hgoodStage⟩ :=
        exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent
          domain values iota (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation)
          K k L A (jetTotalDegree stageQ) (jetDegree stageQ 1) h τ hτ1 hτpos hK hkK hkL
          hLA hAn hcurve hstageWeightPos hstageDerivativePos hstageDerivativeWeight
          hweightExtended hheight hderivExtended hbinExtended
      refine ⟨exceptional, ?_, ?_⟩
      · apply hcard.trans_eq
        simp [firstOrderCurveStageCharge, firstOrderStageCharge, orderOneCurveStageCharge,
          regularPowerBatchedDerivativeCappedBoundTwo, firstOrderTaylorTotalCap,
          firstOrderTaylorDerivativeCap, firstOrderCurveJointStageOne,
          firstOrderCurveFiberStageOne, firstOrderCurveJointRatio,
          firstOrderCurveFiberRatio, firstOrderCurveIncidenceRatio,
          firstOrderCurveDirectRatio]
        ring_nf
      · intro z hz indices P hdegree hagree hvalues hsolution hseparant
        have hgoodClassical :
            @HasExactPowerAgreement F E (Fin n) _ _ _ (Classical.decEq F)
              (Classical.decEq E) ell domain values iota k z P := by
          apply hgoodStage z hz P hdegree
          · apply hagree.trans
            apply Finset.card_le_card
            intro i hi
            simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← eval₂_powerBatchedCoordinate_eq_powerBatchedWord values iota z i]
            exact hvalues i hi
          · have hspecialize (Q : DifferentialPolynomial F[X] 1) :=
              MvPolynomial.eval_map_coefficients iota z Q
            let mappedPres := pres.map (Polynomial.eval₂RingHom iota z)
            change differentialSpecialization
              (MvPolynomial.map (Polynomial.evalRingHom z)
                (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation)) P = 0
            rw [hspecialize pres.equation]
            change differentialSpecialization mappedPres.equation P = 0
            rw [mappedPres.differentialSpecialization_equation P]
            exact hsolution
          · have hspecialize (Q : DifferentialPolynomial F[X] 1) :=
              MvPolynomial.eval_map_coefficients iota z Q
            let mappedPres := pres.map (Polynomial.eval₂RingHom iota z)
            change differentialSpecialization
              (separant
                (MvPolynomial.map (Polynomial.evalRingHom z)
                  (MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation))
                (Fin.last 1)) P ≠ 0
            rw [← map_separant, ← map_separant,
              hspecialize (separant pres.equation (Fin.last 1))]
            rw [map_separant]
            change differentialSpecialization
              (separant mappedPres.equation (Fin.last 1)) P ≠ 0
            have hpresSep :
                differentialSpecialization
                    (separant mappedPres.equation (Fin.last 1)) P =
                  differentialSpecialization
                    (separant (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stageQ)
                      (1 : Fin 2)) P := by
              simpa using mappedPres.differentialSpecialization_separant_equation P
            rw [hpresSep]
            exact hseparant
        have hdecEqE : decEqE = Classical.decEq E := Subsingleton.elim _ _
        rw [← hdecEqE] at hgoodClassical
        exact hgoodClassical
  have hη : 1 ≤ firstOrderCurveDirectRatio n k A := by
    simpa [firstOrderCurveDirectRatio, firstOrderCurveIncidenceRatio] using
      one_le_incidenceFactor (T := k) (b := 1) hAn one_pos
  obtain ⟨exceptional, hcard, hgood⟩ :=
    cert.exists_exceptional_of_regular_stage_bounds_of_factors
      chain iota K L ell τ (firstOrderCurveDirectRatio n k A) hη (by omega) hLA hAn
      (fun z P ↦ HasExactPowerAgreement domain values iota k z P) hregular
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hdegree hagree
  let indices := polynomialAgreementSet
    (domain.trans ⟨iota, iota.injective⟩)
    (powerBatchedWord (fun t i ↦ iota (values t i)) z) P
  apply hgood z hz indices P hdegree hagree
  intro i hi
  exact (Finset.mem_filter.mp hi).2.trans
    (eval₂_powerBatchedCoordinate_eq_powerBatchedWord values iota z i).symm

/-- A strict shifted-height surplus constructs the extension-field first-order curve bound. -/
theorem exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
    {F E : Type u} [Field F] [Field E] [decEqE : DecidableEq E] [IsAlgClosed E]
    {D A m M μ k h n K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n ell h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ell h)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A μ M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        let decEqF : DecidableEq F := Classical.decEq F
        @HasExactPowerAgreement F E (Fin n) _ _ _ decEqF decEqE ell domain values iota k z P := by
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    ell hD hbudget hkD domain (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i) hheight
  exact exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
    domain values iota _ cert hK hkK hkL hLA hAn hcurve τ hτ0 hτ1 hτpos hchar

/-- The extension-field bound descends to the base field with the same exceptional-set envelope.
-/
theorem exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent
    {F E : Type u} [Field F] [Field E] [decEqF : DecidableEq F] [IsAlgClosed E]
    {D A m M μ k h n N K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderCurveCertificate.{u, u} (F := F) D A m M μ k h domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A μ M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
      domain values iota columns cert hK hkK hkL hLA hAn hcurve
        τ hτ0 hτ1 hτpos hchar
  have hdecEqF : decEqF = Classical.decEq F := Subsingleton.elim _ _
  rw [← hdecEqF] at hgood
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    uniformExactPowerAgreement_of_extension domain values iota k A extensionExceptional hgood
  refine ⟨exceptional, ?_, hgoodBase⟩
  exact (show (exceptional.card : ℚ) ≤ (extensionExceptional.card : ℚ) by
    exact_mod_cast hcardBase).trans hcard

/-- A strict shifted-height surplus gives the base-field first-order curve bound. -/
theorem exists_baseExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {D A m M μ k h n K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n ell h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ell h)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A μ M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    ell hD hbudget hkD domain (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i) hheight
  exact exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent
    domain values iota _ cert hK hkK hkL hLA hAn hcurve τ hτ0 hτ1 hτpos hchar

end

end ReedSolomon
