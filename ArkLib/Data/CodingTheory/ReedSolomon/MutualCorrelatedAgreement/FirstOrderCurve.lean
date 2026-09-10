/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveFinite
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveTransfer
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.DerivativeImage
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpGeneralEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Certificate
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.CoefficientExtension
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.JetPrefix
/-!
# Finite first-order polynomial-curve correlated agreement

Power batching turns a tuple of received Reed--Solomon words into one polynomial-valued
received word.  This module applies the finite first-order interpolation construction to that
word, follows its actual separant chain, and counts every regular stage with the sharp
order-zero or order-one polynomial-curve theorem.  The cap-sensitive chain sum retains the
first-derivative cap `M`, rather than charging every stage as first order.

## Reading the statement

The parameters `D`, `m`, `M`, `mu`, and `h` describe the finite interpolation support and
challenge-height budget.  The strict comparison between `firstOrderCurveShiftedRowSlotBound`
and `firstOrderCurveShiftedHeightSlotCount` is the executable interpolation test.  The
thresholds satisfy `k <= L <= A <= n`; `K` is the Taylor
cutoff used by the regular-stage geometry.  The characteristic hypothesis simultaneously
constructs the separant chain and makes its order-zero and order-one binomial pivots nonzero.

The extension-field theorem chooses one finite exceptional set before the challenge and
candidate polynomial. Its base-field corollary descends that same bound to the original
field. Outside it, every degree-`< k` candidate agreeing in at
least `A` positions is exactly the power batching of a tuple of degree-`< k` base-field
polynomials, with equality of the complete agreement sets.  No protocol composition or
challenge-distribution claim is made here.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon

open HiddenDerivative
open HiddenDerivative.SymbolicJetPrefix
open HiddenDerivative.SymbolicReceivedCurve
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.SymbolicWeightedSupportInterpolation
open HiddenDerivative.SymbolicSeparantChain

noncomputable section

universe u

/-- An executable finite first-order curve certificate gives an extension-field exceptional set
with the exact cap-sensitive polynomial-curve envelope.  This is the pre-descent form: challenge
values and candidate polynomials live in the algebraically closed target, while the recovered
tuple still has coefficients in the source field. -/
theorem exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
    {F E : Type u} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {D A m M mu k h n N K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderCurveCertificate.{u, u} (F := F) D A m M mu k h domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) mu < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A mu M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  let curveWord : Fin n → F[X] := fun i ↦
    powerBatchedCoordinate fun t ↦ values t i
  have hcharWeight : ringChar F = 0 ∨ mu < ringChar F :=
    hchar.imp_right fun hpos ↦ (Nat.le_max_right (K - 1) mu).trans_lt hpos
  obtain ⟨stages, terminal, chain⟩ := cert.exists_separant_chain hcharWeight
  have hcharK : ringChar F = 0 ∨ K ≤ ringChar F := by
    apply hchar.imp_right
    intro hpos
    have hpred : K - 1 < ringChar F :=
      (Nat.le_max_left (K - 1) mu).trans_lt hpos
    omega
  have hbin : ∀ r ≤ 1, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hi
    exact binomial_pivots_of_characteristic hcharK r i hri hi
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
    · obtain ⟨pres, _, hpresWeight, _, hpresHeight⟩ :=
        exists_stage_presentation chain cert.challengeDegree_le (stageQ, 0) hstage
      have hstageWeightPos : 0 < jetWeight stageQ := by
        have hhighest := (chain.stage_contract (stageQ, 0) hstage).2.1
        exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1.trans_le
          (jetDegree_le_jetWeight stageQ 0)
      have hweightExtended :
          jetWeight (extendSymbolicCoefficients iota pres.equation) ≤ jetWeight stageQ :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans_eq hpresWeight
      have hbinExtended : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin 0 (by omega) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      obtain ⟨exceptional, hcard, hgoodStage⟩ :=
        exists_exceptional_regularSymbolicCurveMCA_sharp_recognized_of_exponent
          domain values iota (extendSymbolicCoefficients iota pres.equation) K k L A
          (jetWeight stageQ) h τ hτ0 hτpos (by omega) hkK hk hkL hLA hAn hcurve
          hstageWeightPos hweightExtended
          (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hpresHeight)
          hbinExtended
      refine ⟨exceptional, ?_, ?_⟩
      · apply hcard.trans_eq
        simp [firstOrderCurveStageCharge, firstOrderStageCharge, curveStageZero,
          regularSymbolicCurveMCASharpBound, sourceCurveInitialMixedDegree,
          sourceCurveCutChallengeDegree, sourceCurveCutJetDegree, firstOrderCurveJointRatio]
        ring
      · intro z hz indices P hdegree hagree hvalues hsolution hseparant
        apply hgoodStage z hz P hdegree
        · apply hagree.trans
          apply Finset.card_le_card
          intro i hi
          simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← SymbolicReceivedCurve.eval₂_powerBatchedCoordinate_eq_powerBatchedWord
            values iota z i]
          exact hvalues i hi
        · change differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) P = 0
          rw [specialize_extendSymbolicCoefficients, pres.specialization]
          exact hsolution
        · change differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) (Fin.last 0)) P ≠ 0
          rw [specialize_extendSymbolicCoefficients]
          intro hzero
          apply hseparant
          exact (pres.separant_specialization (Polynomial.eval₂RingHom iota z) P).symm.trans
            hzero
    · obtain ⟨pres, _, hpresWeight, _, hpresHeight⟩ :=
        exists_stage_presentation chain cert.challengeDegree_le (stageQ, 1) hstage
      have hstageWeightPos : 0 < jetWeight stageQ := by
        have hhighest := (chain.stage_contract (stageQ, 1) hstage).2.1
        exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1.trans_le
          (jetDegree_le_jetWeight stageQ 1)
      have hweightExtended :
          jetWeight (extendSymbolicCoefficients iota pres.equation) ≤ jetWeight stageQ :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans_eq hpresWeight
      have hstageDerivativePos : 0 < jetDegree stageQ 1 := by
        have hhighest := (chain.stage_contract (stageQ, 1) hstage).2.1
        exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
      have hstageDerivativeWeight : jetDegree stageQ 1 ≤ jetWeight stageQ :=
        jetDegree_le_jetWeight stageQ 1
      have hderivExtended :
          (extendSymbolicCoefficients iota pres.equation).degreeOf (some 1) ≤
            jetDegree stageQ 1 := by
        have hmap :
            (extendSymbolicCoefficients iota pres.equation).degreeOf
                (some (Fin.last (1 : Fin 2).val)) ≤
              pres.equation.degreeOf (some (Fin.last (1 : Fin 2).val)) := by
          apply MvPolynomial.degreeOf_le_iff.mpr
          intro mon hmon
          exact MvPolynomial.monomial_le_degreeOf _
            (MvPolynomial.support_map_subset (Polynomial.mapRingHom iota)
              pres.equation hmon)
        have ht := hmap.trans_eq pres.top_jetDegree
        have hone : (Fin.last (1 : Fin 2).val : Fin 2) = 1 := by decide
        rw [hone] at ht
        exact ht
      have hbinExtended : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin 1 (by omega) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      obtain ⟨exceptional, hcard, hgoodStage⟩ :=
        exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent
          domain values iota
          (extendSymbolicCoefficients iota pres.equation) K k L A
          (jetWeight stageQ) (jetDegree stageQ 1) h τ hτ1 hτpos hK hkK hk hkL hLA
          hAn hcurve hstageWeightPos hstageDerivativePos hstageDerivativeWeight hweightExtended
          (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hpresHeight)
          hderivExtended
          hbinExtended
      refine ⟨exceptional, ?_, ?_⟩
      · apply hcard.trans_eq
        simp [firstOrderCurveStageCharge, firstOrderStageCharge, curveStageOne,
          regularSymbolicCurveMCADerivativeBoundTwo,
          sourceCurveCutChallengeDegree, sourceCurveCutJetDegree,
          sourceCurveCutDerivativeDegree, firstOrderTaylorTotalCap,
          firstOrderTaylorDerivativeCap, firstOrderCurveJointStageOne,
          firstOrderCurveFiberStageOne, AffineHilbert.mixedDerivativeImageDegree,
          AffineHilbert.fixedFiberDerivativeImageDegree,
          firstOrderCurveJointRatio, firstOrderCurveFiberRatio,
          firstOrderCurveDirectRatio]
        ring
      · intro z hz indices P hdegree hagree hvalues hsolution hseparant
        apply hgoodStage z hz P hdegree
        · apply hagree.trans
          apply Finset.card_le_card
          intro i hi
          simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← SymbolicReceivedCurve.eval₂_powerBatchedCoordinate_eq_powerBatchedWord
            values iota z i]
          exact hvalues i hi
        · change differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) P = 0
          rw [specialize_extendSymbolicCoefficients, pres.specialization]
          exact hsolution
        · change differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) (Fin.last 1)) P ≠ 0
          rw [specialize_extendSymbolicCoefficients]
          intro hzero
          apply hseparant
          exact (pres.separant_specialization (Polynomial.eval₂RingHom iota z) P).symm.trans
            hzero
  obtain ⟨exceptional, hcard, hgood⟩ :=
    cert.exists_exceptional_of_regular_stage_bounds_of_exponent
      chain iota K L ell τ (by omega) hk hkL hLA hAn
      (fun z P ↦ HasExactPowerAgreement domain values iota k z P) hregular
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hdegree hagree
  let indices := polynomialAgreementSet (mappedDomain domain iota)
    (powerBatchedWord (fun t i ↦ iota (values t i)) z) P
  apply hgood z hz indices P hdegree hagree
  intro i hi
  exact (Finset.mem_filter.mp hi).2.trans
    (SymbolicReceivedCurve.eval₂_powerBatchedCoordinate_eq_powerBatchedWord
      values iota z i).symm

/-- The finite shifted-height construction supplies the certificate to the generic consumer. -/
theorem exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
    {F E : Type u} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {D A m M mu k h n K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M mu n ell h <
      firstOrderCurveShiftedHeightSlotCount D A m M mu ell h)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) mu < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A mu M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    ell hD hbudget hkD domain (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i) hheight
  exact exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
    domain values iota _ cert hK hkK hk hkL hLA hAn hcurve τ hτ0 hτ1 hτpos hchar

/-- Descending the preceding extension-field exceptional set gives a base-field exceptional set
with the same exact cap-sensitive envelope. -/
theorem exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {D A m M mu k h n N K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderCurveCertificate.{u, u} (F := F) D A m M mu k h domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) mu < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A mu M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
      domain values iota columns cert hK hkK hk hkL hLA hAn hcurve
        τ hτ0 hτ1 hτpos hchar
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend domain values iota k A extensionExceptional hgood
  refine ⟨exceptional, ?_, hgoodBase⟩
  exact (show (exceptional.card : ℚ) ≤ (extensionExceptional.card : ℚ) by
    exact_mod_cast hcardBase).trans hcard

/-- The finite shifted-height constructor supplies the base-field consumer. -/
theorem exists_baseExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {D A m M mu k h n K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M mu n ell h <
      firstOrderCurveShiftedHeightSlotCount D A m M mu ell h)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (τ : ℕ) (hτ0 : TaylorExponentSufficient 0 K τ)
    (hτ1 : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hchar : ringChar F = 0 ∨ max (K - 1) mu < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A mu M ell h
        (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    ell hD hbudget hkD domain (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i) hheight
  exact exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent
    domain values iota _ cert hK hkK hk hkL hLA hAn hcurve τ hτ0 hτ1 hτpos hchar

/-- The extension-field form at the tight common exponent `2K - 3`. -/
theorem exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_tight
    {F E : Type u} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {D A m M mu k h n K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M mu n ell h <
      firstOrderCurveShiftedHeightSlotCount D A m M mu ell h)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (hchar : ringChar F = 0 ∨ max (K - 1) mu < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A mu M ell h
        (τ := 2 * K - 3) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  exact exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
    domain values iota hD hbudget hkD hheight hK hkK hk hkL hLA hAn hcurve
      (2 * K - 3) (taylorExponentSufficient_two_mul_sub_three 0 (by omega))
        (taylorExponentSufficient_two_mul_sub_three 1 (by omega)) (by omega) hchar

/-- The maintained base-field first-order curve consumer uses the tight common exponent `2K - 3`
and the direct order-one incidence ratio. The characteristic-zero branch is included in `hchar`. -/
theorem exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {D A m M mu k h n K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M mu n ell h <
      firstOrderCurveShiftedHeightSlotCount D A m M mu ell h)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (hchar : ringChar F = 0 ∨ max (K - 1) mu < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A mu M ell h
        (τ := 2 * K - 3) (η := firstOrderCurveDirectRatio n k A) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  exact exists_baseExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
    domain values iota hD hbudget hkD hheight hK hkK hk hkL hLA hAn hcurve
      (2 * K - 3) (taylorExponentSufficient_two_mul_sub_three 0 (by omega))
        (taylorExponentSufficient_two_mul_sub_three 1 (by omega)) (by omega) hchar

end

end ReedSolomon
