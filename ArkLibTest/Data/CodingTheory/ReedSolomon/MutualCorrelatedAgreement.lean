/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullDimension
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusAdmissibility
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusRetainedFamily
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleCounting
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode
import Mathlib.Analysis.Complex.Polynomial.Basic
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentAgreement
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedGeometricTransfer
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
import ArkLibTest.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ComponentDimension
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Extension

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedGraphCounting
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedIncidence
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedExceptionalChallenges
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedRegularEquation
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedSharpRegularAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedFrobeniusFamily
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.UniformMca
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for Reed–Solomon mutual correlated agreement -/

open Polynomial Finset ReedSolomon PolynomialDifferential ReedSolomon.HiddenDerivative

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
private noncomputable def agreementEquation : DifferentialPolynomial (ZMod 2)[X] 0 :=
  MvPolynomial.X (some 0) - MvPolynomial.C (Polynomial.X)

noncomputable section

local instance : DecidableEq E₄ := Classical.decEq E₄

/-- A nonzero affine line descends from the degree-two extension. -/
example : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    (RingHom.id (ZMod 2)) 2 1 (1 + X) :=
  HasExactCorrelatedPair.descend pointDomain _ _ (algebraMap (ZMod 2) E₄) 2 1 (1 + X)
    ⟨(1, X), by norm_num, by norm_num, by simp [correlatedPairSpecialization], by
      ext i
      fin_cases i
      simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]⟩

/-- The equation `Y = X` descends from `E₄`: its constant solution at `z = 1` is correlated. -/
example : HasExactCorrelatedPair pointDomain (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1)
    (RingHom.id (ZMod 2)) 2 1 (C 1) := by
  obtain ⟨exceptional, hcard, hdescend⟩ :=
    exists_exceptional_equation_correlatedAgreement_descend pointDomain (fun _ ↦ (0 : ZMod 2))
      (fun _ ↦ 1) (algebraMap (ZMod 2) E₄) agreementEquation 2 1 ∅ fun z _ P _ _ hroot ↦ by
        obtain rfl : P = C z := sub_eq_zero.mp (by
          simpa [agreementEquation, challengeSpecialization, differentialSpecialization,
            differentialSpecializationHom] using hroot)
        refine ⟨(0, 1), by rw [degree_zero]; exact WithBot.bot_lt_coe 2, by norm_num,
          by simp [correlatedPairSpecialization], ?_⟩
        ext i; fin_cases i; simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]
  exact hdescend 1 (by simp_all) (C 1) (by simp) (by simp [pointDomain, polynomialAgreementSet])
    (by simp [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom])

end

/-- Degree-one power agreement on one coordinate supplies the exact line interface. -/
private theorem singletonLineExactBound : LineExactAgreementBound pointDomain 1 1 0 := by
  apply lineExactAgreementBound_of_powerAgreement_one pointDomain 0
  intro w
  refine ⟨∅, by simp, ?_⟩
  intro z _ Q hQ hclose
  have hset : polynomialAgreementSet pointDomain (powerBatchedWord w z) Q = univ :=
    Finset.eq_univ_of_card _
      (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hclose))
  have hword : powerBatchedWord w z 0 = w 0 0 + z * w 1 0 := by
    simp [powerBatchedWord, Fin.sum_univ_two]
  have hval : Q.eval (pointDomain 0) = w 0 0 + z * w 1 0 := by
    calc
      Q.eval (pointDomain 0) = powerBatchedWord w z 0 :=
        (mem_polynomialAgreementSet ..).mp (hset ▸ Finset.mem_univ (0 : Fin 1))
      _ = w 0 0 + z * w 1 0 := hword
  have hcoeff : Q.coeff 0 = w 0 0 + z * w 1 0 := by
    simpa [pointDomain] using (coeff_zero_eq_eval_zero Q).trans hval
  have hconst : Q = Polynomial.C (w 0 0 + z * w 1 0) := by
    rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hQ), hcoeff]
  apply (hasExactPowerAgreement_id_iff pointDomain w 1 z Q).mpr
  refine ⟨![Polynomial.C (w 0 0), Polynomial.C (w 1 0)], ?_, ?_, ?_⟩
  · intro t
    fin_cases t <;> exact (degree_C_le).trans_lt (by norm_num)
  · simpa [powerBatchedPolynomial, Fin.sum_univ_two, Polynomial.smul_eq_C_mul] using hconst
  · rw [hset]
    ext i
    fin_cases i
    simp [commonCurveAgreementSet, pointDomain]
private def affineValues : Fin 2 → Fin 1 → ZMod 2 := ![fun _ ↦ 1, fun _ ↦ 0]

example := exists_affine_exceptionalSet_full_agreement_of_exactLine pointDomain 0
  singletonLineExactBound 0 (by norm_num [pointDomain]) (by norm_num) affineValues

private def fullDomain : Fin 2 ↪ ℚ where
  toFun i := ((i : ℕ) : ℚ)
  inj' _i _j h := Fin.ext (Nat.cast_injective (R := ℚ) h)

/-- The graph-line recognizer accepts the computed candidate `1 + 2X` at challenge `1`. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 2 ∧ G₀.degree < 2 ∧
    (∀ i ∈ (Finset.univ : Finset (Fin 2)),
      F₀.eval (fullDomain i) = ![1, 2] i ∧ G₀.eval (fullDomain i) = ![0, 1] i) ∧
    C 1 + C 2 * X = F₀ + C 1 * G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hsample, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample fullDomain ![1, 2] ![0, 1] univ (card_univ.trans rfl)
  refine ⟨F₀, G₀, hF₀, hG₀, hsample, ?_⟩
  refine (hrecognize (RingHom.id ℚ) 1 (C 1 + C 2 * X) (by compute_degree!) fun i _ ↦ ?_).trans
    (by simp)
  fin_cases i <;> norm_num [fullDomain]
  exacts [rfl, show (1 + 2 * 1 : ℚ) = 3 by norm_num]

/-- The exceptional bound is attained when the graph agrees at only one coordinate. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧ 0 ∈ exceptional := by
  obtain ⟨exceptional, hcard, hagreement⟩ :=
    exists_exceptional_graphLine_challenges fullDomain ![0, 0] ![0, 1]
      (0 : ℚ[X]) 0 (RingHom.id ℚ)
  have hcommon : commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 = {0} := by
    ext i; fin_cases i <;> simp [commonPolynomialAgreementSet, fullDomain]
  refine ⟨exceptional, by simpa [hcommon, Fintype.card_fin] using hcard,
    by_contra fun hz ↦ ?_⟩
  have hone : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by
    rw [← hcommon, ← hagreement 0 hz]; simp [polynomialAgreementSet, fullDomain]
  simp at hone

private noncomputable def tupleOne : Fin 2 → ℚ[X] := ![1, 0]
private noncomputable def tupleChallenge : Fin 2 → ℚ[X] := ![0, 1]
private theorem tuples_ne : tupleOne ≠ tupleChallenge := fun h ↦ by
  simpa [tupleOne, tupleChallenge] using congrFun h 0

example :
    {z : ℚ | powerBatchedPolynomial (fun t ↦ (tupleOne t).map (RingHom.id ℚ)) z =
      powerBatchedPolynomial (fun t ↦ (tupleChallenge t).map (RingHom.id ℚ)) z}.Finite :=
  finite_polynomialTuple_collisions (RingHom.id ℚ) tuples_ne

example : ∃ z : ℚ, z ≠ 1 ∧ z ≠ 0 ∧
    powerBatchedPolynomial (fun t ↦ (tupleOne t).map (RingHom.id ℚ)) z ≠
      powerBatchedPolynomial (fun t ↦ (tupleChallenge t).map (RingHom.id ℚ)) z := by
  classical
  obtain ⟨z, hz, hinj, hroot⟩ := exists_polynomialTuple_specialization_injective_avoiding_roots
    (RingHom.id ℚ) {tupleOne, tupleChallenge} {1} {X} (by simp [X_ne_zero])
  refine ⟨z, by simpa using hz, by simpa using hroot X (by simp), fun heq ↦ ?_⟩
  exact tuples_ne (hinj (by simp) (by simp) heq)

open MvPolynomial Polynomial PolynomialDifferential

namespace ReedSolomon.GraphLineComponentTest

noncomputable section

private def domain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, by intro i j _; exact Subsingleton.elim _ _⟩

private theorem domain_zero : domain (0 : Fin 1) = 0 := rfl

private def componentWord : Fin 1 → ℚ := fun _ ↦ 0

private abbrev componentEquation {E : Type*} [CommRing E] :
    DifferentialPolynomial E[X] 0 :=
  (MvPolynomial.X (some (0 : Fin 1)) : DifferentialPolynomial E[X] 0) -
    (MvPolynomial.X none : DifferentialPolynomial E[X] 0) *
      MvPolynomial.X (some (0 : Fin 1))

private abbrev componentCoordinateEquation {E : Type*} [CommRing E] :
    DifferentialPolynomial E[X] 0 := MvPolynomial.X (some (0 : Fin 1))

private abbrev componentVariable {E : Type*} [CommSemiring E] :
    MvPolynomial (Option (Fin 1)) E := X (some (0 : Fin 1))

private def componentIdeal {E : Type*} [CommSemiring E] :
    Ideal (MvPolynomial (Option (Fin 1)) E) := Ideal.span {componentVariable}

private abbrev ComponentField := ℂ

private theorem componentIdeal_isPrime : (componentIdeal (E := ComponentField)).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime

private theorem componentIdeal_degree_pos :
    0 < (affineHilbertPolynomial (componentIdeal (E := ComponentField))).natDegree := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (f := componentVariable (E := ComponentField)) (X_ne_zero _) componentIdeal_isPrime.ne_top
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at h
  unfold componentIdeal; omega

private theorem componentIdeal_one_notMem :
    (1 : MvPolynomial (Option (Fin 1)) ComponentField) ∉ componentIdeal (E := ComponentField) :=
  (Ideal.ne_top_iff_one _).mp componentIdeal_isPrime.ne_top

private theorem component_separant_notMem :
    jointInitialJetSeparant (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ∉ componentIdeal := by
  simpa [jointInitialJetSeparant, componentEquation, initialJetSeparant,
    separant, Fin.last] using componentIdeal_one_notMem

private theorem component_generator_mem :
    componentVariable (E := ComponentField) ∈ componentIdeal :=
  Ideal.subset_span (by simp)

private theorem component_initialEquation_eq_variable :
    jointInitialJetEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) = componentVariable := by
  rw [jointInitialJetEquation, show initialJetEquation (Polynomial.C (0 : ComponentField))
    componentEquation = MvPolynomial.X 0 by simp [initialJetEquation, componentEquation],
    optionEquivRight_symm_X]

private theorem component_initialEquation_mem :
    jointInitialJetEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ∈ componentIdeal :=
  component_initialEquation_eq_variable ▸ component_generator_mem

private theorem component_initialEquation_ne_zero :
    jointInitialJetEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ≠ 0 :=
  component_initialEquation_eq_variable ▸ X_ne_zero _

private theorem component_commonNumerator_one :
    commonTaylorNumeratorOver ComponentField (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) 2 1 =
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (Polynomial ComponentField)) := by
  have hcoeff :
      ((optionEquivLeft (Polynomial ComponentField) (Fin 1)
        (universalTaylorResidual 1 (Polynomial.C (0 : ComponentField))
          (componentEquation (E := ComponentField)))).coeff 1) =
        -(MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (Polynomial ComponentField)) := by
    rw [show universalTaylorResidual 1 (Polynomial.C (0 : ComponentField))
        (componentEquation (E := ComponentField)) =
          universalTaylorJet (F := Polynomial ComponentField) 1 0 -
            MvPolynomial.X none * universalTaylorJet (F := Polynomial ComponentField) 1 0 by
      simp [universalTaylorResidual, componentEquation]]
    rw [map_sub, map_mul, optionEquivLeft_X_none,
      optionEquivLeft_universalTaylorJet]
    simp [Polynomial.hasseDeriv]
  have hnumerator :
      rationalTaylorNumeratorOver ComponentField (Polynomial.C (0 : ComponentField))
        (componentEquation (E := ComponentField)) 1 =
          (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (Polynomial ComponentField)) := by
    rw [rationalTaylorNumeratorOver, dite_eq_right (by omega)]
    rw [hcoeff]
    simp [MvPolynomial.clearedSubstitution, rationalTaylorNumeratorOver,
      initialJetSeparant, componentEquation, separant, Fin.last, MvPolynomial.support_X]
  rw [commonTaylorNumeratorOver, hnumerator]
  simp [initialJetSeparant, componentEquation, separant, Fin.last]

private theorem component_commonNumerator_initial :
    commonTaylorNumeratorOver ComponentField (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) 2 0 =
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (Polynomial ComponentField)) := by
  have hlt : 0 < 0 + 1 := by omega
  rw [commonTaylorNumeratorOver, rationalTaylorNumeratorOver, dite_eq_left hlt]
  simp [initialJetSeparant, componentEquation, separant, Fin.last]

private theorem component_highCuts : ∀ l : Fin 2, 1 ≤ l.val →
    jointCommonTaylorNumerator (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 2 l ∈ componentIdeal := by
  intro l hl
  obtain rfl : l = 1 := Fin.ext (by omega)
  change (optionEquivRight ComponentField (Fin 1)).symm
      (commonTaylorNumeratorOver ComponentField (Polynomial.C (0 : ComponentField))
        (componentEquation (E := ComponentField)) 2 1) ∈ componentIdeal
  rw [component_commonNumerator_one]
  simpa [componentVariable] using component_generator_mem

private theorem component_cut_eq :
    taylorAgreementEquationOver (F := ComponentField) (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) 2 (0 : ComponentField[X]) 0 (τ := 2) =
        initialJetEquation (Polynomial.C (0 : ComponentField))
          (componentEquation (E := ComponentField)) := by
  rw [taylorAgreementEquationOver, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one]
  rw [component_commonNumerator_initial]
  simp [initialJetEquation, initialJetSeparant, separant, componentEquation]

private theorem component_agreementCuts : ∀ i ∈ Finset.univ,
    jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 2 2
      (Polynomial.C ((algebraMap ℚ ComponentField) (domain i)))
      (Polynomial.C ((algebraMap ℚ ComponentField) (componentWord i)) +
        Polynomial.X * Polynomial.C ((algebraMap ℚ ComponentField) (componentWord i))) ∈
        componentIdeal := by
  intro i _
  obtain rfl : i = 0 := Subsingleton.elim _ _
  change (optionEquivRight ComponentField (Fin 1)).symm
    (taylorAgreementEquationOver (F := ComponentField) _ _ 2 _ _ (τ := 2)) ∈ componentIdeal
  rw [show Polynomial.C ((algebraMap ℚ ComponentField) (domain 0)) = 0 by simp [domain_zero],
    show Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) + Polynomial.X *
      Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) = 0 by simp [componentWord],
    component_cut_eq]
  exact component_initialEquation_mem

private abbrev firstOrderChartEquation : DifferentialPolynomial ComponentField 1 :=
  MvPolynomial.X (Fin.last 1)

private def firstOrderChartIdeal : Ideal (ChartRing 1 ComponentField) :=
  Ideal.span {(MvPolynomial.X (Fin.last 1) : ChartRing 1 ComponentField)}

private def firstOrderTestPoints : Fin 1 ↪ ComponentField :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
private def firstOrderChartValues : Fin 1 → ComponentField := fun _ ↦ 0

private abbrev firstOrderChartCut (i : Fin 1) : ChartRing 1 ComponentField :=
  taylorAgreementEquation (0 : ComponentField) firstOrderChartEquation 2 2
    (firstOrderTestPoints i) (firstOrderChartValues i)

private theorem firstOrderChartIdeal_isPrime : firstOrderChartIdeal.IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime

private theorem firstOrderChartSeparant_notMem :
    initialJetSeparant (0 : ComponentField) firstOrderChartEquation ∉ firstOrderChartIdeal := by
  simpa [firstOrderChartEquation, initialJetSeparant, initialJetEquation, separant] using
    (Ideal.ne_top_iff_one _).mp firstOrderChartIdeal_isPrime.ne_top

private theorem firstOrderChartHigh : ∀ l : Fin 2, 1 ≤ l.val →
    commonTaylorNumerator (0 : ComponentField) firstOrderChartEquation 2 l.val ∈
      firstOrderChartIdeal := by
  intro l hl
  obtain rfl : l = 1 := Fin.ext (by omega)
  simp [commonTaylorNumerator, rationalTaylorNumerator, firstOrderChartEquation,
    initialJetSeparant, separant, firstOrderChartIdeal]

private def firstOrderRegularJet : Fin 2 → ComponentField := fun _ ↦ 0
private def firstOrderRegularJets : Finset (Fin 2 → ComponentField) :=
  {firstOrderRegularJet}
/-- A singleton regular jet satisfies the dimension-sensitive high-cut incidence bound. -/
example : firstOrderRegularJets.Nonempty ∧
    (firstOrderRegularJets.card : ℚ) ≤ (jetTotalDegree firstOrderChartEquation : ℚ) *
      (rationalTaylorCutDegreeBound firstOrderChartEquation 2 : ℚ) ^ 1 *
        dimensionSensitiveIncidenceProduct 1 0 0 1 1 := by
  have hS : ∀ jet ∈ firstOrderRegularJets,
      aeval jet (initialJetEquation (0 : ComponentField) firstOrderChartEquation) = 0 ∧
      aeval jet (initialJetSeparant (0 : ComponentField) firstOrderChartEquation) ≠ 0 ∧
      ∀ l : {l : Fin 2 // 0 ≤ l.val},
        aeval jet (commonTaylorNumerator (0 : ComponentField)
          firstOrderChartEquation 2 l.val) = 0 := by
    intro jet hj
    have hj' : jet = firstOrderRegularJet := Finset.mem_singleton.mp (by
      simpa [firstOrderRegularJets] using hj)
    subst jet
    refine ⟨by simp [firstOrderChartEquation, firstOrderRegularJet, initialJetEquation],
      by simp [firstOrderChartEquation, initialJetSeparant, separant], ?_⟩
    intro l
    have hl : l.val = 0 ∨ l.val = 1 := by omega
    rcases hl with hl | hl <;>
      simp [hl, firstOrderRegularJet, commonTaylorNumerator, rationalTaylorNumerator,
        firstOrderChartEquation, initialJetSeparant, separant]
  have hA : ∀ jet ∈ firstOrderRegularJets, 0 ≤
      {i | aeval jet (taylorAgreementEquation (0 : ComponentField)
        firstOrderChartEquation 2 2 (firstOrderTestPoints i)
          (firstOrderChartValues i)) = 0}.ncard := by intro _ _; omega
  have hbound := finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent
    (center := (0 : ComponentField)) (Q := firstOrderChartEquation)
    (K := 2) (k := 0) (τ := 2) (A := 0) (by intro l; omega) (by omega) (by omega)
    firstOrderTestPoints firstOrderChartValues (by omega) (by omega)
    firstOrderRegularJets hS hA
  exact ⟨by simp [firstOrderRegularJets], hbound⟩

/-- A retained chart prime with one nonempty agreement cut has degree zero. -/
example :
    (affineHilbertPolynomial
      (Ideal.span
        {(MvPolynomial.X (0 : Fin 1) : ChartRing 0 ComponentField)})).natDegree ≤ 0 := by
  have hP : (Ideal.span {(MvPolynomial.X (0 : Fin 1) : ChartRing 0 ComponentField)}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  simpa using chart_prime_affineHilbertPolynomial_natDegree_le_of_agreements_of_exponent
    (center := (0 : ComponentField))
    (Q := (MvPolynomial.X (0 : Fin 1) : DifferentialPolynomial ComponentField 0))
    (K := 1) (k := 1) (c := 1) (τ := 0)
    (by intro l; fin_cases l; decide) (by omega) (by omega) _ hP
    (by simpa [initialJetSeparant, initialJetEquation, separant] using
      (Ideal.ne_top_iff_one _).mp hP.ne_top)
    (by intro l hl; fin_cases l; omega) firstOrderTestPoints firstOrderChartValues fun i ↦ by
      simp [taylorAgreementEquation, commonTaylorNumerator, rationalTaylorNumerator,
        initialJetSeparant, separant, firstOrderTestPoints, firstOrderChartValues]

/-- The two-point evaluation domain `{0, 1}` in `ℚ`. -/
private def pairDomain : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ (i : ℚ), fun i j h ↦ Fin.ext (by simpa using h)⟩

/-- The component contains the agreement cut for the zero pair at every challenge point. -/
private theorem component_zeroCut_mem (alpha : ComponentField) :
    jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 2 2 (Polynomial.C alpha) 0 ∈ componentIdeal := by
  change (optionEquivRight ComponentField (Fin 1)).symm
    (taylorAgreementEquationOver (F := ComponentField) _ _ 2 _ _ (τ := 2)) ∈ componentIdeal
  rw [taylorAgreementEquationOver, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one]
  rw [component_commonNumerator_initial, component_commonNumerator_one]
  simp only [Polynomial.C_0, sub_zero, pow_zero, pow_one, MvPolynomial.C_0, zero_mul, map_one,
    one_mul]
  rw [show (MvPolynomial.X 0 + MvPolynomial.C (Polynomial.C alpha) * MvPolynomial.X 0 :
      MvPolynomial (Fin 1) ComponentField[X]) =
        (1 + MvPolynomial.C (Polynomial.C alpha)) * MvPolynomial.X 0 by ring,
    map_mul, optionEquivRight_symm_X]
  exact Ideal.mul_mem_left _ _ component_generator_mem

/-- A proved zero-pair cut forces the reconstructed polynomials to match the sample. -/
example : (0 : ℚ[X]).eval (domain 0) = 0 ∧ (0 : ℚ[X]).eval (domain 0) = 0 := by
  have hzero (x : Option (Fin 1) → ComponentField)
      (hx : x ∈ zeroLocus ComponentField (componentIdeal (E := ComponentField)))
      (j : Fin 1) : x (some j) = 0 := by
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [componentIdeal, componentVariable, zeroLocus_span] using hx
  exact @commonAgreement_of_jointTaylorAgreementEquation_mem_prime
    ComponentField inferInstance 0 ℚ inferInstance 1 inferInstance
    domain (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ 0) (algebraMap ℚ ComponentField)
    0 componentEquation 2 2 (by intro l; omega) componentIdeal componentIdeal_isPrime
    component_separant_notMem componentIdeal_degree_pos 0 0
    (fun x hx ↦ ⟨x none, funext fun j ↦ by
      cases j with
      | none => simp [affinePairCurve]
      | some j => simp [affinePairCurve, polynomialJet, hzero x hx.1 j]⟩)
    (fun x hx _ ↦ by
      have hjet : (fun j ↦ x (some j)) = polynomialJet (d := 0) 0 (0 : ComponentField[X]) := by
        funext j; simp [polynomialJet, hzero x hx j]
      rw [hjet, rationalTaylorPolynomial_polynomialJet _ _ 0 ?_ ?_
        (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe 2) ?_]
      · simp
      · simp [differentialSpecialization, differentialSpecializationHom]
      · simp [separant, Fin.last, jetEvaluation]
      · intro i _ _; simp)
    0 (by simpa [domain_zero] using component_zeroCut_mem (0 : ComponentField))

/-- Every regular point of a prime component lies on the recognized graph line, and agreement
cuts at two points, one more than the degree bound `k = 1`, give a pair with two common
agreements. -/
example :
    (∃ P₀ P₁ : ℚ[X], ∀ x,
      x ∈ zeroLocus ComponentField (componentIdeal (E := ComponentField)) ∧
      aeval x (jointInitialJetSeparant (r := 0) (0 : ComponentField)
        (componentEquation (E := ComponentField))) ≠ 0 → ∃ z : ComponentField, x = fun i ↦
          (affinePairCurve (r := 0) 0 (P₀.map (algebraMap ℚ ComponentField))
            (P₁.map (algebraMap ℚ ComponentField)) i).eval z) ∧
    ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
      2 ≤ (commonPolynomialAgreementSet pairDomain 0 0 P₀ P₁).card := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  obtain ⟨P₀, P₁, -, -, -, hgraph, -⟩ := exists_graphLine_pair_of_regular_component domain
    componentWord componentWord univ (by simp) (algebraMap ℚ ComponentField) 0
    componentEquation (by omega) 2 (by intro l; omega) componentIdeal component_separant_notMem
    componentIdeal_degree_pos component_initialEquation_mem component_highCuts
    component_agreementCuts
  obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hcommon, -⟩ :=
    exists_graphLine_pair_of_regular_component_agreements
    (k := 1) (L := 2) pairDomain 0 0 univ (by simp) (by omega)
    (algebraMap ℚ ComponentField) 0 componentEquation (by omega) 2 (by intro l; omega)
    componentIdeal component_separant_notMem componentIdeal_degree_pos
    component_initialEquation_mem component_highCuts
    (fun i _ ↦ by simpa using component_zeroCut_mem _)
  exact ⟨⟨P₀, P₁, hgraph⟩, Q₀, Q₁, hQ₀, hQ₁, hcommon⟩

private theorem component_powerBatchedAgreementCuts : ∀ i ∈ Finset.univ,
    jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 2 2
      (Polynomial.C ((algebraMap ℚ ComponentField) (domain i)))
      (powerBatchedCoordinate
        (fun _ : Fin 2 ↦ (algebraMap ℚ ComponentField) (componentWord i))) ∈
        componentIdeal := by
  intro i hi
  have hbatch : powerBatchedCoordinate
      (fun _ : Fin 2 ↦ (algebraMap ℚ ComponentField) (componentWord i)) = 0 := by
    rw [powerBatchedCoordinate_eq_zero_iff]
    funext t
    simp [componentWord]
  rw [hbatch]
  simpa [componentWord] using component_agreementCuts i hi

open Classical in
/-- A polynomial-valued received word with a proved cut gives a concrete source prime bound, and
the component recognizes tuples that match the word at the cut and have a common agreement. -/
example :
    (affineHilbertPolynomial (componentIdeal (E := ComponentField))).natDegree ≤ 1 ∧
      (∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
        ∀ t, (P t).eval (domain 0) = componentWord 0) ∧
      ∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
        1 ≤ (commonCurveAgreementSet domain (fun _ : Fin 2 ↦ componentWord) P).card := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  let α : Fin 1 ↪ ComponentField :=
    ⟨fun i ↦ algebraMap ℚ ComponentField (domain i), fun _ _ _ ↦ Subsingleton.elim _ _⟩
  let f : Fin 1 → ComponentField := fun i ↦ algebraMap ℚ ComponentField (componentWord i)
  have hbound :=
    symbolicSource_prime_affineHilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent
    0 componentEquation 2 1 1 2 (by intro l; omega) (by omega) (by omega) (by omega)
    componentIdeal componentIdeal_isPrime component_separant_notMem component_highCuts α
    (fun i ↦ Polynomial.C (f i) + Polynomial.X * Polynomial.C (f i))
    (fun i ↦ component_agreementCuts i (Finset.mem_univ i))
  obtain ⟨P, hP, -, hgraph, hpoly, -, -⟩ := exists_polynomialGraph_of_primeTaylorComponent
    domain (fun _ : Fin 2 ↦ componentWord) univ (by simp) (algebraMap ℚ ComponentField) 0
    componentEquation (by omega) 2 (by intro l; omega) componentIdeal component_separant_notMem
    componentIdeal_degree_pos component_highCuts component_powerBatchedAgreementCuts
  obtain ⟨R, hR, hcommon, -⟩ := exists_polynomialGraph_of_primeTaylorComponent_agreements
    (L := 1) domain (fun _ : Fin 2 ↦ componentWord) univ (by simp) (by omega)
    (algebraMap ℚ ComponentField) 0 componentEquation (by omega) 2 (by intro l; omega)
    componentIdeal component_separant_notMem componentIdeal_degree_pos component_highCuts
    component_powerBatchedAgreementCuts
  exact ⟨by simpa using hbound, ⟨P, hP,
    commonCurveAgreement_of_jointTaylorAgreementEquation_mem_prime domain _
      (algebraMap ℚ ComponentField) 0 componentEquation 2 2 (by intro l; omega) componentIdeal
      component_separant_notMem componentIdeal_degree_pos P hgraph hpoly 0
      (component_powerBatchedAgreementCuts 0 (by simp))⟩, R, hR, by convert hcommon⟩

noncomputable local instance graphComponentDecidableEq : DecidableEq ℚ := Classical.decEq _

private abbrev componentRegularPoint : Option (Fin 1) → ComponentField := fun _ ↦ 0

private theorem componentRegularPoint_mem : componentRegularPoint ∈
    {x | x ∈ zeroLocus ComponentField (componentIdeal (E := ComponentField)) ∧
      aeval x (jointInitialJetSeparant (0 : ComponentField) componentEquation) ≠ 0} := by
  simp [componentIdeal, componentVariable, zeroLocus_span, jointInitialJetSeparant,
    initialJetSeparant, separant, Fin.last, componentEquation]

local instance : DecidableEq ComponentField := Classical.decEq _
private abbrev badChallengeDomain : Fin 1 ↪ ComponentField :=
  domain.trans ⟨algebraMap ℚ ComponentField, RingHom.injective _⟩
private def badChallengeWords : Fin 2 → Fin 1 → ComponentField := ![fun _ ↦ 0, fun _ ↦ 1]
private abbrev badChallengeEquation : DifferentialPolynomial ComponentField[X] 1 :=
  MvPolynomial.X (some (Fin.last 1)) + MvPolynomial.C (Polynomial.X : ComponentField[X])
private def badChallenges : Finset ComponentField := {0}
private def badChallengeWitness (_ : ComponentField) : ComponentField[X] := 0
private theorem badChallengeEquation_jetDegree : jetTotalDegree badChallengeEquation ≤ 1 := by
  rw [jetTotalDegree_le_iff]; intro u hu
  rcases Finset.mem_union.mp (MvPolynomial.support_add hu) with h | h
  · simp [MvPolynomial.support_X] at h; subst u; simp [totalJetDegree_eq_sum]
  · simp [MvPolynomial.support_C] at h; subst u; simp [totalJetDegree_eq_sum]
private theorem badChallengeEquation_height : CoeffNatDegreeLE badChallengeEquation 1 := by
  apply CoeffNatDegreeLE.add
  · exact fun m ↦ (coeffNatDegreeLE_X _ m).trans (by omega)
  · exact coeffNatDegreeLE_C (by simp)
private theorem badChallengeChartAtZero :
    let Qz := MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField))
      badChallengeEquation
    (badChallengeWitness 0).degree < 0 ∧
      aeval (fun _ : Fin 2 ↦ (0 : ComponentField)) (initialJetEquation 0 Qz) = 0 ∧
      aeval (fun _ : Fin 2 ↦ (0 : ComponentField)) (initialJetSeparant 0 Qz) ≠ 0 ∧
      (∀ l : Fin 2, 0 ≤ l.val → aeval (fun _ : Fin 2 ↦ (0 : ComponentField))
        (commonTaylorNumerator 0 Qz 2 l.val) = 0) ∧
      rationalTaylorPolynomial 0 Qz 2 (fun _ : Fin 2 ↦ 0) = 0 := by
  let Qz := MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField))
    badChallengeEquation
  have hsep : aeval (fun _ : Fin 2 ↦ (0 : ComponentField))
      (initialJetSeparant 0 Qz) ≠ 0 := by simp [Qz, initialJetSeparant, separant, Fin.last]
  have hsolution : differentialSpecialization Qz (0 : ComponentField[X]) = 0 := by
    simp [Qz, differentialSpecialization, differentialSpecializationHom]
  have hseparant : jetEvaluation (separant Qz (Fin.last 1)) 0
      (polynomialJet 0 (0 : ComponentField[X])) ≠ 0 := by
    simp [Qz, separant, jetEvaluation, polynomialJet, Fin.last]
  have hjet : (fun _ : Fin 2 ↦ (0 : ComponentField)) =
      polynomialJet 0 (0 : ComponentField[X]) := by ext j; fin_cases j <;> simp [polynomialJet]
  have hcoeff : ∀ l : Fin 2,
      rationalTaylorCoefficient 0 Qz (fun _ ↦ (0 : ComponentField)) l.val = 0 := by
    intro l
    rw [hjet]
    rw [rationalTaylorCoefficient_eq_solution 0 Qz (0 : ComponentField[X]) hsolution
      hseparant l.val (by intro i hi hil; omega), Polynomial.taylor_coeff]
    simp
  have hpoly := rationalTaylorPolynomial_polynomialJet 0 Qz (0 : ComponentField[X])
    hsolution hseparant (K := 2) (WithBot.bot_lt_coe 2) (by intro i hi hil; omega)
  rw [← hjet] at hpoly
  refine ⟨by simp [badChallengeWitness], ?_, hsep, ?_, ?_⟩
  · simp [initialJetEquation, badChallengeEquation]
  · intro l _
    exact aeval_commonTaylorNumerator_eq_zero 0 Qz (fun _ ↦ 0) 2 hsep (hcoeff l)
  · exact hpoly
private def incidencePoint : Option (Fin 2) → ComponentField := fun j ↦ j.elim 0 ![0, 0]
private def incidencePoints : Finset (Option (Fin 2) → ComponentField) := {incidencePoint}
private theorem incidencePoint_regular :
    aeval incidencePoint (jointInitialJetEquation 0 badChallengeEquation) = 0 ∧
      aeval incidencePoint (jointInitialJetSeparant 0 badChallengeEquation) ≠ 0 ∧
      (∀ l : Fin 2, 0 ≤ l.val →
        aeval incidencePoint (jointCommonTaylorNumerator 0 badChallengeEquation 2 l) = 0) ∧
      incidencePoint ∉ admissibleChartTupleGraphLocus badChallengeDomain
        badChallengeWords (RingHom.id _) 0 badChallengeEquation 2 0 0 2 := by
  let x : Option (Fin 2) → ComponentField := incidencePoint
  have hvector : (![0, 0] : Fin 2 → ComponentField) = fun _ ↦ 0 := by
    ext j; fin_cases j <;> simp
  have hsep := (badChallengeChartAtZero).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [aeval_jointInitialJetEquation]
    simpa [x, incidencePoint, badChallengeEquation, hvector] using
      badChallengeChartAtZero.2.1
  · rw [aeval_jointInitialJetSeparant]
    simpa [x, incidencePoint, badChallengeEquation, hvector] using hsep
  · intro l hl
    rw [aeval_jointCommonTaylorNumerator]
    simpa [x, incidencePoint, badChallengeEquation, hvector] using
      badChallengeChartAtZero.2.2.2.1 l hl
  · rintro ⟨P, hP, -⟩
    have hzero (t : Fin 2) : P t = 0 :=
      Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (hP.degree t))
    have heval := congrArg (Polynomial.eval (1 : ComponentField)) hP.initial
    rw [eval_chartTuplePullback] at heval
    simp [jointInitialJetEquation, initialJetEquation, badChallengeEquation,
      chartTupleJet, powerBatchedJetGraph, powerBatchedCoordinate, polynomialJet,
      hasseJet_apply, hzero] at heval
private theorem badChallengeEquation_regular :
    jointInitialJetEquation 0 badChallengeEquation ≠ 0 := by
  exact jointInitialJetEquation_ne_zero_of_regular (center := (0 : ComponentField))
    (z := (0 : ComponentField)) badChallengeEquation (fun _ ↦ 0)
    badChallengeChartAtZero.2.2.1
private theorem badChallengeExponent : TaylorExponentSufficient 1 2 2 := by intro l; omega
/-- Both sharp incidence bounds apply to a nonempty regular set outside tuple graphs. -/
example : incidencePoints.Nonempty ∧
    ((incidencePoints.card : ℚ) ≤
        regularPowerBatchedInitialMixedDegree 1 1 2 1 1 (τ := 2) *
          (((1 - 0 + 1 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ)) *
            dimensionSensitiveIncidenceProduct 1 0 0 1 1) ∧
    ((incidencePoints.card : ℚ) ≤
        regularPowerBatchedInitialMixedDegree 1 1 2 1 1 (τ := 2) *
          (((1 - 0 + 1 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ)) *
            dimensionSensitiveIncidenceProduct 1 0 0 1 1) := by
  classical
  have hS : ∀ y ∈ incidencePoints,
      aeval y (jointInitialJetEquation 0 badChallengeEquation) = 0 ∧
      aeval y (jointInitialJetSeparant 0 badChallengeEquation) ≠ 0 ∧
      (∀ l : Fin 2, 0 ≤ l.val →
        aeval y (jointCommonTaylorNumerator 0 badChallengeEquation 2 l) = 0) ∧
      y ∉ admissibleChartTupleGraphLocus badChallengeDomain badChallengeWords
        (RingHom.id _) 0 badChallengeEquation 2 0 0 2 := by
    intro y hy
    obtain rfl : y = incidencePoint := Finset.mem_singleton.mp hy
    exact incidencePoint_regular
  have hA : ∀ y ∈ incidencePoints, 0 ≤
      ({i : Fin 1 | aeval y (jointTaylorAgreementEquation 0 badChallengeEquation 2 2
        (Polynomial.C (badChallengeDomain i))
      (powerBatchedCoordinate (fun t ↦ badChallengeWords t i))) = 0} :
        Set (Fin 1)).ncard := by intro y hy; omega
  have hsharpBound :=
    finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_terminal_recognition
      badChallengeDomain badChallengeWords (RingHom.id _) 0 badChallengeEquation
      2 0 0 0 1 1 2 badChallengeExponent (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
      badChallengeEquation_jetDegree badChallengeEquation_height (by
        intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
        exact principalOpen_subset_admissibleChartTupleGraphLocus
          badChallengeDomain badChallengeWords (RingHom.id _) 0 badChallengeEquation
          2 0 0 2 (by omega) (by omega) badChallengeExponent J hJ hsJ hdJ hgJ hhighJ hcutsJ)
      incidencePoints hS hA
  have hinternalBound :=
    finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_exponent
      badChallengeDomain badChallengeWords (RingHom.id _) 0 badChallengeEquation
      2 0 0 0 1 1 2 badChallengeExponent (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
      badChallengeEquation_jetDegree badChallengeEquation_height incidencePoints hS hA
  have _ :=
    finite_powerBatched_regular_points_off_admissible_graphs_card_le_firstOrder_of_exponent
      (domain := badChallengeDomain) (w := badChallengeWords) (iota := RingHom.id _)
      (center := 0) (Q := badChallengeEquation) (K := 2) (k := 0) (L := 0) (A := 0)
      (v := 1) (h := 1) (τ := 2) badChallengeExponent
      (by simp [regularPowerBatchedCutChallengeDegree])
      (by omega) (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
      badChallengeEquation_jetDegree badChallengeEquation_height incidencePoints hS hA
  exact ⟨by simp [incidencePoints], hsharpBound, hinternalBound⟩
/-- A sparse sample cut on the regular prime component determines its Frobenius graph. -/
example :
    (∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
      (∀ i ∈ (Finset.univ : Finset (Fin 1)), ∀ t,
        (P t).eval (domain i) = componentWord i) ∧
      aeval (frobeniusPowerGraphMap (center := (0 : ComponentField)) 1
        (fun t ↦ (P t).map (algebraMap ℚ ComponentField)))
        (jointInitialJetSeparant (r := 0) (0 : ComponentField)
          (componentCoordinateEquation (E := ComponentField))) ≠ 0) ∧
    (∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
      (0 : ComponentField) =
        (frobeniusPowerInitialGraph (center := (0 : ComponentField)) 1
          (fun t ↦ (P t).map (algebraMap ℚ ComponentField)) 0).eval 0) := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  have hsep := componentIdeal_one_notMem
  have hτ : TaylorExponentSufficient 0 1 0 := by intro l; fin_cases l; omega
  obtain ⟨P, hdegree, hsample, _, _, hseparant⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_prime_sample (k := 1) (K := 1) (ℓ := 1)
      domain (fun _ : Fin 2 ↦ componentWord) univ (by simp) (algebraMap ℚ ComponentField)
      1 0 (fun _ ↦ 0) (by intro i _; fin_cases i; simp [domain_zero]) 0
      componentCoordinateEquation (by omega) (by norm_num) 0 hτ componentIdeal
      (by simpa [jointInitialJetSeparant, initialJetSeparant, separant,
        Fin.last, componentCoordinateEquation] using hsep) componentIdeal_degree_pos
      (by intro l hl; simp at hl)
      (by intro i _; fin_cases i; simpa [componentWord, jointTaylorAgreementEquation,
        taylorAgreementEquationOver, commonTaylorNumeratorOver, rationalTaylorNumeratorOver,
        componentCoordinateEquation, frobeniusPowerCoordinate, powerBatchedCoordinate]
        using component_generator_mem)
  have hgeneric := exists_frobeniusPowerGraph_of_symbolic_sample (k := 1) (K := 1) (ℓ := 1)
    domain (fun _ : Fin 2 ↦ componentWord) univ (by simp) (algebraMap ℚ ComponentField)
    1 0 (fun _ ↦ 0) (by intro i _; fin_cases i; simp [domain_zero]) 0
    componentCoordinateEquation (by omega) (by norm_num) 0 hτ
  obtain ⟨P', hdegree', _, hrecognize⟩ := hgeneric
  have hresult := hrecognize 0 (fun _ ↦ 0)
    (by simp [initialJetSeparant, separant, Fin.last, componentCoordinateEquation])
    (by intro l hl; simp at hl)
    (by intro i _; fin_cases i; simp [taylorAgreementEquationOver, commonTaylorNumeratorOver,
      rationalTaylorNumeratorOver, componentWord, componentCoordinateEquation,
      frobeniusPowerCoordinate, powerBatchedCoordinate])
  exact ⟨⟨P, hdegree, hsample, hseparant⟩,
    ⟨P', hdegree', by simpa using hresult.2⟩⟩

/-- The pair form of Frobenius component recognition reads the zero pair off the same sparse
sample cut and keeps the separant nonzero on its graph. -/
example :
    ∃ F₀ G₀ : ℚ[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧
      F₀.eval 0 = 0 ∧ G₀.eval 0 = 0 ∧
      aeval (frobeniusInitialGraph (0 : ComponentField) 1
        (F₀.map (algebraMap ℚ ComponentField))
      (G₀.map (algebraMap ℚ ComponentField)))
      (jointInitialJetSeparant (r := 0) (0 : ComponentField)
        (componentCoordinateEquation (E := ComponentField))) ≠ 0 := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  have hτ : TaylorExponentSufficient 0 1 0 := by intro l; fin_cases l; omega
  obtain ⟨F₀, G₀, hF₀, hG₀, hsample, -, -, hseparant⟩ :=
    exists_frobeniusGraph_of_symbolic_prime_sample (k := 1) (K := 1) domain componentWord
      componentWord univ (by simp) (algebraMap ℚ ComponentField) 1 0 (fun _ ↦ 0)
      (by intro i _; fin_cases i; simp [domain_zero]) 0 componentCoordinateEquation (by omega)
      (by norm_num) 0 hτ componentIdeal
      (by simpa [jointInitialJetSeparant, initialJetSeparant, separant,
        Fin.last, componentCoordinateEquation] using componentIdeal_one_notMem)
      componentIdeal_degree_pos (by intro l hl; simp at hl)
      (by intro i _; fin_cases i; simpa [componentWord, jointTaylorAgreementEquation,
        taylorAgreementEquationOver, commonTaylorNumeratorOver, rationalTaylorNumeratorOver,
        componentCoordinateEquation] using component_generator_mem)
  obtain ⟨h₀, h₁⟩ := hsample 0 (by simp)
  exact ⟨F₀, G₀, hF₀, hG₀, by simpa [componentWord, domain_zero] using h₀,
    by simpa [componentWord, domain_zero] using h₁, hseparant⟩

private abbrev finiteIncidenceEquation : DifferentialPolynomial ComponentField[X] 0 :=
  componentCoordinateEquation (E := ComponentField)
private def finiteIncidencePoint : Option (Fin 1) → ComponentField := fun _ ↦ 0
private def finiteIncidenceSet : Finset (Option (Fin 1) → ComponentField) :=
  {finiteIncidencePoint}
private def finiteIncidenceLeft : Fin 1 → ℚ := fun _ ↦ 0
private def finiteIncidenceRight : Fin 1 → ℚ := fun _ ↦ 1
private abbrev finiteIncidenceGraph : Set (Option (Fin 1) → ComponentField) :=
  admissibleFrobeniusPairGraphLocus domain finiteIncidenceLeft finiteIncidenceRight
    (algebraMap ℚ ComponentField) (fun i ↦ algebraMap ℚ ComponentField (domain i)) 0
    finiteIncidenceEquation 1 1 1 1
private abbrev finiteIncidenceAgreement (i : Fin 1) :=
  jointTaylorAgreementEquation 0 finiteIncidenceEquation 1 1
    (Polynomial.C ((algebraMap ℚ ComponentField) (domain i)))
    (Polynomial.C ((algebraMap ℚ ComponentField) (finiteIncidenceLeft i)) +
      Polynomial.X ^ (1 ^ 0) *
        Polynomial.C ((algebraMap ℚ ComponentField) (finiteIncidenceRight i)))
private def finiteIncidenceAgreementSet (x : Option (Fin 1) → ComponentField) : Set (Fin 1) :=
  {i | aeval x (finiteIncidenceAgreement i) = 0}
private theorem finiteIncidenceEquation_height : CoeffNatDegreeLE finiteIncidenceEquation 0 :=
  coeffNatDegreeLE_X _
private theorem finiteIncidenceEquation_jetDegree :
    weightedTotalDegree (fun i : JetVariable 0 ↦ i.elim 0 (fun _ ↦ 1))
      finiteIncidenceEquation ≤ 1 := by
  simp [finiteIncidenceEquation, componentCoordinateEquation, weightedTotalDegree,
    MvPolynomial.support_X]
private theorem finiteIncidencePoint_initial :
    aeval finiteIncidencePoint (jointInitialJetEquation 0 finiteIncidenceEquation) = 0 := by
  rw [aeval_jointInitialJetEquation]
  simp [finiteIncidencePoint, finiteIncidenceEquation, initialJetEquation]
private theorem finiteIncidencePoint_separant :
    aeval (fun _ : Fin 1 ↦ (0 : ComponentField))
      (initialJetSeparant 0
        (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) finiteIncidenceEquation))
      ≠ 0 := by
  norm_num [finiteIncidenceEquation, initialJetSeparant, separant, Fin.last]
private theorem finiteIncidenceEquation_span_proper :
    Ideal.span {jointInitialJetEquation 0 finiteIncidenceEquation} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have hu' := hu.map (MvPolynomial.aeval finiteIncidencePoint)
  rw [finiteIncidencePoint_initial] at hu'
  exact hu'.ne_zero rfl
private theorem finiteIncidencePoint_notGraph :
    finiteIncidencePoint ∉ finiteIncidenceGraph := by
  rintro ⟨F₀, G₀, hP, _⟩
  obtain ⟨sample, hcard, hsample⟩ := hP.sample
  have hmem : (0 : Fin 1) ∈ sample := by
    have hne : sample.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
    obtain ⟨i, hi⟩ := hne
    have hzero : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa [hzero] using hi
  have hFG : F₀.eval 0 = 0 ∧ G₀.eval 0 = 1 := by
    simpa [domain_zero, finiteIncidenceLeft, finiteIncidenceRight] using
      ⟨(hsample 0 hmem).2.1, (hsample 0 hmem).2.2.1⟩
  have hF : F₀ = 0 := by
    exact (eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP.degree_left)).trans
      (by simp [coeff_zero_eq_eval_zero, hFG.1])
  have hG : G₀ = 1 := by
    exact (eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP.degree_right)).trans
      (by simp [coeff_zero_eq_eval_zero, hFG.2])
  have hbad : (Polynomial.X : Polynomial ComponentField) = 0 := by
    simpa [jointInitialJetEquation, finiteIncidenceEquation, initialJetEquation,
      frobeniusInitialGraph, hF, hG] using hP.initial
  have heval := congrArg (Polynomial.eval (1 : ComponentField)) hbad
  norm_num at heval
private theorem finiteIncidencePoint_agreement :
    aeval finiteIncidencePoint (finiteIncidenceAgreement 0) = 0 := by
  have hτ : TaylorExponentSufficient 0 1 1 := by intro l; omega
  have hsep : aeval (fun _ : Fin 1 ↦ (0 : ComponentField))
      (initialJetSeparant 0
        (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) finiteIncidenceEquation))
      ≠ 0 := finiteIncidencePoint_separant
  have hrec : (rationalTaylorPolynomial 0
      (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) finiteIncidenceEquation)
      1 (fun _ ↦ (0 : ComponentField))).eval 0 = 0 := by
    simpa [rationalTaylorPolynomial, Polynomial.centeredCoefficientPrefix] using
      (rationalTaylorCoefficient_initial (0 : ComponentField)
        (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) finiteIncidenceEquation)
        (fun _ ↦ (0 : ComponentField)) (0 : Fin 1))
  rw [finiteIncidenceAgreement, aeval_jointTaylorAgreementEquation]
  simpa [finiteIncidencePoint, domain_zero, finiteIncidenceLeft, finiteIncidenceRight] using
    (taylorAgreementEquation_eq_zero_iff (0 : ComponentField)
      (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) finiteIncidenceEquation)
      hτ (fun _ ↦ (0 : ComponentField)) hsep 0 0).2 hrec
/-- A nonempty finite set of regular chart points outside Frobenius pair graphs satisfies the
finite incidence bound. -/
example : finiteIncidenceSet.Nonempty ∧ (finiteIncidenceSet.card : ℚ) ≤ 1 := by
  classical
  have hS : ∀ x ∈ finiteIncidenceSet,
      aeval x (jointInitialJetEquation 0 finiteIncidenceEquation) = 0 ∧
      aeval x (jointInitialJetSeparant 0 finiteIncidenceEquation) ≠ 0 ∧
      (∀ q ∈ frobeniusSparseTaylorCuts 0 finiteIncidenceEquation 1 1 (1 ^ 0),
        aeval x q = 0) ∧
      x ∉ finiteIncidenceGraph := by
    intro x hx
    have hx' : x = finiteIncidencePoint := Finset.mem_singleton.mp hx
    subst x
    refine ⟨finiteIncidencePoint_initial, ?_,
      (by intro q hq; simp [frobeniusSparseTaylorCuts] at hq), finiteIncidencePoint_notGraph⟩
    rw [aeval_jointInitialJetSeparant]
    simpa [finiteIncidencePoint] using finiteIncidencePoint_separant
  have hA : ∀ x ∈ finiteIncidenceSet, 1 ≤ (finiteIncidenceAgreementSet x).ncard := by
    intro x hx
    have hx' : x = finiteIncidencePoint := Finset.mem_singleton.mp hx
    subst x
    apply (Set.ncard_pos (Set.toFinite _)).2
    exact ⟨0, finiteIncidencePoint_agreement⟩
  have hbound := finite_frobeniusChartPoints_off_admissiblePairGraphs_card_le
    (F := ℚ) (E := ComponentField) (n := 1) (k := 1) (K := 1)
    (domain := domain) (f := finiteIncidenceLeft) (g := finiteIncidenceRight)
    (iota := algebraMap ℚ ComponentField) (p := 1) (e := 0)
    (roots := fun i ↦ algebraMap ℚ ComponentField (domain i))
    (hroots := by intro i; simp) (center := (0 : ComponentField))
    (Q := finiteIncidenceEquation) (hK := by omega) (hKk := by omega)
    (τ := 1) (h := 0) (b := 1) (A := 1) (hτ := by intro l; omega)
    (hτpos := by omega) (hb := by omega) (hkA := by omega)
    (hheight := finiteIncidenceEquation_height) (hjet := finiteIncidenceEquation_jetDegree)
    (hinit := jointInitialJetEquation_ne_zero_of_regular (0 : ComponentField) 0
      finiteIncidenceEquation (fun _ ↦ 0) finiteIncidencePoint_separant)
    (hproper := finiteIncidenceEquation_span_proper) (S := finiteIncidenceSet) hS hA
  exact ⟨by simp [finiteIncidenceSet], by simpa using hbound⟩
example := principalOpen_subset_admissibleFrobeniusPairGraphLocus
  (F := ℚ) (E := ComponentField) (n := 1) (k := 1) (K := 1)
  (domain := domain) (f := componentWord) (g := componentWord)
  (iota := algebraMap ℚ ComponentField) (p := 1) (e := 0)
  (roots := fun i ↦ algebraMap ℚ ComponentField (domain i))
  (hroots := by intro i; simp) (center := (0 : ComponentField))
  (Q := componentCoordinateEquation) (hK := by omega) (hKk := by omega) (τ := 0)
  (hτ := by intro l; fin_cases l; omega) (I := componentIdeal)
  (hI := componentIdeal_isPrime)
  (hs := by simpa [jointInitialJetSeparant, initialJetSeparant, separant,
    componentCoordinateEquation] using componentIdeal_one_notMem)
  (hinit := by simpa [jointInitialJetEquation, initialJetEquation,
    componentCoordinateEquation] using component_generator_mem)
  (hsparse := by intro q hq; simp [frobeniusSparseTaylorCuts] at hq)
  (hd := componentIdeal_degree_pos) (hcuts := by
    apply (Set.ncard_pos (Set.toFinite _)).2
    refine ⟨0, ?_⟩
    simpa [componentWord, domain_zero, jointTaylorAgreementEquation, taylorAgreementEquationOver,
      commonTaylorNumeratorOver, rationalTaylorNumeratorOver, initialJetSeparant, separant,
      componentCoordinateEquation, componentVariable] using component_generator_mem)
end

end ReedSolomon.GraphLineComponentTest

namespace ReedSolomon.PowerBatchedPointRecognitionTest

noncomputable section

/-- The one-point evaluation domain at zero over `ZMod 3`. -/
private def domain : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private theorem domain_zero : domain (0 : Fin 1) = 0 := rfl

private def recognitionWords : Fin 2 → Fin 1 → ZMod 3 :=
  fun t _ ↦ if t = 0 then 2 else 1

/-- The differential equation whose regular chart reconstructs the zero polynomial. -/
private def recognitionChart : DifferentialPolynomial (Polynomial (ZMod 3)) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

/-- The chart specialized at the recognition challenge `1`. -/
private def recognitionChartAt : DifferentialPolynomial (ZMod 3) 0 :=
  MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 3)) recognitionChart

/-- The recognition jet used at the regular chart point. -/
private def recognitionJet : Fin 1 → ZMod 3 := fun _ ↦ 0

/-- A sample with a nonzero second component and a nontrivial high cut yields all three
recognition conclusions at the regular chart point. -/
example : ∃ P : Fin 2 → Polynomial (ZMod 3), (∀ t, (P t).degree < 1) ∧
    (∀ i ∈ ({0} : Finset (Fin 1)), ∀ t, (P t).eval (domain i) = recognitionWords t i) ∧
    rationalTaylorPolynomial (0 : ZMod 3) recognitionChartAt 2 recognitionJet =
      powerBatchedPolynomial (fun t ↦ (P t).map (RingHom.id _)) 1 ∧
    (recognitionJet = fun j ↦ Polynomial.eval 1
      (powerBatchedJetGraph (r := 0) (0 : ZMod 3) (fun t ↦ (P t).map (RingHom.id _)) j)) ∧
    ∀ l : Fin 2, MvPolynomial.aeval recognitionJet
        (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 l.val) =
      MvPolynomial.aeval recognitionJet
          (initialJetSeparant (0 : ZMod 3) recognitionChartAt) ^ 4 *
        (Polynomial.taylor 0
          (powerBatchedPolynomial (fun t ↦ (P t).map (RingHom.id _)) 1)).coeff l.val := by
  obtain ⟨P, hP, hs, hrecognize⟩ :=
    exists_polynomialGraph_of_symbolic_sample_of_exponent (k := 1) (K := 2) (r := 0)
      domain recognitionWords {0} (by simp) (RingHom.id _) 0 recognitionChart (by omega) 4
      (taylorExponentSufficient_two_mul 0 2)
  have hS : MvPolynomial.aeval recognitionJet
      (initialJetSeparant (0 : ZMod 3) recognitionChartAt) ≠ 0 := by
    simp [recognitionChartAt, recognitionChart, initialJetSeparant, separant]
  have hjetZero : recognitionJet = polynomialJet 0 (0 : Polynomial (ZMod 3)) := by
    funext j; fin_cases j; simp [recognitionJet, polynomialJet, Polynomial.hasseJet]
  have hcoeff : rationalTaylorCoefficient (0 : ZMod 3) recognitionChartAt
      recognitionJet 1 = 0 := by
    rw [hjetZero, rationalTaylorCoefficient_eq_solution (0 : ZMod 3) recognitionChartAt 0
      (by simp [recognitionChartAt, recognitionChart, differentialSpecialization,
        differentialSpecializationHom])
      (by simp [recognitionChartAt, recognitionChart, separant, jetEvaluation, polynomialJet,
        Polynomial.hasseJet]) 1 (by intro i _ _; obtain rfl : i = 1 := (by omega); norm_num)]
    simp
  refine ⟨P, hP, hs, hrecognize 1 recognitionJet hS (fun l hl ↦ ?_) fun i _ ↦ ?_⟩
  · obtain rfl : l = 1 := Fin.ext (by omega)
    exact aeval_commonTaylorNumerator_eq_zero (0 : ZMod 3) recognitionChartAt
      recognitionJet 4 hS hcoeff
  · fin_cases i
    refine (taylorAgreementEquation_eq_zero_iff (0 : ZMod 3) recognitionChartAt
      (taylorExponentSufficient_two_mul 0 2) recognitionJet hS _ _).2 ?_
    have hc0 : rationalTaylorCoefficient (0 : ZMod 3) recognitionChartAt recognitionJet 0 = 0 :=
      rationalTaylorCoefficient_initial (0 : ZMod 3) recognitionChartAt recognitionJet 0
    rw [eval_rationalTaylorPolynomial, powerBatchedCoordinate_eval]
    simp [hc0, recognitionWords, Fin.sum_univ_succ, domain_zero,
      show (2 + 1 : ZMod 3) = 0 by decide]

local instance : DecidableEq (ZMod 3) := Classical.decEq _
local instance : DecidableEq (ZMod 3) := Classical.decEq _

private def batchedWords : Fin 2 → Fin 1 → ZMod 3 :=
  fun t _ ↦ if t = 0 then 0 else 1

private def batchedTuple : Fin 2 → (ZMod 3)[X] :=
  fun t ↦ if t = 0 then 0 else Polynomial.C 1

private theorem batchedTuple_common :
    1 ≤ (commonCurveAgreementSet domain batchedWords batchedTuple).card := by
  have hmem : (0 : Fin 1) ∈ commonCurveAgreementSet domain batchedWords batchedTuple := by
    rw [mem_commonCurveAgreementSet]
    intro t
    fin_cases t <;> simp [batchedTuple, batchedWords, domain]
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨0, hmem⟩)

private def zeroTuple : Fin 2 → (ZMod 3)[X] := fun _ ↦ 0

private def zeroWords : Fin 2 → Fin 1 → ZMod 3 := fun _ _ ↦ 0

private def zeroCandidate : ZMod 3 → (ZMod 3)[X] → Prop := fun _ Q ↦ Q = 0

private def retainedZeroTuple : Finset (Fin 2 → (ZMod 3)[X]) := {zeroTuple}

-- One retained zero tuple covers every degree-bounded zero candidate.
example : ∃ exceptional : Finset (ZMod 3),
    (exceptional.card : ℚ) ≤
      geometricTransferBound 0 1 1 1 0 0 (fun _ : PUnit ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) ∧
    ∀ z ∉ exceptional, ∀ Q, zeroCandidate z Q → Q.degree < 1 →
      HasExactPowerAgreement (ℓ := 1) domain zeroWords
        (RingHom.id (ZMod 3)) 1 z Q := by
  classical
  have h := exists_geometricTransfer_exceptional
    (α := Fin 1) (ν := PUnit) (k := 1) (ℓ := 1) (L := 0) (A := 0)
    domain zeroWords (RingHom.id (ZMod 3)) zeroCandidate ∅
    (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ ∅) (fun _ ↦ retainedZeroTuple)
    (fun _ ↦ by simp) (fun _ ↦ by simp [retainedZeroTuple, dimensionSensitiveIncidenceProduct])
    (fun _ P hP t ↦ by rw [Finset.mem_singleton.mp hP]; simp [zeroTuple]) (fun _ _ _ ↦ by simp)
    fun z Q hQ _ _ _ ↦ Or.inr ⟨(), zeroTuple, by simp [retainedZeroTuple],
      by rw [show Q = 0 from hQ]; simp [zeroTuple, powerBatchedPolynomial]⟩
  simpa [geometricTransferBound, Fintype.card_fin] using h

-- The identity embedding pulls back an empty exceptional set to an empty base-field set.
example : ∃ exceptional : Finset (ZMod 3), exceptional.card = 0 ∧
    ∀ z ∉ exceptional, ∀ Q, zeroCandidate z Q →
      HasExactPowerAgreement (ℓ := 1) domain zeroWords
        (RingHom.id (ZMod 3)) 1 z Q := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_geometricTransfer_baseField_semantic (domain := domain) (w := zeroWords)
      (iota := RingHom.id (ZMod 3)) (k := 1) (Candidate := zeroCandidate)
      (exceptional := ∅) (bound := 0) (by simp) fun z _ Q hQ ↦ by
        subst Q
        exact ⟨zeroTuple, fun t ↦ by simp [zeroTuple],
          by simp [zeroTuple, powerBatchedPolynomial], by
            ext i
            simp [zeroWords, zeroTuple, commonCurveAgreementSet, polynomialAgreementSet,
              powerBatchedWord]⟩
  exact ⟨exceptional, Nat.eq_zero_of_le_zero (by exact_mod_cast hcard), hgood⟩

-- The degree-one tuple uses the positive challenge term in exact power agreement.
example : ∃ exceptional : Finset (ZMod 3), exceptional.card ≤ 0 ∧
    ∀ z ∉ exceptional,
      HasExactPowerAgreement domain batchedWords (RingHom.id (ZMod 3)) 1 z
        (powerBatchedPolynomial
          (fun t ↦ (batchedTuple t).map (RingHom.id (ZMod 3))) z) := by
  classical
  have h := exists_exceptional_exactPowerAgreement (α := Fin 1) (ℓ := 1) (k := 1) (L := 1)
    domain batchedWords batchedTuple (RingHom.id (ZMod 3))
    (by intro t; fin_cases t <;> norm_num [batchedTuple]) batchedTuple_common
  simpa [Fintype.card_fin] using h

/-- A singleton sample recognizes the zero sparse Frobenius pullback. -/
example : ∃ P : Fin 2 → (ZMod 2)[X],
    (∀ t, (P t).degree < 1) ∧
    (∀ i ∈ (univ : Finset (Fin 1)), ∀ t, (P t).eval (pointDomain i) = 0) ∧
    (0 : (ZMod 2)[X]) =
      expand (ZMod 2) (2 ^ 1)
        (powerBatchedPolynomial (fun t ↦ (P t).map (RingHom.id (ZMod 2)))
          ((0 : ZMod 2) ^ (2 ^ 1))) ∧
    (0 : (ZMod 2)[X]).eval 0 =
      (powerBatchedPolynomial (fun t ↦ (P t).map (RingHom.id (ZMod 2)))
        ((0 : ZMod 2) ^ (2 ^ 1))).eval (0 ^ (2 ^ 1)) := by
  obtain ⟨P, hdegree, hsample, hrecognize⟩ :=
    exists_frobeniusPowerGraph_polynomials_of_sample (k := 1) (ℓ := 1) pointDomain
      (fun _ _ ↦ (0 : ZMod 2)) univ (by simp)
  have hresult := hrecognize (RingHom.id (ZMod 2)) 2 1
    (fun _ ↦ (0 : ZMod 2)) (0 : ZMod 2) (0 : ZMod 2) (0 : (ZMod 2)[X])
    (fun _ _ ↦ rfl) (by compute_degree!) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
  exact ⟨P, hdegree, hsample, hresult⟩

end

end ReedSolomon.PowerBatchedPointRecognitionTest

namespace ReedSolomon.GraphLineComponentTest

noncomputable section

private theorem component_cut_eq_length_one :
    taylorAgreementEquationOver (F := ComponentField) (0 : ComponentField[X])
      (componentEquation (E := ComponentField)) 1 0 0 (τ := 2) =
        initialJetEquation (0 : ComponentField[X])
          (componentEquation (E := ComponentField)) := by
  rw [taylorAgreementEquationOver, Fin.sum_univ_one]
  simp only [Fin.val_zero]
  have hnum : commonTaylorNumeratorOver ComponentField (0 : ComponentField[X])
      (componentEquation (E := ComponentField)) 2 0 =
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (Polynomial ComponentField)) := by
    simpa only [Polynomial.C_0] using component_commonNumerator_initial
  rw [hnum]
  simp [initialJetEquation, componentEquation, initialJetSeparant, separant, Fin.last]

private theorem component_jointCut_eq_length_one :
  jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 1 2 (0 : ComponentField[X]) 0 =
      jointInitialJetEquation (r := 0) (0 : ComponentField)
        (componentEquation (E := ComponentField)) := by
  simp only [jointTaylorAgreementEquation, jointInitialJetEquation, Polynomial.C_0]
  rw [component_cut_eq_length_one]
private def componentPowerTuple : Fin 2 → ℚ[X] := fun _ ↦ 0
private abbrev componentMap : ℚ →+* ComponentField := algebraMap ℚ ComponentField
private abbrev componentJet := componentEquation (E := ComponentField)
private theorem componentPowerGraphMap_zero :
    frobeniusPowerGraphMap (0 : ComponentField) 1
      (fun t ↦ (componentPowerTuple t).map componentMap) =
    fun i ↦ i.elim Polynomial.X fun _ ↦ 0 := by
  funext i
  cases i with
  | none => rfl
  | some j => fin_cases j; simp [frobeniusPowerGraphMap, frobeniusPowerInitialGraph,
      componentPowerTuple, frobeniusPowerCoordinate, powerBatchedCoordinate]
private theorem componentZeroTuple_graph_on_component :
    ∀ x ∈ {x | x ∈ zeroLocus ComponentField
      (componentIdeal (E := ComponentField)) ∧
      aeval x (jointInitialJetSeparant 0 componentJet) ≠ 0},
      x = fun i ↦ (frobeniusPowerGraphMap (0 : ComponentField) 1
        (fun t ↦ (componentPowerTuple t).map componentMap) i).eval (x none) := by
  intro x hx
  funext i
  cases i with
  | none => simp [componentPowerGraphMap_zero]
  | some j => fin_cases j; simpa [componentPowerGraphMap_zero, componentIdeal,
      componentVariable, zeroLocus_span] using hx.1
private theorem component_roots :
    ∀ i : Fin 1, (0 : ComponentField) ^ (1 ^ 0) =
      componentMap (domain i) := fun i ↦ by rw [Subsingleton.elim i 0]; simp [domain_zero]
private theorem extractedAdmissibleFrobeniusPowerTuple :
    IsAdmissibleFrobeniusPowerTuple domain (fun _ ↦ componentWord)
      componentMap (fun _ ↦ 0) 0 componentJet 1 1 2 1 componentPowerTuple := by
  have hgraph := componentPowerGraphMap_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    fin_cases t <;> simp [componentPowerTuple]
  · rw [component_initialEquation_eq_variable]
    simp [hgraph]
  · intro hsep
    have heval := congrArg (fun f : ComponentField[X] ↦ f.eval 0) hsep
    norm_num [hgraph, jointInitialJetSeparant, componentEquation,
      initialJetSeparant, separant, Fin.last] at heval
  · intro l hl
    fin_cases l
    norm_num at hl
  · refine ⟨univ, by simp, ?_, ?_⟩
    · intro i hi t
      simp [componentPowerTuple, componentWord]
    · intro i _
      obtain rfl := Subsingleton.elim i 0
      rw [hgraph]
      have hcoord :
          frobeniusPowerCoordinate 1
            (fun _ : Fin 2 ↦ componentMap (componentWord 0)) = 0 := by
        simp [frobeniusPowerCoordinate, powerBatchedCoordinate, componentWord]
      rw [hcoord]
      simp only [Polynomial.C_0]
      rw [component_jointCut_eq_length_one, component_initialEquation_eq_variable]
      simp
private theorem componentAgreementCut_mem :
    jointTaylorAgreementEquation 0 componentJet 1 2 (Polynomial.C (0 : ComponentField))
      (frobeniusPowerCoordinate 1 (fun _ : Fin 2 ↦ componentMap (componentWord 0))) ∈
      componentIdeal (E := ComponentField) := by
  rw [show frobeniusPowerCoordinate 1
      (fun _ : Fin 2 ↦ componentMap (componentWord 0)) = 0 by
        simp [frobeniusPowerCoordinate, powerBatchedCoordinate, componentWord]]
  simpa only [Polynomial.C_0] using
    (component_jointCut_eq_length_one ▸ component_initialEquation_mem)
private theorem componentAgreementCut_mem_at (i : Fin 1) :
    jointTaylorAgreementEquation 0 componentJet 1 2 (Polynomial.C (0 : ComponentField))
      (frobeniusPowerCoordinate 1 (fun _ : Fin 2 ↦ componentMap (componentWord i))) ∈
      componentIdeal (E := ComponentField) := by
  obtain rfl : i = 0 := Subsingleton.elim i 0; exact componentAgreementCut_mem
private theorem componentAgreementCuts_card_ge :
    1 ≤ {i : Fin 1 | jointTaylorAgreementEquation 0 componentJet 1 2
      (Polynomial.C (0 : ComponentField))
      (frobeniusPowerCoordinate 1 (fun _ : Fin 2 ↦ componentMap (componentWord i))) ∈
        componentIdeal (E := ComponentField)}.ncard := by
  have hp := (Set.ncard_pos (s := {i : Fin 1 | jointTaylorAgreementEquation 0 componentJet
    1 2 (Polynomial.C (0 : ComponentField))
    (frobeniusPowerCoordinate 1 (fun _ : Fin 2 ↦ componentMap (componentWord i))) ∈
      componentIdeal (E := ComponentField)})).2 ⟨0, componentAgreementCut_mem_at 0⟩
  omega
example : (componentPowerTuple 0).eval (domain 0) = componentWord 0 ∧
    componentRegularPoint ∈ admissibleFrobeniusPowerTupleGraphLocus domain
      (fun _ : Fin 2 ↦ componentWord) componentMap (fun _ ↦ 0) 0 componentJet 1 1 1 2 1 := by
  have hcommon := commonAgreement_of_frobeniusPowerAgreementEquation_mem_prime
    (domain := domain) (values := fun _ : Fin 2 ↦ componentWord) (ι := componentMap)
    (p := 1) (e := 0) (roots := fun _ ↦ 0) component_roots (center := 0)
    (Q := componentJet) (K := 1) (k := 1) (by omega) (by norm_num) (τ := 2)
    (taylorExponentSufficient_two_mul 0 1) (I := componentIdeal (E := ComponentField))
    (hI := componentIdeal_isPrime) component_separant_notMem componentIdeal_degree_pos
    (P := componentPowerTuple) extractedAdmissibleFrobeniusPowerTuple
    componentZeroTuple_graph_on_component 0 componentAgreementCut_mem
  have hsparse : ∀ q ∈ frobeniusPowerSparseTaylorNumerators 0 componentJet 1 2 1,
      q ∈ componentIdeal := by
    intro q hq
    simp [frobeniusPowerSparseTaylorNumerators] at hq
  have hprincipal := principalOpen_subset_admissibleFrobeniusPowerTupleGraphLocus
    (domain := domain) (values := fun _ : Fin 2 ↦ componentWord) (ι := componentMap)
    (p := 1) (e := 0) (roots := fun _ ↦ 0) component_roots (center := 0)
    (Q := componentJet) (K := 1) (k := 1) (L := 1) (by omega) (by norm_num) (by omega)
    (τ := 2) (taylorExponentSufficient_two_mul 0 1)
    (I := componentIdeal (E := ComponentField)) (hI := componentIdeal_isPrime)
    component_separant_notMem component_initialEquation_mem hsparse componentIdeal_degree_pos
    componentAgreementCuts_card_ge
  exact ⟨hcommon 0, hprincipal componentRegularPoint_mem⟩
private abbrev incidenceEquation := componentCoordinateEquation (E := ComponentField)
private def incidenceValues : Fin 2 → Fin 1 → ℚ := ![fun _ ↦ 0, fun _ ↦ 1]
private theorem incidenceTaylor_zero :
    rationalTaylorPolynomial 0
      (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) incidenceEquation)
      1 (fun _ : Fin 1 ↦ 0) = 0 := by
  have hsolution : differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) incidenceEquation)
      (0 : ComponentField[X]) = 0 := by
    simp [incidenceEquation, componentCoordinateEquation, differentialSpecialization,
      differentialSpecializationHom]
  have hsep : jetEvaluation
      (separant
        (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) incidenceEquation)
        (Fin.last 0)) 0 (polynomialJet 0 (0 : ComponentField[X])) ≠ 0 := by
    simp [incidenceEquation, componentCoordinateEquation, separant, jetEvaluation,
      polynomialJet]
  have hjet : (fun _ : Fin 1 ↦ (0 : ComponentField)) =
      polynomialJet 0 (0 : ComponentField[X]) := by
    ext j
    fin_cases j
    simp [polynomialJet]
  rw [hjet, rationalTaylorPolynomial_polynomialJet 0 _ 0 hsolution hsep
    (K := 1) (by simp) (by intro i hi; omega)]
private theorem componentRegularPoint_not_incidenceGraph :
    componentRegularPoint ∉ admissibleFrobeniusPowerTupleGraphLocus domain
      incidenceValues componentMap (fun _ ↦ 0) 0 incidenceEquation 1 1 1 2 1 := by
  rintro ⟨P, hP, -, -⟩
  obtain ⟨sample, hcard, hsample, -⟩ := hP.sample
  have hsample_univ : sample = Finset.univ :=
    Finset.eq_univ_of_card sample (by simpa [Fintype.card_fin] using hcard)
  have hzero (t : Fin 2) : P t = Polynomial.C (incidenceValues t 0) := by
    have hval : (P t).eval (domain 0) = incidenceValues t 0 :=
      hsample 0 (by rw [hsample_univ]; simp) t
    rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp (hP.degree t)),
      coeff_zero_eq_eval_zero]
    exact congrArg Polynomial.C (by simpa [domain_zero] using hval)
  have hinitial := hP.initial
  rw [show jointInitialJetEquation 0 incidenceEquation = componentVariable by
    simp [jointInitialJetEquation, initialJetEquation, incidenceEquation,
      componentCoordinateEquation, componentVariable]] at hinitial
  simp [frobeniusPowerGraphMap, frobeniusPowerInitialGraph, frobeniusPowerCoordinate,
    powerBatchedCoordinate, hzero, incidenceValues, componentVariable] at hinitial
example : ({componentRegularPoint} : Finset (Option (Fin 1) → ComponentField)).Nonempty ∧
    (({componentRegularPoint} : Finset (Option (Fin 1) → ComponentField)).card : ℚ) ≤ 1 := by
  classical
  have hheight : CoeffNatDegreeLE incidenceEquation 0 := by
    exact coeffNatDegreeLE_X (some (0 : Fin 1))
  have hjet : jetTotalDegree incidenceEquation ≤ 1 := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    have hu' : u = Finsupp.single (some (0 : Fin 1)) 1 := by
      simpa [incidenceEquation, componentCoordinateEquation, MvPolynomial.support_X] using hu
    subst u
    simp [totalJetDegree_eq_sum]
  have hinit : jointInitialJetEquation 0 incidenceEquation ≠ 0 := by
    simp [incidenceEquation, jointInitialJetEquation, initialJetEquation,
      componentCoordinateEquation]
  have hproper : Ideal.span ({jointInitialJetEquation 0 incidenceEquation} :
      Set (MvPolynomial (Option (Fin 1)) ComponentField)) ≠ ⊤ := by
    rw [show jointInitialJetEquation 0 incidenceEquation = componentVariable by
      simp [jointInitialJetEquation, initialJetEquation, incidenceEquation,
        componentCoordinateEquation, componentVariable]]
    exact componentIdeal_isPrime.ne_top
  have hS : ∀ x ∈ ({componentRegularPoint} :
      Finset (Option (Fin 1) → ComponentField)),
      aeval x (jointInitialJetEquation 0 incidenceEquation) = 0 ∧
      aeval x (jointInitialJetSeparant 0 incidenceEquation) ≠ 0 ∧
      (∀ q ∈ frobeniusPowerSparseTaylorNumerators 0 incidenceEquation 1 2 1,
        aeval x q = 0) ∧
      x ∉ admissibleFrobeniusPowerTupleGraphLocus domain incidenceValues componentMap
        (fun _ ↦ 0) 0 incidenceEquation 1 1 1 2 1 := by
    intro x hx
    rcases Finset.mem_singleton.mp hx with rfl
    refine ⟨by simp [jointInitialJetEquation, initialJetEquation, incidenceEquation,
      componentCoordinateEquation], ?_, ?_,
      componentRegularPoint_not_incidenceGraph⟩
    · simp [jointInitialJetSeparant, initialJetSeparant, separant, incidenceEquation,
        componentCoordinateEquation, Fin.last]
    · intro q hq
      simp [frobeniusPowerSparseTaylorNumerators] at hq
  have hA : ∀ x ∈ ({componentRegularPoint} :
      Finset (Option (Fin 1) → ComponentField)),
      1 ≤ {i : Fin 1 | aeval x
        (jointTaylorAgreementEquation 0 incidenceEquation 1 2 (Polynomial.C 0)
          (frobeniusPowerCoordinate 1
            (fun t ↦ componentMap (incidenceValues t i)))) = 0}.ncard := by
    intro x hx
    rcases Finset.mem_singleton.mp hx with rfl
    have hsep : aeval componentRegularPoint
        (jointInitialJetSeparant 0 incidenceEquation) ≠ 0 := by
      simp [jointInitialJetSeparant, initialJetSeparant, separant, incidenceEquation,
        componentCoordinateEquation, Fin.last]
    have hzero : aeval componentRegularPoint
        (jointTaylorAgreementEquation 0 incidenceEquation 1 2 (Polynomial.C 0)
          (frobeniusPowerCoordinate 1
            (fun t ↦ componentMap (incidenceValues t (0 : Fin 1))))) = 0 := by
      have hcalc : aeval componentRegularPoint
          (jointTaylorAgreementEquation 0 incidenceEquation 1 2 (Polynomial.C 0)
            (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)) = 0 := by
        rw [aeval_jointTaylorAgreementEquation_eq_zero_iff 0 incidenceEquation 1 2
          (taylorExponentSufficient_two_mul 0 1) componentRegularPoint hsep 0 0 1]
        rw [incidenceTaylor_zero]
        simp [componentRegularPoint]
      simpa [incidenceValues, frobeniusPowerCoordinate, powerBatchedCoordinate,
        Polynomial.smul_eq_C_mul, Polynomial.X] using hcalc
    have hp : 0 < {i : Fin 1 | aeval componentRegularPoint
        (jointTaylorAgreementEquation 0 incidenceEquation 1 2 (Polynomial.C 0)
          (frobeniusPowerCoordinate 1 (fun t ↦ componentMap (incidenceValues t i)))) = 0}.ncard :=
      (Set.ncard_pos).2 ⟨0, hzero⟩
    omega
  have hbound := finite_frobeniusPowerTupleIncidence_off_graphs_card_le
    (domain := domain) (values := incidenceValues) (ι := componentMap)
    (p := 1) (e := 0) (roots := fun _ ↦ 0) component_roots (center := 0)
    (Q := incidenceEquation) (K := 1) (k := 1) (by omega) (by norm_num)
    (τ := 2) (h := 0) (b := 1) (A := 1) (taylorExponentSufficient_two_mul 0 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) hheight hjet hinit hproper
    ({componentRegularPoint} : Finset (Option (Fin 1) → ComponentField)) hS hA
  refine ⟨by simp, ?_⟩
  convert hbound using 1; norm_num
private theorem extractedAdmissibleFrobeniusPair :
    IsAdmissibleFrobeniusPair domain componentWord componentWord
      componentMap (fun _ ↦ 0) 0 componentJet 1 1 2 1 0 0 := by
  have hgraph :
      frobeniusInitialGraph (0 : ComponentField) 1
        ((0 : ℚ[X]).map componentMap) ((0 : ℚ[X]).map componentMap) =
      fun i ↦ i.elim Polynomial.X fun _ ↦ 0 := by
    funext i
    cases i <;> simp [frobeniusInitialGraph]
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
  · rw [component_initialEquation_eq_variable]
    simp [frobeniusInitialGraph]
  · intro hsep
    have heval := congrArg (fun f : ComponentField[X] ↦ f.eval 0) hsep
    norm_num [hgraph, jointInitialJetSeparant, componentEquation,
      initialJetSeparant, separant, Fin.last] at heval
  · intro l hl; fin_cases l; norm_num at hl
  · refine ⟨univ, by simp, ?_⟩
    intro i hi
    fin_cases i
    refine ⟨component_roots 0, ?_, ?_, ?_⟩
    · simp [domain_zero, componentWord]
    · simp [domain_zero, componentWord]
    · rw [hgraph]
      simp [componentWord, component_jointCut_eq_length_one,
        component_initialEquation_eq_variable]
local instance : DecidableEq ComponentField := Classical.decEq _
private abbrev componentInitialDegree :=
  (jointInitialJetEquation (r := 0) (0 : ComponentField)
    (componentEquation (E := ComponentField))).degreeOf (some 0)
private abbrev componentRetainedPairs :=
  frobeniusRetainedPairFamily domain componentWord componentWord
    componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet 1 1 2 1
private abbrev componentRetainedTuples :=
  frobeniusRetainedPowerTupleFamily (ℓ := 1) domain (fun _ ↦ componentWord)
    componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet 1 1 2 1
example :
    ∃ P : Fin 2 → ℚ[X],
      IsAdmissibleFrobeniusPowerTuple domain (fun _ ↦ componentWord)
        componentMap (fun _ ↦ 0) 0 componentJet 1 1 2 1 P ∧
      rationalTaylorPolynomial (0 : ComponentField)
        (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField))
          componentJet) 1
        (fun j ↦ (frobeniusPowerGraphMap (0 : ComponentField) 1
          (fun t ↦ (P t).map componentMap) (some j)).eval 0) =
        Polynomial.expand ComponentField 1
          (powerBatchedPolynomial
            (fun t ↦ (P t).map componentMap) (0 : ComponentField)) := by
  refine ⟨componentPowerTuple, extractedAdmissibleFrobeniusPowerTuple, ?_⟩
  have hspec := extractedAdmissibleFrobeniusPowerTuple.specialize
    (K := 1) (k := 1) (p := 1) (e := 0)
    component_roots (by norm_num) (by norm_num)
    (taylorExponentSufficient_two_mul 0 1) 0 (by
      simp [jointInitialJetSeparant, initialJetSeparant, separant, Fin.last])
  simpa [pow_zero, one_pow] using hspec
example :
    ({componentPowerTuple} : Finset (Fin 2 → ℚ[X])).card ≤
        componentInitialDegree ∧
    ({((0 : ℚ[X]), (0 : ℚ[X]))} : Finset (ℚ[X] × ℚ[X])).card ≤
        componentInitialDegree ∧
    0 < componentRetainedPairs.card ∧ componentRetainedPairs.card ≤ componentInitialDegree ∧
    0 < componentRetainedTuples.card ∧
      componentRetainedTuples.card ≤ componentInitialDegree := by
  classical
  have hmem := (mem_frobeniusRetainedPairFamily_iff domain componentWord componentWord
    componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet 1 1 2 1 (0, 0)).mpr
    extractedAdmissibleFrobeniusPair
  have htmem := (mem_frobeniusRetainedPowerTupleFamily_iff domain
    (fun _ ↦ componentWord) componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet
    1 1 2 1 componentPowerTuple).mpr extractedAdmissibleFrobeniusPowerTuple
  refine ⟨?_, ?_, Finset.card_pos.mpr ⟨(0, 0), hmem⟩, ?_,
    Finset.card_pos.mpr ⟨componentPowerTuple, htmem⟩, ?_⟩
  · exact admissibleFrobeniusPowerTuples_card_le_degreeOf (K := 1) (k := 1)
      domain (fun _ ↦ componentWord) componentMap (fun _ ↦ (0 : ComponentField))
      0 componentJet 1 0 2
      component_roots (by norm_num) (by norm_num)
      (taylorExponentSufficient_two_mul 0 1) component_initialEquation_ne_zero
      {componentPowerTuple} fun P hP ↦ by
        rw [Finset.mem_singleton.mp hP]; exact extractedAdmissibleFrobeniusPowerTuple
  · exact admissibleFrobeniusPairs_card_le_degreeOf (K := 1) (k := 1)
      domain componentWord componentWord componentMap (fun _ ↦ (0 : ComponentField))
      0 componentJet 1 0 2
      (by norm_num) (by norm_num) (taylorExponentSufficient_two_mul 0 1)
      component_initialEquation_ne_zero {(0, 0)} fun P hP ↦ by
        rw [Finset.mem_singleton.mp hP]; exact extractedAdmissibleFrobeniusPair
  · exact frobeniusRetainedPairFamily_card_le (K := 1) (k := 1)
      domain componentWord componentWord componentMap (fun _ ↦ (0 : ComponentField))
      0 componentJet 1 0 2
      (by norm_num) (by norm_num) (taylorExponentSufficient_two_mul 0 1)
      component_initialEquation_ne_zero
  · exact frobeniusRetainedPowerTupleFamily_card_le (K := 1) (k := 1)
      domain (fun _ : Fin 2 ↦ componentWord) componentMap
      (fun _ ↦ (0 : ComponentField))
      0 componentJet 1 0 2 component_roots
      (by norm_num) (by norm_num) (taylorExponentSufficient_two_mul 0 1)
      component_initialEquation_ne_zero
example :
    ∃ exceptional : Finset ComponentField,
      exceptional.card ≤ 0 ∧
      ∀ P ∈ componentRetainedPairs, ∀ z ∉ exceptional,
      polynomialAgreementSet
          (domain.trans ⟨componentMap, componentMap.injective⟩)
          (fun i ↦ componentMap (componentWord i) + z * componentMap (componentWord i))
          (P.1.map componentMap + Polynomial.C z * P.2.map componentMap) =
          commonPolynomialAgreementSet domain componentWord componentWord P.1 P.2 := by
  simpa [componentRetainedPairs, Fintype.card_fin] using
    exists_exceptional_frobeniusRetainedPairFamily domain componentWord componentWord
      componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet 1 1 2 1

/-- Exact power agreement for zero words yields an exact correlated pair. -/
example : HasExactCorrelatedPair pointDomain (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 0)
    (RingHom.id (ZMod 2)) 1 0 0 := by
  apply exactCorrelatedPair_of_powerAgreement_one pointDomain
    ![fun _ ↦ (0 : ZMod 2), fun _ ↦ 0] (RingHom.id (ZMod 2)) 0 0
  refine ⟨![0, 0], ?_, ?_, ?_⟩
  · intro t
    fin_cases t <;> simp
  · simp [powerBatchedPolynomial]
  · ext i
    fin_cases i
    simp [powerBatchedWord, commonCurveAgreementSet, pointDomain]
example :
    ∃ exceptional : Finset ComponentField,
      exceptional.card ≤ 0 ∧
      ∀ P ∈ componentRetainedTuples, ∀ z ∉ exceptional,
        letI : DecidableEq ℚ := fun a b ↦ Classical.propDecidable (a = b)
        letI : DecidableEq ComponentField := fun a b ↦ Classical.propDecidable (a = b)
        HasExactPowerAgreement (ℓ := 1) domain (fun _ ↦ componentWord) componentMap 1 z
          (powerBatchedPolynomial (fun t ↦ (P t).map componentMap) z) := by
  simpa [componentRetainedTuples, Fintype.card_fin] using
    exists_exceptional_frobeniusRetainedPowerTupleFamily (ℓ := 1) domain
      (fun _ ↦ componentWord) componentMap (fun _ ↦ (0 : ComponentField)) 0
      componentJet 1 1 2 1
end
end ReedSolomon.GraphLineComponentTest

/-- The Taylor jet cut has degree at most eight at the concrete capped exponent. -/
example : regularPowerBatchedCutJetDegree 2 2 (τ := 4) ≤ 8 :=
  regularPowerBatchedCutJetDegree_le_two_mul 2 2 2 4 (by norm_num) (by norm_num) (by norm_num)

/-- The Taylor challenge cut has degree at most six at the concrete capped exponent. -/
example : regularPowerBatchedCutChallengeDegree 1 1 1 (τ := 4) ≤ 6 :=
  regularPowerBatchedCutChallengeDegree_le_three_mul 2 1 1 1 4 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The mixed degree is below its concrete uniform cap for a one-stage order-one chart. -/
example : regularPowerBatchedInitialMixedDegree 1 1 1 2 1 (τ := 4) ≤ 256 :=
  regularPowerBatchedInitialMixedDegree_le_uniformCaps 1 2 1 1 2 1 2 1 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Raising the Taylor exponent from zero to one increases the concrete agreement budget. -/
example :
    regularPowerBatchedAgreementSharpBound 1 2 1 1 1 1 2 1 1 (τ := 0) ≤
      regularPowerBatchedAgreementSharpBound 1 2 1 1 1 1 2 1 1 (τ := 1) :=
  regularPowerBatchedAgreementSharpBound_mono_exponent 1 2 1 1 1 1 2 1 1 0 1 (by norm_num)
