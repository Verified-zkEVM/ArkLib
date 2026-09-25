/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullDimension
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusAdmissibility
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusRetainedFamily
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleCounting
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleSeparableBound
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
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedDerivativeImage
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
/-- A nonzero affine line descends and gives degree-one power agreement. -/
example : HasExactPowerAgreement pointDomain ![fun _ ↦ (1 : ZMod 2), fun _ ↦ 0]
    (RingHom.id (ZMod 2)) 2 1 (1 + X) :=
  powerAgreement_one_of_exactCorrelatedPair pointDomain (fun _ ↦ 1) (fun _ ↦ 0)
    (RingHom.id (ZMod 2)) 1 (1 + X)
    (HasExactCorrelatedPair.descend pointDomain _ _ (algebraMap (ZMod 2) E₄) 2 1 (1 + X)
      ⟨(1, X), by norm_num, by norm_num, by simp [correlatedPairSpecialization], by
        ext i; fin_cases i; simp [polynomialAgreementSet, commonPolynomialAgreementSet,
          pointDomain]⟩)

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

private theorem singletonLineExactBound : LineExactAgreementBound pointDomain 1 1 0 :=
  fun f g ↦ ⟨∅, by simp, fun z _ P hP hclose ↦ by
    have hagree : polynomialAgreementSet pointDomain (fun i ↦ f i + z * g i) P = Finset.univ :=
      Finset.eq_univ_of_card _
        (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hclose))
    have heval := (mem_polynomialAgreementSet ..).mp (hagree ▸ Finset.mem_univ (0 : Fin 1))
    refine ⟨C (f 0), C (g 0), degree_C_le.trans_lt (by norm_num),
      degree_C_le.trans_lt (by norm_num), ?_, ?_⟩
    · rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP), coeff_zero_eq_eval_zero,
        ← C_mul, ← C_add, ← heval]; rfl
    · rw [hagree]; ext i; fin_cases i; simp [commonPolynomialAgreementSet, pointDomain]⟩

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
    exists_exceptional_graphLine_challenges fullDomain ![0, 0] ![0, 1] (0 : ℚ[X]) 0 (RingHom.id ℚ)
  have hcommon : commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 = {0} := by
    ext i; fin_cases i <;> simp [commonPolynomialAgreementSet, fullDomain]
  refine ⟨exceptional, by simpa [hcommon, Fintype.card_fin] using hcard, by_contra fun hz ↦ ?_⟩
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
private def firstOrderTestPoints : Fin 1 ↪ ComponentField :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
private def firstOrderChartValues : Fin 1 → ComponentField := fun _ ↦ 0
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

/-- A nonempty agreement cut lowers the affine Hilbert degree of this chart prime to zero. -/
example : (affineHilbertPolynomial
    (Ideal.span {(MvPolynomial.X (0 : Fin 1) : ChartRing 0 ComponentField)})).natDegree ≤ 0 := by
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

/-- Every regular point of a prime component lies on the recognized graph line, and agreement
cuts at two points, one more than the degree bound `k = 1`, give a pair with two common
agreements. -/
example :
    (∃ P₀ P₁ : ℚ[X], ∀ x, x ∈ zeroLocus ComponentField (componentIdeal (E := ComponentField)) ∧
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
  obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hcommon, -⟩ := exists_graphLine_pair_of_regular_component_agreements
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

private theorem componentAdmissibleTupleWitness : ∃ P : Fin 2 → ℚ[X],
    IsAdmissibleChartTupleAtExponent domain (fun _ ↦ componentWord)
      (algebraMap ℚ ComponentField) 0 (componentEquation (E := ComponentField)) 2 1 1 2 P := by
  obtain ⟨P, hP, _⟩ := exists_admissibleChartTuple_of_primeTaylorComponent_agreements
    (K := 2) (k := 1) (L := 1) domain (fun _ ↦ componentWord) univ (by simp) (by omega)
    (algebraMap ℚ ComponentField) 0 componentEquation (by omega) 2 (by intro l; omega)
    componentIdeal componentIdeal_isPrime component_separant_notMem componentIdeal_degree_pos
    component_initialEquation_mem component_highCuts component_powerBatchedAgreementCuts
  exact ⟨P, hP⟩

/-- A nonempty family of admissible tuples has a nonempty regular high-cut jet image. -/
example : ∃ z : ComponentField, ∃ jets : Finset (Fin 1 → ComponentField),
    jets.Nonempty ∧ jets.card = 1 ∧
      ∀ jet ∈ jets, aeval jet (initialJetSeparant 0
        (MvPolynomial.map (Polynomial.evalRingHom z) componentEquation)) ≠ 0 := by
  obtain ⟨P, hP⟩ := componentAdmissibleTupleWitness
  have hτ : TaylorExponentSufficient 0 2 2 := by intro l; fin_cases l <;> omega
  have htuples : ∀ R ∈ ({P} : Finset (Fin 2 → ℚ[X])),
      IsAdmissibleChartTupleAtExponent domain (fun _ ↦ componentWord)
        (algebraMap ℚ ComponentField) 0 componentEquation 2 1 1 2 R := by
    intro R hR
    rcases Finset.mem_singleton.mp hR with rfl
    exact hP
  obtain ⟨z, jets, _, himage, _, hcard, hregular, _⟩ :=
    exists_regularHighCutJetImage_of_admissibleChartTuples domain
      (fun _ ↦ componentWord) (algebraMap ℚ ComponentField) 0 componentEquation
      2 1 1 2 hτ (by omega) {P} htuples
  exact ⟨z, jets, ⟨_, himage P (by simp)⟩, by simpa using hcard,
    fun jet hj ↦ (hregular jet hj).2.1⟩

local instance : DecidableEq ComponentField := Classical.decEq _
private abbrev badChallengeEquation : DifferentialPolynomial ComponentField[X] 1 :=
  MvPolynomial.X (some (Fin.last 1))
private def positiveChallengeDomain : Fin 2 ↪ ComponentField where
  toFun i := (i.val : ComponentField)
  inj' _ _ h := Fin.ext (Nat.cast_inj.mp h)
private def positiveChallengeWords : Fin 2 → Fin 2 → ComponentField :=
  fun t i ↦ if t.val = 0 then 0 else i.val
private def positiveChallenges : Finset ComponentField := {0}
private def positiveChallengeWitness (_ : ComponentField) : ComponentField[X] := 0
private def positiveChallengeJet (_ : ComponentField) : Fin 2 → ComponentField := fun _ ↦ 0
private theorem badChallengeEquation_jetDegree : jetTotalDegree badChallengeEquation ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  rintro u hu
  simp [badChallengeEquation, MvPolynomial.support_X] at hu
  subst u
  simp [totalJetDegree_eq_sum]
private theorem badChallengeEquation_height : CoeffNatDegreeLE badChallengeEquation 1 := by
  exact (coeffNatDegreeLE_X (some (Fin.last 1))).mono (by omega)
private theorem badChallengeExponent : TaylorExponentSufficient 1 2 2 := by
  intro l
  omega
private theorem badChallengeChartAtZero :
    let Qz := MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField))
      badChallengeEquation
    (0 : ComponentField[X]).degree < 1 ∧
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
      rationalTaylorCoefficient 0 Qz (fun _ ↦ (0 : ComponentField)) l.val = 0 := fun l ↦ by
    simpa using rationalTaylorCoefficient_initial 0 Qz (fun _ : Fin 2 ↦ 0) l
  have hpoly := rationalTaylorPolynomial_polynomialJet 0 Qz (0 : ComponentField[X])
    hsolution hseparant (K := 2) (WithBot.bot_lt_coe 2) (by intro i hi hil; omega)
  rw [← hjet] at hpoly
  refine ⟨by simp, ?_, hsep, ?_, ?_⟩
  · simp [initialJetEquation, badChallengeEquation]
  · intro l _
    exact aeval_commonTaylorNumerator_eq_zero 0 Qz (fun _ ↦ 0) 2 hsep (hcoeff l)
  · exact hpoly
private theorem positiveChallenge_no_common (P : Fin 2 → ComponentField[X])
    (hdegree : ∀ t, (P t).degree < 1)
    (hcommon : commonCurveAgreementSet positiveChallengeDomain positiveChallengeWords P = univ) :
    False := by
  have h0 := ((mem_commonCurveAgreementSet positiveChallengeDomain
    positiveChallengeWords P 0).mp (by rw [hcommon]; simp)) 1
  have h1 := ((mem_commonCurveAgreementSet positiveChallengeDomain
    positiveChallengeWords P 1).mp (by rw [hcommon]; simp)) 1
  rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp (hdegree 1))] at h0 h1
  norm_num [positiveChallengeDomain, positiveChallengeWords] at h0 h1
  exact zero_ne_one (h0.symm.trans h1)
private theorem positiveChallenge_isBad :
    ¬ HasExactPowerAgreement positiveChallengeDomain positiveChallengeWords
      (RingHom.id ComponentField) 1 0 0 := by
  rintro ⟨P, hdegree, -, hsets⟩
  apply positiveChallenge_no_common P hdegree
  rw [← hsets]
  ext i
  simp [polynomialAgreementSet, positiveChallengeDomain, positiveChallengeWords,
    powerBatchedWord]
private abbrev positiveDerivativeBound :=
  regularPowerBatchedDerivativeCappedBoundTwo 2 1 2 1 1 1 1 1 1 2
/-- A nonempty positive-rate bad set has the derivative-capped finite and exceptional bounds. -/
example : positiveChallenges.Nonempty ∧
    (positiveChallenges.card : ℚ) ≤ positiveDerivativeBound ∧
    ∃ exceptional : Finset ComponentField,
      (exceptional.card : ℚ) ≤ positiveDerivativeBound ∧ 0 ∈ exceptional := by
  have hjet := badChallengeEquation_jetDegree
  have hheight := badChallengeEquation_height
  have hchart : ∀ z ∈ positiveChallenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) badChallengeEquation
      (positiveChallengeWitness z).degree < 1 ∧
        aeval (positiveChallengeJet z) (initialJetEquation 0 Qz) = 0 ∧
        aeval (positiveChallengeJet z) (initialJetSeparant 0 Qz) ≠ 0 ∧
        (∀ l : Fin 2, 1 ≤ l.val →
          aeval (positiveChallengeJet z) (commonTaylorNumerator 0 Qz 2 l.val) = 0) ∧
        rationalTaylorPolynomial 0 Qz 2 (positiveChallengeJet z) = positiveChallengeWitness z := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    rcases badChallengeChartAtZero with ⟨hd, hi, hs, hc, ht⟩
    exact ⟨hd, hi, hs,
      (fun l hl ↦ hc l (by omega)),
      by
        change rationalTaylorPolynomial 0
          (MvPolynomial.map (Polynomial.evalRingHom 0) badChallengeEquation) 2
          (fun _ : Fin 2 ↦ (0 : ComponentField)) = 0
        exact ht⟩
  have hagree : ∀ z ∈ positiveChallenges, 1 ≤
      (polynomialAgreementSet positiveChallengeDomain
        (powerBatchedWord positiveChallengeWords z) (positiveChallengeWitness z)).card := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    have hmem : (0 : Fin 2) ∈ polynomialAgreementSet positiveChallengeDomain
        (powerBatchedWord positiveChallengeWords 0) (positiveChallengeWitness 0) := by
      simp [polynomialAgreementSet, positiveChallengeDomain, positiveChallengeWords,
        positiveChallengeWitness, powerBatchedWord]
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨0, hmem⟩)
  have hbad : ∀ z ∈ positiveChallenges,
      ¬ HasExactPowerAgreement positiveChallengeDomain positiveChallengeWords
        (RingHom.id _) 1 z (positiveChallengeWitness z) := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    exact positiveChallenge_isBad
  have hbound := finite_powerBatchedBadChallenges_card_le_derivativeCapped_of_exponent
    positiveChallengeDomain positiveChallengeWords (RingHom.id _) 0 badChallengeEquation
    2 1 1 1 1 1 1 2 badChallengeExponent (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hjet hheight
    (by simp [badChallengeEquation]) positiveChallenges positiveChallengeWitness
    positiveChallengeJet hchart hagree hbad
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent
      positiveChallengeDomain positiveChallengeWords (RingHom.id _) badChallengeEquation
      2 1 1 1 1 1 1 2 badChallengeExponent (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hjet hheight
      (by simp [badChallengeEquation]) (by omega)
  have hzero : (0 : ComponentField) ∈ exceptional := by
    by_contra hz
    apply hbad 0 (by simp [positiveChallenges])
    exact hgood 0 hz 0 (by simp) (hagree 0 (by simp [positiveChallenges]))
      (by simp [badChallengeEquation, challengeSpecialization, differentialSpecialization,
        differentialSpecializationHom])
      (by simp [badChallengeEquation, challengeSpecialization, separant,
        differentialSpecialization, differentialSpecializationHom, Fin.last])
  exact ⟨by simp [positiveChallenges], hbound, exceptional, hcard, hzero⟩
private def incidencePoint : Option (Fin 2) → ComponentField := fun _ ↦ 0
private theorem incidencePoint_regular :
    aeval incidencePoint (jointInitialJetEquation 0 badChallengeEquation) = 0 ∧
      aeval incidencePoint (jointInitialJetSeparant 0 badChallengeEquation) ≠ 0 ∧
      (∀ l : Fin 2, 0 ≤ l.val →
        aeval incidencePoint (jointCommonTaylorNumerator 0 badChallengeEquation 2 l) = 0) := by
  let x : Option (Fin 2) → ComponentField := incidencePoint
  have hsep := (badChallengeChartAtZero).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [aeval_jointInitialJetEquation]
    simpa [x, incidencePoint, badChallengeEquation] using
      (badChallengeChartAtZero).2.1
  · rw [aeval_jointInitialJetSeparant]
    simpa [x, incidencePoint, badChallengeEquation] using hsep
  · intro l hl
    rw [aeval_jointCommonTaylorNumerator]
    simpa [x, incidencePoint, badChallengeEquation] using
      (badChallengeChartAtZero).2.2.2.1 l hl
private theorem badChallengeEquation_regular :
    jointInitialJetEquation 0 badChallengeEquation ≠ 0 := by
  exact jointInitialJetEquation_ne_zero_of_regular (center := (0 : ComponentField))
    (z := (0 : ComponentField)) badChallengeEquation (fun _ ↦ 0)
    (badChallengeChartAtZero).2.2.1
private def positiveIncidencePoints : Finset (Option (Fin 2) → ComponentField) :=
  {incidencePoint}
private theorem positiveIncidencePoint_offGraph :
    incidencePoint ∉ admissibleChartTupleGraphLocus positiveChallengeDomain
      positiveChallengeWords (RingHom.id _) 0 badChallengeEquation 2 1 2 2 := by
  rintro ⟨P, hP, -⟩
  apply positiveChallenge_no_common P hP.degree
  exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hP.common)
private theorem positiveIncidencePoint_agrees (i : Fin 2) :
    aeval incidencePoint (jointTaylorAgreementEquation 0 badChallengeEquation 2 2
      (Polynomial.C (positiveChallengeDomain i))
      (powerBatchedCoordinate (fun t ↦ positiveChallengeWords t i))) = 0 := by
  rw [aeval_jointTaylorAgreementEquation]
  have hcut := aeval_taylorAgreementEquation 0
    (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField)) badChallengeEquation)
    badChallengeExponent (fun _ : Fin 2 ↦ (0 : ComponentField))
    (badChallengeChartAtZero).2.2.1 (positiveChallengeDomain i) 0
  have ht := (badChallengeChartAtZero).2.2.2.2
  rw [ht] at hcut
  simpa [incidencePoint, positiveChallengeDomain, positiveChallengeWords,
    powerBatchedCoordinate, badChallengeEquation] using hcut

/-- A nonempty positive-k first-order incidence set satisfies the derivative-capped bound. -/
example : positiveIncidencePoints.Nonempty ∧
    (positiveIncidencePoints.card : ℚ) ≤
      (firstOrderCurveJointStageOne 2 1 1 1 1 2 : ℚ) := by
  have hS : ∀ x ∈ positiveIncidencePoints,
      aeval x (jointInitialJetEquation 0 badChallengeEquation) = 0 ∧
      aeval x (jointInitialJetSeparant 0 badChallengeEquation) ≠ 0 ∧
      (∀ l : Fin 2, 1 ≤ l.val →
        aeval x (jointCommonTaylorNumerator 0 badChallengeEquation 2 l) = 0) ∧
      x ∉ admissibleChartTupleGraphLocus positiveChallengeDomain positiveChallengeWords
        (RingHom.id _) 0 badChallengeEquation 2 1 2 2 := by
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨(incidencePoint_regular).1, (incidencePoint_regular).2.1,
      fun l hl ↦ (incidencePoint_regular).2.2 l (by omega),
      positiveIncidencePoint_offGraph⟩
  have hA : ∀ x ∈ positiveIncidencePoints, 2 ≤
      ({i : Fin 2 | aeval x (jointTaylorAgreementEquation 0 badChallengeEquation 2 2
        (Polynomial.C (positiveChallengeDomain i))
        (powerBatchedCoordinate (fun t ↦ positiveChallengeWords t i))) = 0} :
        Set (Fin 2)).ncard := by
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    have hset : {i : Fin 2 | aeval incidencePoint
        (jointTaylorAgreementEquation 0 badChallengeEquation 2 2
          (Polynomial.C (positiveChallengeDomain i))
          (powerBatchedCoordinate (fun t ↦ positiveChallengeWords t i))) = 0} =
        Set.univ := by
      ext i
      simp [positiveIncidencePoint_agrees]
    rw [hset]
    simp
  have hbound := finite_powerBatched_regular_points_off_graphs_card_le_derivativeCapped_of_exponent
    positiveChallengeDomain positiveChallengeWords (RingHom.id _) 0 badChallengeEquation
    2 1 2 2 1 1 1 2 badChallengeExponent (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
    badChallengeEquation_jetDegree badChallengeEquation_height (by simp [badChallengeEquation])
    positiveIncidencePoints hS hA
  have hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) ComponentField),
      J.IsPrime → jointInitialJetSeparant 0 badChallengeEquation ∉ J →
      jointInitialJetEquation 0 badChallengeEquation ∈ J →
      (∀ l : Fin 2, 1 ≤ l.val → jointCommonTaylorNumerator 0 badChallengeEquation 2 l ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      2 ≤ {i : Fin 2 | jointTaylorAgreementEquation 0 badChallengeEquation 2 2
        (Polynomial.C (positiveChallengeDomain i))
        (powerBatchedCoordinate (fun t ↦ positiveChallengeWords t i)) ∈ J}.ncard →
      {x | x ∈ zeroLocus ComponentField J ∧
        aeval x (jointInitialJetSeparant 0 badChallengeEquation) ≠ 0} ⊆
        admissibleChartTupleGraphLocus positiveChallengeDomain positiveChallengeWords
          (RingHom.id _) 0 badChallengeEquation 2 1 2 2 := by
    intro J hJ hs hg hhigh hd hcuts
    exact principalOpen_subset_admissibleChartTupleGraphLocus
      positiveChallengeDomain positiveChallengeWords (RingHom.id _) 0 badChallengeEquation
      2 1 2 2 (by omega) (by omega) badChallengeExponent J hJ hs hd hg hhigh hcuts
  have _ :=
    finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_terminal_recognition
      positiveChallengeDomain positiveChallengeWords (RingHom.id _) 0 badChallengeEquation
      2 1 2 2 1 1 2 badChallengeExponent (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
      badChallengeEquation_jetDegree badChallengeEquation_height hterminal positiveIncidencePoints
      hS hA
  have _ := finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_exponent
    positiveChallengeDomain positiveChallengeWords (RingHom.id _) 0 badChallengeEquation
    2 1 2 2 1 1 2 badChallengeExponent (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
    badChallengeEquation_jetDegree badChallengeEquation_height positiveIncidencePoints hS hA
  have _ := finite_powerBatched_regular_points_off_admissible_graphs_card_le_firstOrder_of_exponent
    (domain := positiveChallengeDomain) (w := positiveChallengeWords) (iota := RingHom.id _)
    (center := 0) (Q := badChallengeEquation) (K := 2) (k := 1) (L := 2) (A := 2)
    (v := 1) (h := 1) (τ := 2) badChallengeExponent
    (by norm_num [regularPowerBatchedCutChallengeDegree])
    (by omega) (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
    badChallengeEquation_jetDegree badChallengeEquation_height positiveIncidencePoints hS hA
  exact ⟨by simp [positiveIncidencePoints], by simpa using hbound⟩

/-- The pair form of Frobenius component recognition reads the zero pair off the same sparse
sample cut and keeps the separant nonzero on its graph. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧ F₀.eval 0 = 0 ∧ G₀.eval 0 = 0 ∧
    aeval (frobeniusInitialGraph (0 : ComponentField) 1 (F₀.map (algebraMap ℚ ComponentField))
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

end

end ReedSolomon.GraphLineComponentTest

namespace ReedSolomon.PowerBatchedPointRecognitionTest

noncomputable section

private abbrev E₉ := FiniteField.Extension (ZMod 3) 3 2

/-- The one-point evaluation domain at zero over `ZMod 3`. -/
private def domain : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private theorem domain_zero : domain (0 : Fin 1) = 0 := rfl

/-- The two-point evaluation domain in `ZMod 3`. -/
private def exceptionalDomain : Fin 2 ↪ ZMod 3 :=
  ⟨fun i ↦ (i.val : ZMod 3), by decide⟩

/-- The tuple agrees at zero, while its second word component creates one bad challenge. -/
private def exceptionalWords : Fin 2 → Fin 2 → ZMod 3 :=
  fun t i ↦ if t = 0 then 0 else if i = 0 then 0 else 1

/-- The zero polynomial tuple matching `exceptionalWords` at zero. -/
private def exceptionalPolynomials : Fin 2 → Polynomial (ZMod 3) :=
  fun _ ↦ 0

/-- Nonzero second word component with a zero batched value at challenge `1`. -/
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
local instance : DecidableEq E₉ := Classical.decEq _

/-- A two-component tuple has one exceptional challenge; scalar extension preserves its concrete
common agreement set. -/
example : ∃ exceptional : Finset E₉, exceptional.card ≤ 1 ∧ (∀ z ∉ exceptional,
      polynomialAgreementSet
        (exceptionalDomain.trans ⟨algebraMap (ZMod 3) E₉, (algebraMap (ZMod 3) E₉).injective⟩)
        (powerBatchedWord (fun t i ↦ algebraMap (ZMod 3) E₉ (exceptionalWords t i)) z)
        (powerBatchedPolynomial
          (fun t ↦ (exceptionalPolynomials t).map (algebraMap (ZMod 3) E₉)) z) = {0}) ∧
    commonCurveAgreementSet
      (exceptionalDomain.trans ⟨algebraMap (ZMod 3) E₉, (algebraMap (ZMod 3) E₉).injective⟩)
      (fun t i ↦ algebraMap (ZMod 3) E₉ (exceptionalWords t i))
      (fun t ↦ (exceptionalPolynomials t).map (algebraMap (ZMod 3) E₉)) = {0} := by
  have hbase : commonCurveAgreementSet exceptionalDomain exceptionalWords
      exceptionalPolynomials = {0} := by
    ext i; fin_cases i <;> simp [commonCurveAgreementSet, Fin.forall_fin_two,
      exceptionalWords, exceptionalPolynomials, exceptionalDomain]
  obtain ⟨exceptional, hbound, hgood⟩ := exists_exceptional_powerBatched_extension
    exceptionalDomain exceptionalWords exceptionalPolynomials (algebraMap (ZMod 3) E₉) 1
    (by simp [hbase])
  exact ⟨exceptional, by simpa using hbound, fun z hz ↦ (hgood z hz).trans hbase,
    (commonCurveAgreementSet_map ..).trans hbase⟩

private def batchedWords : Fin 2 → Fin 1 → ZMod 3 :=
  fun t _ ↦ if t = 0 then 0 else 1

private def batchedTuple : Fin 2 → (ZMod 3)[X] :=
  fun t ↦ if t = 0 then 0 else Polynomial.C 1

private def alternateBatchedTuple : Fin 2 → (ZMod 3)[X] :=
  fun t ↦ if t = 0 then 0 else Polynomial.C 1 + Polynomial.X

private def candidateFamily : Finset (Fin 2 → (ZMod 3)[X]) :=
  {batchedTuple, alternateBatchedTuple}

private theorem batchedTuple_common :
    1 ≤ (commonCurveAgreementSet domain batchedWords batchedTuple).card := by
  have hmem : (0 : Fin 1) ∈ commonCurveAgreementSet domain batchedWords batchedTuple := by
    rw [mem_commonCurveAgreementSet]
    intro t
    fin_cases t <;> simp [batchedTuple, batchedWords, domain]
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨0, hmem⟩)

private theorem candidateFamily_degree :
    ∀ P ∈ candidateFamily, ∀ t, (P t).degree < 2 := by
  intro P hP t
  simp only [candidateFamily, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl <;> refine lt_of_le_of_lt (b := 1) ?_ (by decide) <;>
    simp only [batchedTuple, alternateBatchedTuple] <;> split_ifs <;> compute_degree!

private theorem candidateFamily_common :
    ∀ P ∈ candidateFamily,
      1 ≤ (commonCurveAgreementSet domain batchedWords P).card := by
  intro P hP
  simp only [candidateFamily, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · exact batchedTuple_common
  refine Finset.card_pos.mpr ⟨0, (mem_commonCurveAgreementSet ..).2 fun t ↦ ?_⟩
  fin_cases t <;> simp [alternateBatchedTuple, batchedWords, domain_zero]

private theorem batchedCandidates_ne : batchedTuple ≠ alternateBatchedTuple := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  simp [batchedTuple, alternateBatchedTuple] at h1

private def zeroTuple : Fin 2 → (ZMod 3)[X] := fun _ ↦ 0

private def zeroWords : Fin 2 → Fin 1 → ZMod 3 := fun _ _ ↦ 0

private def zeroCandidate : ZMod 3 → (ZMod 3)[X] → Prop := fun _ Q ↦ Q = 0

private def retainedZeroTuple : Finset (Fin 2 → (ZMod 3)[X]) := {zeroTuple}

-- One retained zero tuple covers every degree-bounded zero candidate.
example : ∃ exceptional : Finset (ZMod 3),
    (exceptional.card : ℚ) ≤
      geometricTransferBound 0 1 1 1 0 0 (fun _ : PUnit ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) ∧
    ∀ z ∉ exceptional, ∀ Q, zeroCandidate z Q →
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
  obtain ⟨exceptional, hcard, hgood⟩ := h
  exact exists_geometricTransfer_baseField_semantic (domain := domain) (w := zeroWords)
    (iota := RingHom.id (ZMod 3)) (k := 1) (Candidate := zeroCandidate) exceptional
    (geometricTransferBound 0 1 1 1 0 0 (fun _ : PUnit ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1))
    (by simpa [geometricTransferBound, Fintype.card_fin] using hcard)
    (by rintro z hz Q rfl; simpa using hgood z hz 0 rfl (by simp) (by omega))

-- Two distinct degree-bounded tuples share the one-point sample and have one family bound.
example : ∃ exceptional : Finset (ZMod 3), exceptional.card ≤ 0 ∧
    ∀ P ∈ candidateFamily, ∀ z ∉ exceptional,
      HasExactPowerAgreement domain batchedWords (RingHom.id (ZMod 3)) 2 z
        (powerBatchedPolynomial
          (fun t ↦ (P t).map (RingHom.id (ZMod 3))) z) := by
  classical
  have h := exists_exceptional_exactPowerAgreement_family
    (α := Fin 1) (ℓ := 1) (k := 2) (L := 1) domain batchedWords
    (RingHom.id (ZMod 3)) candidateFamily candidateFamily_degree candidateFamily_common
  simpa [Fintype.card_fin, candidateFamily, batchedCandidates_ne] using h


end

end ReedSolomon.PowerBatchedPointRecognitionTest

namespace ReedSolomon.GraphLineComponentTest

noncomputable section

private def zeroCertificateValues : Fin 2 → Fin 1 → ℚ := fun _ _ ↦ 0
private theorem componentCoordinateJetDegree :
    jetTotalDegree (componentCoordinateEquation (E := ℚ)) ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  simp [componentCoordinateEquation, MvPolynomial.support_X] at hu
  subst u
  simp [totalJetDegree_eq_sum]
private def zeroCurveCertificate :
    SymbolicReceivedCurve.Certificate 1 1 1 1 0 0 domain
      (fun i ↦ powerBatchedCoordinate (fun t ↦ zeroCertificateValues t i)) := by
  refine ⟨componentCoordinateEquation, ?_, ?_, ?_⟩
  · exact coeffNatDegreeLE_X (some (0 : Fin 1))
  · exact (jetTotalDegree_le_iff _ _).mp componentCoordinateJetDegree
  · intro E _ ρ z
    refine ⟨by simp [componentCoordinateEquation], ?_, ?_⟩
    · exact (jetTotalDegree_map_le (Polynomial.eval₂RingHom ρ z)
        (componentCoordinateEquation (E := ℚ))).trans componentCoordinateJetDegree
    · intro indices P hdegree hcard hagree
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < indices.card)
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      have hval : P.eval 0 = 0 := by
        simpa [domain_zero, zeroCertificateValues, powerBatchedCoordinate] using hagree 0 hi
      have hconst := eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hdegree)
      have hzero : P = 0 := by
        rw [hconst, coeff_zero_eq_eval_zero]
        simpa using hval
      simpa [componentCoordinateEquation, differentialSpecialization,
        differentialSpecializationHom] using hzero

example := zeroCurveCertificate.exists_exceptional_powerBatchedAgreement_sharp_of_exponent
  (algebraMap ℚ ComponentField) 1 1 1
  (by
    intro r hr
    have hr0 : r = 0 := by omega
    subst r
    intro l
    omega)
  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) (by omega)

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
      componentRetainedTuples.card ≤ componentInitialDegree ∧
    ∃ exceptional : Finset ComponentField,
      exceptional.card ≤ 0 ∧ ∀ P ∈ componentRetainedPairs, ∀ z ∉ exceptional,
        polynomialAgreementSet
            (domain.trans ⟨componentMap, componentMap.injective⟩)
            (fun i ↦ componentMap (componentWord i) + z * componentMap (componentWord i))
            (P.1.map componentMap + Polynomial.C z * P.2.map componentMap) =
          commonPolynomialAgreementSet domain componentWord componentWord P.1 P.2 := by
  classical
  have hmem := (mem_frobeniusRetainedPairFamily_iff domain componentWord componentWord
    componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet 1 1 2 1 (0, 0)).mpr
    extractedAdmissibleFrobeniusPair
  have htmem := (mem_frobeniusRetainedPowerTupleFamily_iff domain
    (fun _ ↦ componentWord) componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet
    1 1 2 1 componentPowerTuple).mpr extractedAdmissibleFrobeniusPowerTuple
  refine ⟨?_, ?_, Finset.card_pos.mpr ⟨(0, 0), hmem⟩, ?_,
    Finset.card_pos.mpr ⟨componentPowerTuple, htmem⟩, ?_, ?_⟩
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
  · simpa [componentRetainedPairs, Fintype.card_fin] using
      exists_exceptional_frobeniusRetainedPairFamily domain componentWord componentWord
        componentMap (fun _ ↦ (0 : ComponentField)) 0 componentJet 1 1 2 1
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

namespace ReedSolomon.FrobeniusRegularBoundAcceptanceTest

noncomputable section

private abbrev RegularBoundField := ℂ
private def regularBoundDomain : Fin 2 ↪ ℂ where
  toFun i := i.val
  inj' _i _j h := Fin.ext (Nat.cast_injective (R := ℂ) h)
private def regularBoundValues : Fin 2 → Fin 2 → ℂ := fun t i ↦ if t = 0 then 0 else i.val
private abbrev regularBoundEquation :
    DifferentialPolynomial RegularBoundField[X] 0 := X (some (0 : Fin 1))
private def regularBoundWitness (_ : RegularBoundField) : RegularBoundField[X] := 0

example : ∃ exceptional : Finset RegularBoundField,
    exceptional.card ≤ 1 ∧ (0 : RegularBoundField) ∈ exceptional := by
  classical
  have hroots : ∀ i, regularBoundDomain i ^ (1 ^ 0) = regularBoundDomain i := by simp
  have hτ : TaylorExponentSufficient 0 1 1 := by
    intro l
    fin_cases l
    norm_num [TaylorExponentSufficient]
  have hjet : jetTotalDegree regularBoundEquation ≤ 1 := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    have hu' : u = Finsupp.single (some (0 : Fin 1)) 1 := by
      simpa [regularBoundEquation, MvPolynomial.support_X] using hu
    rw [hu']
    simp [totalJetDegree_eq_sum]
  have hirr : Irreducible regularBoundEquation := by
    exact (MvPolynomial.X_prime : Prime regularBoundEquation).irreducible
  have hder : pderiv (some (0 : Fin 1)) regularBoundEquation ≠ 0 := by
    simp [regularBoundEquation, MvPolynomial.pderiv_X]
  have hdegree : regularBoundEquation.degreeOf (some (0 : Fin 1)) = 1 := by
    simp [regularBoundEquation]
  have hleft : polynomialAgreementSet regularBoundDomain (powerBatchedWord regularBoundValues 0)
      (regularBoundWitness 0) = Finset.univ := by
    ext i
    fin_cases i <;> simp [polynomialAgreementSet, regularBoundDomain,
      regularBoundValues, regularBoundWitness, powerBatchedWord]
  have hdomain : regularBoundDomain.trans ⟨RingHom.id ℂ,
      (RingHom.id ℂ).injective⟩ = regularBoundDomain := by
    ext i
    rfl
  have hbad : ∀ z ∈ ({(0 : RegularBoundField)} : Finset RegularBoundField),
      ¬HasExactPowerAgreement regularBoundDomain regularBoundValues (RingHom.id ℂ) 1
        (z ^ (1 ^ 0)) (regularBoundWitness z) := by
    intro z hz hexact
    have : z = 0 := Finset.mem_singleton.mp hz
    subst z
    have hexact0 : HasExactPowerAgreement regularBoundDomain regularBoundValues (RingHom.id ℂ) 1 0
        (regularBoundWitness 0) := by simpa using hexact
    obtain ⟨P, hdeg, hpoly, hsets⟩ :=
      (hasExactPowerAgreement_id_iff regularBoundDomain regularBoundValues 1 0
        (regularBoundWitness 0)).mp hexact0
    have hcommon : commonCurveAgreementSet regularBoundDomain regularBoundValues P =
        Finset.univ := by
      rw [← hsets]
      exact hleft
    have h0 :=
      (mem_commonCurveAgreementSet regularBoundDomain regularBoundValues P 0).mp
        (by rw [hcommon]; simp)
    have h1 :=
      (mem_commonCurveAgreementSet regularBoundDomain regularBoundValues P 1).mp
        (by rw [hcommon]; simp)
    have hconst : P 1 = Polynomial.C ((P 1).coeff 0) := by
      apply eq_C_of_degree_le_zero
      exact Order.lt_succ_iff.mp (hdeg 1)
    have heval : (P 1).eval (regularBoundDomain 0) = (P 1).eval (regularBoundDomain 1) := by
      rw [hconst]
      simp
    have hfalse : (0 : ℂ) = 1 := by
      calc
        0 = (P 1).eval (regularBoundDomain 0) := by
          simpa [regularBoundValues, regularBoundDomain] using (h0 1).symm
        _ = (P 1).eval (regularBoundDomain 1) := heval
        _ = 1 := by simpa [regularBoundValues, regularBoundDomain] using h1 1
    exact zero_ne_one hfalse
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_frobeniusPowerSeparableSolutions_at
      (F := ℂ) (E := ℂ) (n := 2) (k := 1) (K := 1) (ℓ := 1) (L := 2)
      regularBoundDomain regularBoundValues (RingHom.id ℂ) regularBoundDomain
      regularBoundEquation 1 0 1 0 1 2 hroots (by norm_num) (by norm_num) hτ
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (coeffNatDegreeLE_X (some (0 : Fin 1))) hjet hirr hder hdegree
  have hzero : (0 : ℂ) ∈ exceptional := by
    by_contra hz
    apply hbad 0 (by simp)
    apply hgood 0 hz (regularBoundWitness 0)
    · norm_num [regularBoundWitness]
    · simp [regularBoundEquation, regularBoundWitness, challengeSpecialization,
        differentialSpecialization, differentialSpecializationHom]
    · rw [hdomain]
      norm_num [RingHom.id_apply]
      change 2 ≤ (polynomialAgreementSet regularBoundDomain
        (powerBatchedWord regularBoundValues 0) (regularBoundWitness 0)).card
      rw [hleft]
      simp
  refine ⟨exceptional, ?_, hzero⟩
  norm_num at hcard
  exact hcard

end

end ReedSolomon.FrobeniusRegularBoundAcceptanceTest
