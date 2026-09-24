/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullDimension
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusAdmissibility
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentAgreement
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedGeometricTransfer
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
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

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for Reed–Solomon mutual correlated agreement -/

open Polynomial Finset ReedSolomon ReedSolomon.FirstOrder.Squarefree PolynomialDifferential

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
private noncomputable def agreementEquation : DifferentialPolynomial (ZMod 2)[X] 0 :=
  MvPolynomial.X (some 0) - MvPolynomial.C (Polynomial.X)

noncomputable section

local instance : DecidableEq E₄ := Classical.decEq E₄

/-- A nonzero affine line descends from the degree-two extension. -/
example : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    (RingHom.id (ZMod 2)) 2 1 (1 + X) := by
  let ι : ZMod 2 →+* E₄ := algebraMap (ZMod 2) E₄
  have hext : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
      ι 2 (ι 1) ((1 + X : (ZMod 2)[X]).map ι) := by
    refine ⟨(1, X), by norm_num, by norm_num, ?_, ?_⟩
    · simp [correlatedPairSpecialization]
    · ext i
      fin_cases i
      simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]
  exact HasExactCorrelatedPair.descend pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    ι 2 1 (1 + X) hext

example : agreementEquation ≠ 0 ∧
    ∃ exceptional : Finset (ZMod 2), exceptional.card ≤ 0 ∧
      HasExactCorrelatedPair pointDomain (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1)
        (RingHom.id (ZMod 2)) 2 1 (C 1) ∧
      differentialSpecialization
        (challengeSpecialization
          (MvPolynomial.map (Polynomial.mapRingHom (algebraMap (ZMod 2) E₄)) agreementEquation)
          (algebraMap (ZMod 2) E₄ 1)) (C (algebraMap (ZMod 2) E₄ 1)) = 0 ∧
      polynomialAgreementSet
        (pointDomain.trans ⟨algebraMap (ZMod 2) E₄,
          (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ 0 + algebraMap (ZMod 2) E₄ 1 *
          algebraMap (ZMod 2) E₄ 1)
        (C (algebraMap (ZMod 2) E₄ 1)) = Finset.univ := by
  let ι : ZMod 2 →+* E₄ := algebraMap (ZMod 2) E₄
  have hnonzero : agreementEquation ≠ 0 := by
    intro heq
    have hcoeff := congrArg
      (fun q : DifferentialPolynomial (ZMod 2)[X] 0 =>
        q.coeff (Finsupp.single (some (0 : Fin 1)) 1)) heq
    have hindex : (0 : JetVariable 0 →₀ ℕ) ≠ Finsupp.single (some (0 : Fin 1)) 1 := by
      intro h
      have hvalue := congrArg (fun f : JetVariable 0 →₀ ℕ => f (some (0 : Fin 1))) h
      simp at hvalue
    norm_num [agreementEquation, hindex] at hcoeff
  have hgood : ∀ z ∉ (∅ : Finset E₄), ∀ P : E₄[X], P.degree < 2 →
      1 ≤ (polynomialAgreementSet (pointDomain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι ((fun _ : Fin 1 ↦ (0 : ZMod 2)) i) +
          z * ι ((fun _ : Fin 1 ↦ (1 : ZMod 2)) i)) P).card →
      differentialSpecialization
        (challengeSpecialization
          (MvPolynomial.map (Polynomial.mapRingHom ι)
            agreementEquation) z) P = 0 →
      HasExactCorrelatedPair pointDomain (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1) ι 2 z P := by
    intro z _ P hP hagree hroot
    have hpoly : P - C z = 0 := by
      simpa [agreementEquation, challengeSpecialization, differentialSpecialization,
        differentialSpecializationHom] using hroot
    have hPconst : P = C z := sub_eq_zero.mp hpoly
    subst P
    have hfull : polynomialAgreementSet (pointDomain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι ((fun _ : Fin 1 ↦ (0 : ZMod 2)) i) +
          z * ι ((fun _ : Fin 1 ↦ (1 : ZMod 2)) i)) (C z) = Finset.univ :=
      Finset.eq_univ_of_card _
        (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hagree))
    refine ⟨(0, 1), (by simpa using
      (show (⊥ : WithBot ℕ) < (2 : WithBot ℕ) by decide)), by norm_num, ?_, ?_⟩
    · simp [correlatedPairSpecialization]
    · rw [hfull]
      ext i
      fin_cases i
      simp [commonPolynomialAgreementSet, pointDomain]
  obtain ⟨exceptional, hcard, hdescend⟩ :=
    exists_exceptional_equation_correlatedAgreement_descend pointDomain
      (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1) ι
      agreementEquation 2 1 ∅ hgood
  have hex : exceptional = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
  have hroot : differentialSpecialization (challengeSpecialization
      agreementEquation 1) (C 1) = 0 := by
    simp [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom]
  have hpair := hdescend 1 (by simp [hex]) (C 1) (by simp) (by
    simp [pointDomain, polynomialAgreementSet]) hroot
  have hmappedRoot : differentialSpecialization
      (challengeSpecialization
        (MvPolynomial.map (Polynomial.mapRingHom ι) agreementEquation) (ι 1))
      (C (ι 1)) = 0 := by
    simp [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom]
  have hmappedAgreement : polynomialAgreementSet
      (pointDomain.trans ⟨ι, ι.injective⟩)
      (fun _ ↦ ι 0 + ι 1 * ι 1) (C (ι 1)) = Finset.univ := by
    ext i
    fin_cases i
    simp [polynomialAgreementSet, pointDomain]
  exact ⟨hnonzero, exceptional, hcard, hpair, hmappedRoot, hmappedAgreement⟩

end

private theorem singletonLineExactBound : LineExactAgreementBound pointDomain 1 1 0 := by
  intro f g
  refine ⟨∅, by simp, fun z _ P hP hclose ↦ ?_⟩
  have hagree :
      polynomialAgreementSet pointDomain (fun i ↦ f i + z * g i) P = Finset.univ :=
    Finset.eq_univ_of_card _
      (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hclose))
  have heval := (mem_polynomialAgreementSet ..).mp
    (hagree ▸ Finset.mem_univ (0 : Fin 1))
  have hcoeff : P.coeff 0 = f 0 + z * g 0 := by
    have hpoint : pointDomain 0 = 0 := rfl
    rw [hpoint] at heval
    exact (coeff_zero_eq_eval_zero P).trans heval
  have hPconst : P = C (f 0 + z * g 0) := by
    rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP), hcoeff]
  refine ⟨C (f 0), C (g 0), (degree_C_le).trans_lt (by norm_num),
    (degree_C_le).trans_lt (by norm_num), ?_, ?_⟩
  · calc
      P = C (f 0 + z * g 0) := hPconst
      _ = C (f 0) + C z * C (g 0) := by simp
  · rw [hagree]
    ext i
    fin_cases i
    simp [commonPolynomialAgreementSet, pointDomain]

private def affineValues : Fin 2 → Fin 1 → ZMod 2 := ![fun _ ↦ 1, fun _ ↦ 0]

example := exists_affine_exceptionalSet_full_agreement_of_exactLine pointDomain 0
  singletonLineExactBound 0 (by norm_num [pointDomain]) (by norm_num) affineValues

private def fullDomain : Fin 2 ↪ ℚ where
  toFun i := ((i : ℕ) : ℚ)
  inj' _i _j h := Fin.ext (Nat.cast_injective (R := ℚ) h)

private theorem affineCandidateEvaluation (i : Fin 2) :
    Polynomial.eval (fullDomain i) (C 1 + C 2 * X : ℚ[X]) =
      ![1, 2] i + 1 * ![0, 1] i := by
  fin_cases i
  · norm_num [fullDomain]
    change (0 : ℚ) = 0
    rfl
  · norm_num [fullDomain]
    change 1 + 2 * (1 : ℚ) = 3
    norm_num

/-- At challenge `1`, the candidate `1 + 2X` is explained by one pair on both coordinates. -/
example : ∃ F₀ G₀ : ℚ[X], C 1 + C 2 * X = F₀ + C 1 * G₀ ∧
    commonPolynomialAgreementSet fullDomain ![1, 2] ![0, 1] F₀ G₀ = univ := by
  obtain ⟨F₀, G₀, -, -, hpair⟩ :=
    exists_exactPair_fullDimension fullDomain ![1, 2] ![0, 1]
  have hagree : polynomialAgreementSet fullDomain (fun i ↦ ![1, 2] i + 1 * ![0, 1] i)
      (C 1 + C 2 * X) = univ := by
    ext i
    simpa only [mem_polynomialAgreementSet, Finset.mem_univ, iff_true] using
      affineCandidateEvaluation i
  obtain ⟨hP, hset⟩ := hpair 1 (C 1 + C 2 * X) (by
    rw [Fintype.card_fin]
    compute_degree!) (by rw [hagree, card_univ])
  exact ⟨F₀, G₀, hP, hset.symm.trans hagree⟩

/-- The graph-line recognizer accepts the computed candidate `1 + 2X` at challenge `1`. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 2 ∧ G₀.degree < 2 ∧
    (∀ i ∈ (Finset.univ : Finset (Fin 2)),
      F₀.eval (fullDomain i) = ![1, 2] i ∧ G₀.eval (fullDomain i) = ![0, 1] i) ∧
    Polynomial.eval (fullDomain 0) (C 1 + C 2 * X : ℚ[X]) = ![1, 2] 0 + 1 * ![0, 1] 0 ∧
    Polynomial.eval (fullDomain 1) (C 1 + C 2 * X : ℚ[X]) = ![1, 2] 1 + 1 * ![0, 1] 1 ∧
    C 1 + C 2 * X = F₀ + C 1 * G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hsample, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample fullDomain ![1, 2] ![0, 1] univ
      (card_univ.trans rfl)
  have hP : (C 1 + C 2 * X : ℚ[X]).degree < 2 := by compute_degree!
  have heval : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      Polynomial.eval (fullDomain i) (C 1 + C 2 * X : ℚ[X]) = ![1, 2] i + 1 * ![0, 1] i := by
    intro i hi
    exact affineCandidateEvaluation i
  exact ⟨F₀, G₀, hF₀, hG₀, hsample, heval 0 (by simp), heval 1 (by simp),
    by simpa using hrecognize (RingHom.id ℚ) 1 (C 1 + C 2 * X) hP heval⟩

/-- The exceptional bound is attained when the graph agrees at only one coordinate. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧ 0 ∈ exceptional := by
  obtain ⟨exceptional, hcard, hagreement⟩ :=
    exists_exceptional_graphLine_challenges fullDomain ![0, 0] ![0, 1]
      (0 : ℚ[X]) 0 (RingHom.id ℚ)
  have hcommon : commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 = {0} := by
    ext i
    fin_cases i <;> simp [commonPolynomialAgreementSet, fullDomain]
  have hcard' : exceptional.card ≤ 1 := by
    simpa [hcommon, Fintype.card_fin] using hcard
  have hzero : 0 ∈ exceptional := by
    by_contra hz
    have hset := hagreement 0 hz
    have hleft : polynomialAgreementSet fullDomain (fun _ : Fin 2 ↦ 0) (0 : ℚ[X]) = univ := by
      ext i
      simp [polynomialAgreementSet]
    have hzero : (fun i : Fin 2 ↦ ![0, 0] i) = fun _ ↦ (0 : ℚ) := by
      funext i
      fin_cases i <;> norm_num
    have hset'' : polynomialAgreementSet fullDomain (fun i : Fin 2 ↦ ![0, 0] i)
        (0 : ℚ[X]) = commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 := by
      simpa using hset
    have hset' : polynomialAgreementSet fullDomain (fun _ : Fin 2 ↦ 0) (0 : ℚ[X]) =
        commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 := by
      rw [← hzero]
      exact hset''
    rw [hleft, hcommon] at hset'
    have hone : (1 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
    rw [hset'] at hone
    simp at hone
  exact ⟨exceptional, hcard', hzero⟩

/-- A double root of `X²` kills the specialized singular tail. -/
example : singularTail (1 : ℚ[X]) (X ^ 2 : ℚ[X][X]) 2 = 0 := by
  have h := singularTail_map_eq_zero_of_common_root (1 : ℚ[X]) (X ^ 2 : ℚ[X][X]) two_pos
    (by simp) (RingHom.id ℚ[X]) 0 (by simp) (by simp)
  simpa using h

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

private abbrev componentVariable {E : Type*} [CommSemiring E] :
    MvPolynomial (Option (Fin 1)) E := X (some (0 : Fin 1))

private def componentIdeal {E : Type*} [CommSemiring E] :
    Ideal (MvPolynomial (Option (Fin 1)) E) := Ideal.span {componentVariable}

private abbrev ComponentField := AlgebraicClosure ℚ

private theorem componentIdeal_isPrime :
    (componentIdeal (E := ComponentField)).IsPrime := by
  change (Ideal.span {(X (some (0 : Fin 1)) :
    MvPolynomial (Option (Fin 1)) ComponentField)}).IsPrime
  exact (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime

private theorem componentIdeal_degree_pos :
    0 < (affineHilbertPolynomial (componentIdeal (E := ComponentField))).natDegree := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (f := componentVariable (E := ComponentField)) (X_ne_zero _) componentIdeal_isPrime.ne_top
  have hcard : Nat.card (Option (Fin 1)) = 2 := by simp
  have h' :
      (affineHilbertPolynomial (componentIdeal (E := ComponentField))).natDegree + 1 = 2 := by
    simpa [componentIdeal, componentVariable, hcard] using h
  omega

private theorem componentIdeal_one_notMem :
    (1 : MvPolynomial (Option (Fin 1)) ComponentField) ∉
      componentIdeal (E := ComponentField) := by
  intro h
  exact componentIdeal_isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

private theorem component_separant_notMem :
    jointInitialJetSeparant (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ∉ componentIdeal := by
  simpa [jointInitialJetSeparant, componentEquation, initialJetSeparant,
    separant, Fin.last] using componentIdeal_one_notMem

private theorem component_generator_mem :
    componentVariable (E := ComponentField) ∈ componentIdeal :=
  Ideal.subset_span (by simp)

private theorem component_initialEquation_mem :
    jointInitialJetEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ∈ componentIdeal := by
  change (optionEquivRight ComponentField (Fin 1)).symm
    (initialJetEquation (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField))) ∈ componentIdeal
  rw [show initialJetEquation (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) =
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (Polynomial ComponentField)) by
    simp [initialJetEquation, componentEquation]]
  simp only [optionEquivRight_symm_X]
  exact component_generator_mem

private theorem component_initialEquation_ne_zero :
    jointInitialJetEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ≠ 0 := by
  have heq : jointInitialJetEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) = componentVariable := by
    change (optionEquivRight ComponentField (Fin 1)).symm
      (initialJetEquation (Polynomial.C (0 : ComponentField))
        (componentEquation (E := ComponentField))) = _
    rw [show initialJetEquation (Polynomial.C (0 : ComponentField))
        (componentEquation (E := ComponentField)) =
          (MvPolynomial.X (0 : Fin 1) :
            MvPolynomial (Fin 1) (Polynomial ComponentField)) by
      simp [initialJetEquation, componentEquation]]
    simp only [optionEquivRight_symm_X, componentVariable]
  rw [heq]
  exact X_ne_zero _

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

private abbrev componentHighNumerator : MvPolynomial (Option (Fin 1)) ComponentField :=
  jointCommonTaylorNumerator (r := 0) (0 : ComponentField)
    (componentEquation (E := ComponentField)) 2 (1 : Fin 2)

private theorem component_highNumerator_eq :
    componentHighNumerator = componentVariable (E := ComponentField) := by
  rw [componentHighNumerator, jointCommonTaylorNumerator]
  change (optionEquivRight ComponentField (Fin 1)).symm
      (commonTaylorNumeratorOver ComponentField (Polynomial.C (0 : ComponentField))
        (componentEquation (E := ComponentField)) 2 1) = componentVariable
  rw [component_commonNumerator_one]
  simp [componentVariable]

private theorem component_highNumerator_mem : componentHighNumerator ∈ componentIdeal := by
  rw [component_highNumerator_eq]
  exact component_generator_mem

private theorem component_highNumerator_ne_zero : componentHighNumerator ≠ 0 := by
  rw [component_highNumerator_eq]
  exact X_ne_zero _

private theorem component_highCuts : ∀ l : Fin 2, 1 ≤ l.val →
    jointCommonTaylorNumerator (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 2 l ∈ componentIdeal := by
  intro l hl
  have hl1 : l = 1 := Fin.ext (by omega)
  subst l
  exact component_highNumerator_mem

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
  intro i hi
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst i
  have hd0 : domain (0 : Fin 1) = 0 := rfl
  have hxval : Polynomial.C ((algebraMap ℚ ComponentField) (domain 0)) =
      (0 : ComponentField[X]) := by
    rw [hd0]
    simp
  have hyval : Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) +
      Polynomial.X * Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) =
        (0 : ComponentField[X]) := by simp [componentWord]
  change (optionEquivRight ComponentField (Fin 1)).symm
    (taylorAgreementEquationOver (F := ComponentField) (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) 2
      (Polynomial.C ((algebraMap ℚ ComponentField) (domain 0)))
      (Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) +
        Polynomial.X * Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)))
      (τ := 2)) ∈ componentIdeal
  rw [hxval, hyval, component_cut_eq]
  exact component_initialEquation_mem

private abbrev firstOrderChartEquation : DifferentialPolynomial ComponentField 1 :=
  MvPolynomial.X (Fin.last 1)

private abbrev firstOrderSourceEquation : DifferentialPolynomial ComponentField[X] 1 :=
  MvPolynomial.X (some (Fin.last 1))

private def firstOrderChartIdeal : Ideal (ChartRing 1 ComponentField) :=
  Ideal.span {(MvPolynomial.X (Fin.last 1) : ChartRing 1 ComponentField)}

private def firstOrderSourceIdeal : Ideal (SourceRing 1 ComponentField) :=
  Ideal.span {(MvPolynomial.X (some (Fin.last 1)) : SourceRing 1 ComponentField)}

private def firstOrderTestPoints : Fin 1 ↪ ComponentField :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def firstOrderChartValues : Fin 1 → ComponentField := fun _ ↦ 0

private abbrev firstOrderChartCut (i : Fin 1) : ChartRing 1 ComponentField :=
  taylorAgreementEquation (0 : ComponentField) firstOrderChartEquation 2 2
    (firstOrderTestPoints i) (firstOrderChartValues i)

private abbrev firstOrderSourceCut (i : Fin 1) : SourceRing 1 ComponentField :=
  jointTaylorAgreementEquation (0 : ComponentField) firstOrderSourceEquation 2 2
    (Polynomial.C (firstOrderTestPoints i)) 0

private theorem firstOrderChartIdeal_isPrime : firstOrderChartIdeal.IsPrime := by
  change (Ideal.span {(MvPolynomial.X (Fin.last 1) : ChartRing 1 ComponentField)}).IsPrime
  exact (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime

private theorem firstOrderSourceIdeal_isPrime : firstOrderSourceIdeal.IsPrime := by
  change
    (Ideal.span {(MvPolynomial.X (some (Fin.last 1)) : SourceRing 1 ComponentField)}).IsPrime
  exact (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime

private theorem firstOrderChartIdeal_one_notMem : (1 : ChartRing 1 ComponentField) ∉
    firstOrderChartIdeal := by
  intro h
  exact firstOrderChartIdeal_isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

private theorem firstOrderSourceIdeal_one_notMem : (1 : SourceRing 1 ComponentField) ∉
    firstOrderSourceIdeal := by
  intro h
  exact firstOrderSourceIdeal_isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

private theorem firstOrderChartSeparant_notMem :
    initialJetSeparant (0 : ComponentField) firstOrderChartEquation ∉ firstOrderChartIdeal := by
  simpa [firstOrderChartEquation, initialJetSeparant, initialJetEquation, separant] using
    firstOrderChartIdeal_one_notMem

private theorem firstOrderSourceSeparant_notMem :
    jointInitialJetSeparant (0 : ComponentField) firstOrderSourceEquation ∉
      firstOrderSourceIdeal := by
  simpa [jointInitialJetSeparant, firstOrderSourceEquation, initialJetSeparant,
    initialJetEquation, separant] using firstOrderSourceIdeal_one_notMem

private theorem firstOrderChartHighNumerator :
    commonTaylorNumerator (0 : ComponentField) firstOrderChartEquation 2 1 =
      (MvPolynomial.X (Fin.last 1) : ChartRing 1 ComponentField) := by
  simp [commonTaylorNumerator, rationalTaylorNumerator, firstOrderChartEquation,
    initialJetSeparant, separant]

private theorem firstOrderSourceHighNumerator :
    jointCommonTaylorNumerator (0 : ComponentField) firstOrderSourceEquation 2
      (1 : Fin 2) =
        (MvPolynomial.X (some (Fin.last 1)) : SourceRing 1 ComponentField) := by
  simp [jointCommonTaylorNumerator, commonTaylorNumeratorOver, rationalTaylorNumeratorOver,
    firstOrderSourceEquation, initialJetSeparant, separant]

private theorem firstOrderChartHigh : ∀ l : Fin 2, 1 ≤ l.val →
    commonTaylorNumerator (0 : ComponentField) firstOrderChartEquation 2 l.val ∈
      firstOrderChartIdeal := by
  intro l hl
  have h : l = 1 := Fin.ext (by omega)
  subst l
  change commonTaylorNumerator (0 : ComponentField) firstOrderChartEquation 2 1 ∈ _
  rw [firstOrderChartHighNumerator]
  exact Ideal.subset_span (by simp)

private theorem firstOrderSourceHigh : ∀ l : Fin 2, 1 ≤ l.val →
    jointCommonTaylorNumerator (0 : ComponentField) firstOrderSourceEquation 2 l ∈
      firstOrderSourceIdeal := by
  intro l hl
  have h : l = 1 := Fin.ext (by omega)
  subst l
  change jointCommonTaylorNumerator (0 : ComponentField) firstOrderSourceEquation 2
    (1 : Fin 2) ∈ _
  rw [firstOrderSourceHighNumerator]
  exact Ideal.subset_span (by simp)

private theorem firstOrderChartIdeal_degree :
    (affineHilbertPolynomial firstOrderChartIdeal).natDegree = 1 := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (f := (MvPolynomial.X (Fin.last 1) : ChartRing 1 ComponentField)) (X_ne_zero _)
    firstOrderChartIdeal_isPrime.ne_top
  have hc : Nat.card (Fin 2) = 2 := by simp
  have h' : (affineHilbertPolynomial firstOrderChartIdeal).natDegree + 1 = 2 := by
    simpa [firstOrderChartIdeal, hc] using h
  omega

private theorem firstOrderSourceIdeal_degree :
    (affineHilbertPolynomial firstOrderSourceIdeal).natDegree = 2 := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (f := (MvPolynomial.X (some (Fin.last 1)) : SourceRing 1 ComponentField))
    (X_ne_zero _) firstOrderSourceIdeal_isPrime.ne_top
  have hc : Nat.card (Option (Fin 2)) = 3 := by simp
  have h' : (affineHilbertPolynomial firstOrderSourceIdeal).natDegree + 1 = 3 := by
    simpa [firstOrderSourceIdeal, hc] using h
  omega

/-- Every regular point of a prime component lies on the graph returned by recognition. -/
example :
    ∃ P₀ P₁ : ℚ[X],
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 0 ∧
      componentHighNumerator ∈ componentIdeal ∧ componentHighNumerator ≠ 0 ∧
      ∀ x, x ∈ zeroLocus ComponentField (componentIdeal (E := ComponentField)) ∧
        aeval x (jointInitialJetSeparant (r := 0) (0 : ComponentField)
          (componentEquation (E := ComponentField))) ≠ 0 →
          ∃ z : ComponentField, x = fun i ↦
            (affinePairCurve (r := 0) 0
              (P₀.map (algebraMap ℚ ComponentField))
              (P₁.map (algebraMap ℚ ComponentField)) i).eval z := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  have hcomponent := exists_graphLine_pair_of_regular_component
    (domain := domain) (f := componentWord) (g := componentWord) (sample := Finset.univ)
    (hsample := by simp) (iota := algebraMap ℚ ComponentField) (center := 0)
    (Q := componentEquation (E := ComponentField)) (hK := by omega) (τ := 2)
    (hτ := by intro l; omega) (P := componentIdeal (E := ComponentField))
    (hs := component_separant_notMem) (hd := componentIdeal_degree_pos)
    (hinit := component_initialEquation_mem) (hhigh := component_highCuts)
    (hcuts := component_agreementCuts)
  obtain ⟨P₀, P₁, -, -, hsample, hgraph, -, -, -, -, -⟩ := hcomponent
  have hd0 : domain (0 : Fin 1) = 0 := rfl
  refine ⟨P₀, P₁,
    by simpa [componentWord, hd0] using (hsample 0 (by simp)).1,
    by simpa [componentWord, hd0] using (hsample 0 (by simp)).2,
    component_highNumerator_mem, component_highNumerator_ne_zero,
    ?_⟩
  intro x hx
  exact hgraph x hx

/-- A regular component supported on its agreement set yields a pair with that agreement. -/
example :
    ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 0 ∧
      1 ≤ (commonPolynomialAgreementSet domain componentWord componentWord P₀ P₁).card := by
  classical
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  have hcomponent := exists_graphLine_pair_of_regular_component_agreements
    (n := 1) (k := 1) (K := 2) (r := 0) (L := 1) (domain := domain)
    (f := componentWord) (g := componentWord) (indices := Finset.univ)
    (hcard := by simp) (hkL := by omega) (iota := algebraMap ℚ ComponentField)
    (center := 0) (Q := componentEquation (E := ComponentField)) (hK := by omega)
    (τ := 2) (hτ := by intro l; omega) (P := componentIdeal (E := ComponentField))
    (hs := component_separant_notMem) (hd := componentIdeal_degree_pos)
    (hinit := component_initialEquation_mem) (hhigh := component_highCuts)
    (hcuts := component_agreementCuts)
  obtain ⟨P₀, P₁, hP₀, hP₁, hcard, -, -, -, -, -, -⟩ := hcomponent
  have hfull : commonPolynomialAgreementSet domain componentWord componentWord P₀ P₁ =
      Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _)
      (by simpa [Fintype.card_fin] using hcard))
  have hmem : (0 : Fin 1) ∈
      commonPolynomialAgreementSet domain componentWord componentWord P₀ P₁ := by
    rw [hfull]
    simp
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, ?_, hcard⟩
  · simpa [componentWord, domain_zero] using
      (mem_commonPolynomialAgreementSet domain componentWord componentWord P₀ P₁ 0).mp hmem |>.1
  · simpa [componentWord, domain_zero] using
      (mem_commonPolynomialAgreementSet domain componentWord componentWord P₀ P₁ 0).mp hmem |>.2

/-- A polynomial-valued received word with a proved cut gives a concrete source prime bound. -/
example :
    (affineHilbertPolynomial (componentIdeal (E := ComponentField))).natDegree ≤ 1 := by
  let α : Fin 1 ↪ ComponentField :=
    ⟨fun i ↦ algebraMap ℚ ComponentField (domain i),
      fun _ _ _ ↦ Subsingleton.elim _ _⟩
  let f : Fin 1 → ComponentField := fun i ↦ algebraMap ℚ ComponentField (componentWord i)
  let g : Fin 1 → ComponentField := fun i ↦ algebraMap ℚ ComponentField (componentWord i)
  have hcut : ∀ i,
      jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
        (componentEquation (E := ComponentField)) 2 2 (Polynomial.C (α i))
        (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) ∈ componentIdeal := by
    intro i
    simpa [α, f, g] using component_agreementCuts i (Finset.mem_univ i)
  have hbound :=
    symbolicSource_prime_affineHilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent
    (center := (0 : ComponentField))
    (Q := componentEquation (E := ComponentField)) (K := 2) (k := 1) (c := 1)
    (τ := 2) (by intro l; omega) (by omega) (by omega) (by omega)
    componentIdeal componentIdeal_isPrime component_separant_notMem component_highCuts α
    (received := fun i ↦ Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) hcut
  simpa using hbound

/-- A retained chart prime with one nonempty agreement cut has degree zero. -/
example :
    (affineHilbertPolynomial
      (Ideal.span {(MvPolynomial.X (0 : Fin 1) : ChartRing 0 ComponentField)})).natDegree ≤
        0 := by
  let Q : DifferentialPolynomial ComponentField 0 := MvPolynomial.X (0 : Fin 1)
  let P : Ideal (ChartRing 0 ComponentField) :=
    Ideal.span {(MvPolynomial.X (0 : Fin 1) : ChartRing 0 ComponentField)}
  let α : Fin 1 ↪ ComponentField :=
    ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  let y : Fin 1 → ComponentField := fun _ ↦ 0
  have hP : P.IsPrime := by
    change (Ideal.span {(MvPolynomial.X (0 : Fin 1) : ChartRing 0 ComponentField)}).IsPrime
    exact (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hsep : initialJetSeparant (0 : ComponentField) Q ∉ P := by
    have hone : (1 : ChartRing 0 ComponentField) ∉ P := by
      intro h
      exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    simpa [Q, initialJetSeparant, initialJetEquation, separant] using hone
  have hcut : ∀ i, taylorAgreementEquation (0 : ComponentField) Q 1
      (α i) (y i) (τ := 0) ∈ P := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change taylorAgreementEquation (0 : ComponentField) Q 1 0 0 (τ := 0) ∈ P
    have heq : taylorAgreementEquation (0 : ComponentField) Q 1 0 0 (τ := 0) =
        (MvPolynomial.X (0 : Fin 1) : ChartRing 0 ComponentField) := by
      simp [taylorAgreementEquation, commonTaylorNumerator, rationalTaylorNumerator,
        Q, initialJetSeparant, separant]
    rw [heq]
    exact Ideal.subset_span (by simp)
  have hbound := chart_prime_affineHilbertPolynomial_natDegree_le_of_agreements_of_exponent
    (center := (0 : ComponentField)) (Q := Q) (K := 1) (k := 1) (c := 1) (τ := 0)
    (by intro l; fin_cases l; decide) (by omega) (by omega) P hP hsep
    (by intro l hl; fin_cases l; omega) α y hcut
  simpa using hbound

/-- The positive-dimensional chart and source bounds include empty-cut boundary cases; the chart
bound forces the cut count to zero. -/
example :
    (affineHilbertPolynomial firstOrderChartIdeal).natDegree +
        {i : Fin 1 | firstOrderChartCut i ∈ firstOrderChartIdeal}.ncard ≤ 1 ∧
      (affineHilbertPolynomial firstOrderSourceIdeal).natDegree +
        {i : Fin 1 | firstOrderSourceCut i ∈ firstOrderSourceIdeal}.ncard ≤ 2 ∧
      (affineHilbertPolynomial firstOrderSourceIdeal).natDegree = 2 ∧
      {i : Fin 1 | firstOrderSourceCut i ∈ firstOrderSourceIdeal}.ncard = 0 := by
  have hτ : TaylorExponentSufficient 1 2 2 := by
    intro l
    fin_cases l <;> omega
  have hchart := chart_dimensionSensitive_component_of_exponent
    (center := (0 : ComponentField)) (Q := firstOrderChartEquation) (K := 2) (k := 1)
    (n := 1) (τ := 2) hτ (by omega) (by omega) firstOrderChartIdeal
    firstOrderChartIdeal_isPrime firstOrderChartSeparant_notMem firstOrderChartHigh
    firstOrderTestPoints firstOrderChartValues
    (by rw [firstOrderChartIdeal_degree]; omega)
  have hsource := symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
    (center := (0 : ComponentField)) (Q := firstOrderSourceEquation) (K := 2) (k := 1)
    (n := 1) (τ := 2) hτ (by omega) (by omega) firstOrderSourceIdeal
    firstOrderSourceIdeal_isPrime firstOrderSourceSeparant_notMem firstOrderSourceHigh
    firstOrderTestPoints
    (fun _ ↦ 0)
  have hline := symbolicSource_dimensionSensitive_component_of_exponent
    (center := (0 : ComponentField)) (Q := firstOrderSourceEquation) (K := 2) (k := 1)
    (n := 1) (τ := 2) hτ (by omega) (by omega) firstOrderSourceIdeal
    firstOrderSourceIdeal_isPrime firstOrderSourceSeparant_notMem firstOrderSourceHigh
    firstOrderTestPoints (fun _ ↦ 0) (fun _ ↦ 0)
  have hfirst := firstOrder_symbolicSource_dimensionSensitive_component_of_exponent
    (center := (0 : ComponentField)) (Q := firstOrderSourceEquation) (K := 2) (n := 1)
    (τ := 2) hτ (by omega) firstOrderSourceIdeal firstOrderSourceIdeal_isPrime
    firstOrderSourceSeparant_notMem firstOrderSourceHigh firstOrderTestPoints
    (fun _ ↦ 0) (fun _ ↦ 0)
  have hlineZero := hline.2 (by rw [firstOrderSourceIdeal_degree]; omega)
  have hfirstZero := hfirst.2 (by rw [firstOrderSourceIdeal_degree]; omega)
  have hsourceTotal :
      (affineHilbertPolynomial firstOrderSourceIdeal).natDegree +
        {i : Fin 1 | firstOrderSourceCut i ∈ firstOrderSourceIdeal}.ncard ≤ 2 := by
    have hcount : {i : Fin 1 | firstOrderSourceCut i ∈ firstOrderSourceIdeal}.ncard ≤ 0 := by
      rw [firstOrderSourceIdeal_degree] at hlineZero
      simpa [firstOrderSourceCut, firstOrderTestPoints] using hlineZero
    have hcountZero := Nat.eq_zero_of_le_zero hcount
    rw [hcountZero, Nat.add_zero]
    exact hsource.1
  have hfirstCount :
      {i : Fin 1 | firstOrderSourceCut i ∈ firstOrderSourceIdeal}.ncard = 0 := by
    simpa [firstOrderSourceCut, firstOrderTestPoints] using hfirstZero
  exact ⟨hchart, hsourceTotal, firstOrderSourceIdeal_degree, hfirstCount⟩

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
  have hreceived :
      Polynomial.C ((algebraMap ℚ ComponentField) (componentWord i)) +
        Polynomial.X * Polynomial.C
          ((algebraMap ℚ ComponentField) (componentWord i)) = 0 := by
    simp [componentWord]
  have hpair := component_agreementCuts i hi
  rw [hreceived] at hpair
  rw [hbatch]
  exact hpair

/-- A positive-dimensional prime component determines one base-field tuple whose graph contains
its regular points, with nonzero restricted separant. -/
example :
    ∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
      (∀ i ∈ Finset.univ, ∀ t, (P t).eval (domain i) = componentWord i) ∧
      (∀ x ∈ {x | x ∈ zeroLocus ComponentField
          (componentIdeal (E := ComponentField)) ∧
        aeval x (jointInitialJetSeparant (r := 0) (0 : ComponentField)
              (componentEquation (E := ComponentField))) ≠ 0},
        x = fun i ↦ (powerBatchedJetGraphMap (r := 0) 0
          (fun t ↦ (P t).map (algebraMap ℚ ComponentField)) i).eval (x none)) ∧
      aeval (powerBatchedJetGraphMap (r := 0) 0
        (fun t ↦ (P t).map (algebraMap ℚ ComponentField)))
        (jointInitialJetSeparant (r := 0) (0 : ComponentField)
          (componentEquation (E := ComponentField))) ≠ 0 := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  obtain ⟨P, hP, hsample, hgraph, -, -, hsep⟩ :=
    exists_polynomialGraph_of_primeTaylorComponent (domain := domain)
      (w := fun _ : Fin 2 ↦ fun i ↦ componentWord i)
      (sample := Finset.univ) (hsample := by simp)
      (φ := algebraMap ℚ ComponentField) (center := 0)
      (Q := componentEquation (E := ComponentField)) (hK := by omega) (τ := 2)
      (hτ := by intro l; fin_cases l <;> omega)
      (I := componentIdeal (E := ComponentField)) (hsep := component_separant_notMem)
      (hdim := componentIdeal_degree_pos) (hhigh := component_highCuts)
      (hcuts := component_powerBatchedAgreementCuts)
  exact ⟨P, hP, hsample, hgraph, hsep⟩

/-- The prime component's joint cut forces the tuple's value at its evaluation point. -/
example : ∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
    ∀ t, (P t).eval (domain 0) = componentWord 0 := by
  classical
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  obtain ⟨P, hP, _, hgraph, hpoly, _, _⟩ :=
    exists_polynomialGraph_of_primeTaylorComponent (domain := domain)
      (w := fun _ : Fin 2 ↦ componentWord) (sample := Finset.univ) (hsample := by simp)
      (φ := algebraMap ℚ ComponentField) (center := 0)
      (Q := componentEquation (E := ComponentField)) (hK := by omega) (τ := 2)
      (hτ := by intro l; fin_cases l <;> omega)
      (I := componentIdeal (E := ComponentField)) (hsep := component_separant_notMem)
      (hdim := componentIdeal_degree_pos) (hhigh := component_highCuts)
      (hcuts := component_powerBatchedAgreementCuts)
  have hagreement := commonCurveAgreement_of_jointTaylorAgreementEquation_mem_prime
    (n := 1) (K := 2) (r := 0) (ℓ := 1) (domain := domain)
    (w := fun _ : Fin 2 ↦ componentWord) (ιₑ := algebraMap ℚ ComponentField)
    (center := 0) (Q := componentEquation (E := ComponentField)) (τ := 2)
    (hτ := by intro l; omega) (I := componentIdeal (E := ComponentField))
    (hsep := component_separant_notMem) (hdim := componentIdeal_degree_pos) (P := P)
    (hgraph := hgraph) (hpoly := hpoly) (i := 0)
    (hcut := component_powerBatchedAgreementCuts 0 (by simp))
  exact ⟨P, hP, hagreement⟩

noncomputable local instance graphComponentDecidableEq : DecidableEq ℚ := Classical.decEq _

open Classical in
/-- One joint agreement cut for a two-entry tuple yields a common agreement. -/
example : ∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
    1 ≤ (commonCurveAgreementSet domain (fun _ : Fin 2 ↦ componentWord) P).card := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  obtain ⟨P, hP, hcommon, -, -, -, -⟩ :=
    exists_polynomialGraph_of_primeTaylorComponent_agreements (n := 1) (k := 1) (K := 2)
      (r := 0) (ℓ := 1) (L := 1) (domain := domain)
      (w := fun _ : Fin 2 ↦ componentWord) (indices := Finset.univ)
      (hcard := by simp) (hkL := by omega) (ιₑ := algebraMap ℚ ComponentField)
      (center := 0) (Q := componentEquation (E := ComponentField)) (hK := by omega)
      (τ := 2) (hτ := by intro l; omega)
      (I := componentIdeal (E := ComponentField)) (hsep := component_separant_notMem)
      (hdim := componentIdeal_degree_pos) (hhigh := component_highCuts)
      (hcuts := component_powerBatchedAgreementCuts)
  exact ⟨P, hP, hcommon⟩

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
  ⟨fun i ↦ (i.val : ZMod 3), by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · norm_num at hij
    · fin_cases j
      · norm_num at hij
      · rfl⟩

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

/-- The common agreement set computed with the classical equality decision. -/
private def classicalAgreementSet (domain : Fin 2 ↪ ZMod 3) (w : Fin 2 → Fin 2 → ZMod 3)
    (P : Fin 2 → Polynomial (ZMod 3)) : Finset (Fin 2) :=
  @commonCurveAgreementSet (ZMod 3) (Fin 2) _ 1 (Classical.decEq _) _ domain w P

/-- The common agreement set after extension to `E₉`. -/
private def extensionCommonAgreementSet (domain : Fin 2 ↪ E₉)
    (w : Fin 2 → Fin 2 → E₉) (P : Fin 2 → Polynomial E₉) : Finset (Fin 2) :=
  @commonCurveAgreementSet E₉ (Fin 2) _ 1 (Classical.decEq _) _ domain w P

/-- The polynomial agreement set after extension to `E₉`. -/
private def extensionPolynomialAgreementSet (domain : Fin 2 ↪ E₉)
    (w : Fin 2 → E₉) (P : Polynomial E₉) : Finset (Fin 2) :=
  @polynomialAgreementSet E₉ _ (Classical.decEq _) (Fin 2) _ domain w P

/-- A two-component tuple has one exceptional challenge; scalar extension preserves its concrete
common agreement set. -/
example :
    ∃ exceptional : Finset E₉, exceptional.card ≤ 1 ∧
      (∀ z ∉ exceptional,
        extensionPolynomialAgreementSet
          (exceptionalDomain.trans ⟨algebraMap (ZMod 3) E₉,
            (algebraMap (ZMod 3) E₉).injective⟩)
          (powerBatchedWord (fun t i ↦ algebraMap (ZMod 3) E₉ (exceptionalWords t i)) z)
          (powerBatchedPolynomial
            (fun t ↦ (exceptionalPolynomials t).map (algebraMap (ZMod 3) E₉)) z) =
        classicalAgreementSet exceptionalDomain exceptionalWords exceptionalPolynomials) ∧
      classicalAgreementSet exceptionalDomain exceptionalWords exceptionalPolynomials =
        ({0} : Finset (Fin 2)) ∧
      extensionCommonAgreementSet
          (exceptionalDomain.trans ⟨algebraMap (ZMod 3) E₉,
            (algebraMap (ZMod 3) E₉).injective⟩)
          (fun t i ↦ algebraMap (ZMod 3) E₉ (exceptionalWords t i))
          (fun t ↦ (exceptionalPolynomials t).map (algebraMap (ZMod 3) E₉)) =
        classicalAgreementSet exceptionalDomain exceptionalWords exceptionalPolynomials := by
  have hbase : classicalAgreementSet exceptionalDomain exceptionalWords
      exceptionalPolynomials = ({0} : Finset (Fin 2)) := by
    ext i
    fin_cases i
    · simp only [classicalAgreementSet, commonCurveAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _
        trivial
      · intro _ t
        fin_cases t <;> simp [exceptionalWords, exceptionalPolynomials, exceptionalDomain]
    · simp only [classicalAgreementSet, commonCurveAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have hbad := h 1
        norm_num [exceptionalWords, exceptionalPolynomials, exceptionalDomain] at hbad
      · intro h
        have : False := (by decide : (1 : Fin 2) ≠ 0) h
        exact False.elim this
  have hcommon : 1 ≤ (classicalAgreementSet exceptionalDomain exceptionalWords
      exceptionalPolynomials).card := by
    rw [hbase]
    simp
  let ι : ZMod 3 →+* E₉ := algebraMap (ZMod 3) E₉
  obtain ⟨exceptional, hbound, hgood⟩ :=
    exists_exceptional_powerBatched_extension exceptionalDomain exceptionalWords
      exceptionalPolynomials ι 1 hcommon
  have hbound' : exceptional.card ≤ 1 := by
    simpa using hbound
  refine ⟨exceptional, hbound', ?_, hbase, ?_⟩
  · intro z hz
    exact hgood z hz
  · exact commonCurveAgreementSet_map exceptionalDomain exceptionalWords exceptionalPolynomials
      ι

/-- Batching `X^2` with twice `X + 1` at `z = 2` has initial jet `(5, 4)` at `1` in `ℚ`.
-/
example :
    polynomialJet (d := 1) (1 : ℚ)
      (powerBatchedPolynomial (fun i : Fin 2 ↦
        if i = 0 then (Polynomial.X ^ 2 : Polynomial ℚ) else Polynomial.X + 1) 2) =
      ![5, 4] := by
  rw [polynomialJet_powerBatched]
  ext j
  fin_cases j <;> norm_num [powerBatchedJetGraph, powerBatchedCoordinate_eval,
    powerBatchedCoordinate, polynomialJet, Polynomial.hasseJet, Fin.sum_univ_succ]

/-- A sample with a nonzero second component and a nontrivial high cut yields all three
recognition conclusions at the regular chart point. -/
example :
    ∃ P : Fin 2 → Polynomial (ZMod 3),
      (∀ t, (P t).degree < 1) ∧
      (∀ i ∈ ({0} : Finset (Fin 1)), ∀ t,
        (P t).eval (domain i) = recognitionWords t i) ∧
      rationalTaylorPolynomial (0 : ZMod 3) recognitionChartAt 2 recognitionJet =
        powerBatchedPolynomial (fun t ↦ (P t).map (RingHom.id _)) 1 ∧
      (recognitionJet = fun j ↦ Polynomial.eval 1
        (powerBatchedJetGraph (r := 0) (0 : ZMod 3)
          (fun t ↦ (P t).map (RingHom.id _)) j)) ∧
      ∀ l : Fin 2,
        MvPolynomial.aeval recognitionJet
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
  have hsolution :
      differentialSpecialization recognitionChartAt (0 : Polynomial (ZMod 3)) = 0 := by
    simp [recognitionChartAt, recognitionChart, differentialSpecialization,
      differentialSpecializationHom]
  have hseparant : jetEvaluation (separant recognitionChartAt (Fin.last 0)) 0
      (polynomialJet 0 (0 : Polynomial (ZMod 3))) ≠ 0 := by
    simp [recognitionChartAt, recognitionChart, separant, jetEvaluation, polynomialJet,
      Polynomial.hasseJet]
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val →
      MvPolynomial.aeval recognitionJet
        (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 l.val) = 0 := by
    intro l hl
    fin_cases l
    · simp at hl
    · have hjetZero : recognitionJet = polynomialJet 0 (0 : Polynomial (ZMod 3)) := by
        funext j
        fin_cases j
        simp [recognitionJet, polynomialJet, Polynomial.hasseJet]
      have hcoeff : rationalTaylorCoefficient (0 : ZMod 3) recognitionChartAt
          recognitionJet 1 = 0 := by
        rw [hjetZero, rationalTaylorCoefficient_eq_solution (0 : ZMod 3)
          recognitionChartAt (0 : Polynomial (ZMod 3)) hsolution hseparant 1 (by
            intro i hir hi
            have : i = 1 := by omega
            subst i
            norm_num)]
        simp
      have hcoeffZero : MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
          (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0 := by
        change MvPolynomial.aeval recognitionJet
          (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0
        exact aeval_commonTaylorNumerator_eq_zero (0 : ZMod 3) recognitionChartAt
          recognitionJet 4 hS hcoeff
      change MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
        (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0
      exact hcoeffZero
  have hcuts : ∀ i ∈ ({0} : Finset (Fin 1)),
      MvPolynomial.aeval recognitionJet
        (taylorAgreementEquation (0 : ZMod 3) recognitionChartAt 2 4
          (RingHom.id _ (domain i))
          (Polynomial.eval 1
            (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t i))))) =
        0 := by
    intro i hi
    fin_cases i
    apply (taylorAgreementEquation_eq_zero_iff (0 : ZMod 3) recognitionChartAt
      (taylorExponentSufficient_two_mul 0 2) recognitionJet hS
      (RingHom.id _ (domain 0))
      (Polynomial.eval 1
          (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t 0))))).2
    have hc0 : rationalTaylorCoefficient (0 : ZMod 3) recognitionChartAt
        recognitionJet 0 = recognitionJet 0 := by
      simpa using rationalTaylorCoefficient_initial (0 : ZMod 3) recognitionChartAt
        recognitionJet ⟨0, by omega⟩
    have hy : Polynomial.eval 1
        (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t 0))) = 0 := by
      rw [powerBatchedCoordinate_eval]
      norm_num [recognitionWords, Fin.sum_univ_succ]
      exact ZMod.natCast_self 3
    have hx : RingHom.id (ZMod 3) (domain (0 : Fin 1)) = 0 := by
      rfl
    calc
      (rationalTaylorPolynomial (0 : ZMod 3) recognitionChartAt 2 recognitionJet).eval
          (RingHom.id _ (domain 0)) = 0 := by
        rw [eval_rationalTaylorPolynomial]
        simp [hc0, recognitionJet, Fin.sum_univ_succ, hx]
      _ = Polynomial.eval 1
          (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t 0))) :=
        hy.symm
  obtain ⟨hpoly, hjet, hcoeff⟩ := hrecognize 1 recognitionJet hS hhigh hcuts
  exact ⟨P, hP, hs, hpoly, hjet, hcoeff⟩

local instance : DecidableEq (ZMod 3) := Classical.decEq _

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
  rcases hP with hP | hP
  · subst P
    fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue]
      exact WithBot.bot_lt_coe 2
    · simp [batchedTuple]
  · subst P
    fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue]
      exact WithBot.bot_lt_coe 2
    · apply (Polynomial.degree_add_le _ _).trans_lt
      exact max_lt (Polynomial.degree_C_le.trans_lt (by norm_num)) (by simp)

private theorem candidateFamily_common :
    ∀ P ∈ candidateFamily,
      1 ≤ (commonCurveAgreementSet domain batchedWords P).card := by
  intro P hP
  simp only [candidateFamily, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with hP | hP
  · subst P
    have hmem : (0 : Fin 1) ∈
        commonCurveAgreementSet domain batchedWords batchedTuple := by
      rw [mem_commonCurveAgreementSet]
      intro t
      fin_cases t <;> simp [batchedTuple, batchedWords, domain]
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨0, hmem⟩)
  · subst P
    have hmem : (0 : Fin 1) ∈
        commonCurveAgreementSet domain batchedWords alternateBatchedTuple := by
      rw [mem_commonCurveAgreementSet]
      intro t
      fin_cases t
      · rw [domain_zero]
        simp [alternateBatchedTuple, batchedWords]
      · rw [domain_zero]
        simp [alternateBatchedTuple, batchedWords]
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨0, hmem⟩)

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
    ∀ z ∉ exceptional, ∀ Q, zeroCandidate z Q → Q.degree < 1 →
      HasExactPowerAgreement (ℓ := 1) domain zeroWords
        (RingHom.id (ZMod 3)) 1 z Q := by
  classical
  have h := exists_geometricTransfer_exceptional
    (α := Fin 1) (ν := PUnit) (k := 1) (ℓ := 1) (L := 0) (A := 0)
    domain zeroWords (RingHom.id (ZMod 3)) zeroCandidate ∅
    (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ ∅) (fun _ ↦ retainedZeroTuple)
    (by intro s; simp)
    (by intro s; simp [retainedZeroTuple, dimensionSensitiveIncidenceProduct])
    (by
      intro s P hP t
      simp only [retainedZeroTuple, Finset.mem_singleton] at hP
      rw [hP]
      simp [zeroTuple])
    (by intro s P hP; simp)
    (by
      intro z Q hQ hQdegree hA hz
      right
      refine ⟨(), zeroTuple, ?_, ?_⟩
      · simp [retainedZeroTuple]
      · rw [hQ]
        simp [zeroTuple, powerBatchedPolynomial])
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
      (exceptional := ∅) (bound := 0) (by simp) (by
        intro z hz Q hQ
        subst Q
        refine ⟨zeroTuple, ?_, ?_, ?_⟩
        · intro t
          simp [zeroTuple]
        · simp [zeroTuple, powerBatchedPolynomial]
        · ext i
          simp [zeroWords, zeroTuple, commonCurveAgreementSet, polynomialAgreementSet,
            powerBatchedWord])
  refine ⟨exceptional, ?_, hgood⟩
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast hcard)

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
    (by intro i hi; change (0 : ZMod 2) = 0; rfl)
    (by compute_degree!)
    (by intro j hj; simp)
    (by intro i hi; simp)
  exact ⟨P, hdegree, hsample, hresult.1, hresult.2⟩

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

private theorem component_admissibility_cut :
    ∀ i ∈ (Finset.univ : Finset (Fin 1)),
      jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
        (componentEquation (E := ComponentField)) 1 2 (Polynomial.C 0) 0 ∈
          componentIdeal (E := ComponentField) := by
  intro i hi
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst i
  have hcut : jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 1 2 (Polynomial.C 0) 0 =
      jointInitialJetEquation (r := 0) (0 : ComponentField)
        (componentEquation (E := ComponentField)) := by
    simpa only [Polynomial.C_0] using component_jointCut_eq_length_one
  rw [hcut]
  exact component_initialEquation_mem

local instance : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime

private theorem extractedAdmissibleFrobeniusPair :
    ∃ F₀ G₀ : ℚ[X],
      IsAdmissibleFrobeniusPair domain componentWord componentWord
        (algebraMap ℚ ComponentField) (fun _ ↦ 0) 0
        (componentEquation (E := ComponentField)) 1 1 2 1 F₀ G₀ := by
  obtain ⟨F₀, G₀, hP, _⟩ := exists_admissibleFrobeniusPair_of_symbolic_prime_sample
    (domain := domain) (f := componentWord) (g := componentWord)
    (sample := Finset.univ) (hsample := by simp)
    (iota := algebraMap ℚ ComponentField) (p := 1) (e := 0)
    (roots := fun _ ↦ 0) (hroots := by
      intro i hi
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      norm_num
      change (0 : ComponentField) = (algebraMap ℚ ComponentField) (0 : ℚ)
      simp)
    (center := 0) (Q := componentEquation (E := ComponentField))
    (K := 1) (k := 1) (hK := by norm_num) (hKk := by norm_num) (τ := 2)
    (hτ := taylorExponentSufficient_two_mul 0 1)
    (I := componentIdeal (E := ComponentField))
    component_separant_notMem component_initialEquation_mem
    componentIdeal_degree_pos
    (by intro l hl; fin_cases l; norm_num at hl)
    (by
      intro i hi
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [componentWord, Polynomial.C_0] using component_admissibility_cut 0 (by simp))
  exact ⟨F₀, G₀, hP⟩

example :
    ∃ F₀ G₀ : ℚ[X],
      ({(F₀, G₀)} : Finset (ℚ[X] × ℚ[X])).card ≤
        (jointInitialJetEquation (r := 0) (0 : ComponentField)
          (componentEquation (E := ComponentField))).degreeOf (some 0) := by
  obtain ⟨F₀, G₀, hP⟩ := extractedAdmissibleFrobeniusPair
  refine ⟨F₀, G₀, ?_⟩
  exact admissibleFrobeniusPairs_card_le_degreeOf (K := 1) (k := 1)
    domain componentWord componentWord
    (algebraMap ℚ ComponentField) (fun _ ↦ (0 : ComponentField)) 0
    (componentEquation (E := ComponentField)) 1 0 2
    (by norm_num) (by norm_num) (taylorExponentSufficient_two_mul 0 1)
    component_initialEquation_ne_zero {(F₀, G₀)} (by
      intro P hmem
      rw [Finset.mem_singleton] at hmem
      cases hmem
      exact hP)

example :
    ∃ F₀ G₀ : ℚ[X],
      IsAdmissibleFrobeniusPair domain componentWord componentWord
        (algebraMap ℚ ComponentField) (fun _ ↦ 0) 0
        (componentEquation (E := ComponentField)) 1 1 2 1 F₀ G₀ ∧
      rationalTaylorPolynomial (0 : ComponentField)
        (MvPolynomial.map (Polynomial.evalRingHom (0 : ComponentField))
          (componentEquation (E := ComponentField))) 1
        (fun j ↦ (frobeniusInitialGraph (0 : ComponentField) 1
          (F₀.map (algebraMap ℚ ComponentField)) (G₀.map (algebraMap ℚ ComponentField))
          (some j)).eval 0) =
        expand ComponentField 1
          (F₀.map (algebraMap ℚ ComponentField) + Polynomial.C 0 *
            G₀.map (algebraMap ℚ ComponentField)) := by
  obtain ⟨F₀, G₀, hP⟩ := extractedAdmissibleFrobeniusPair
  refine ⟨F₀, G₀, hP, ?_⟩
  have hspec := hP.specialize (K := 1) (k := 1) (p := 1) (e := 0)
    (by norm_num) (by norm_num) (taylorExponentSufficient_two_mul 0 1) 0 (by
      simp [jointInitialJetSeparant, componentEquation, initialJetSeparant,
        separant, Fin.last])
  simpa [pow_zero, one_pow] using hspec

end

end ReedSolomon.GraphLineComponentTest
