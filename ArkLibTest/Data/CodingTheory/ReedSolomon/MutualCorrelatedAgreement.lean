/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedDerivativeImage
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.Nullstellensatz
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for Reed–Solomon mutual correlated agreement -/

open Polynomial Finset ReedSolomon PolynomialDifferential

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

noncomputable section

open MvPolynomial

private abbrev MCAField := ℂ

private def componentDomain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private theorem componentDomain_zero : componentDomain 0 = 0 := rfl

private abbrev componentEquation : DifferentialPolynomial MCAField[X] 0 :=
  MvPolynomial.X (some (0 : Fin 1))

private abbrev componentVariable : MvPolynomial (Option (Fin 1)) MCAField :=
  MvPolynomial.X (some (0 : Fin 1))

private def componentIdeal : Ideal (MvPolynomial (Option (Fin 1)) MCAField) :=
  Ideal.span {componentVariable}

private theorem componentIdeal_prime : componentIdeal.IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime

private theorem componentIdeal_positiveDimension :
    0 < (affineHilbertPolynomial componentIdeal).natDegree := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (f := componentVariable) (X_ne_zero _) componentIdeal_prime.ne_top
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at h
  unfold componentIdeal
  omega

private theorem componentSeparant_notMem :
    jointInitialJetSeparant (0 : MCAField) componentEquation ∉ componentIdeal := by
  have h1 : (1 : MvPolynomial (Option (Fin 1)) MCAField) ∉ componentIdeal :=
    (Ideal.ne_top_iff_one _).mp componentIdeal_prime.ne_top
  simpa [jointInitialJetSeparant, initialJetSeparant, separant, componentEquation,
    Fin.last] using h1

private theorem componentInitialEquation_mem :
    jointInitialJetEquation (0 : MCAField) componentEquation ∈ componentIdeal := by
  have hEq : jointInitialJetEquation (0 : MCAField) componentEquation = componentVariable := by
    simp [jointInitialJetEquation, initialJetEquation, componentEquation, componentVariable]
  rw [hEq]
  exact Ideal.subset_span (by simp)

private theorem componentAgreementCut_mem :
    jointTaylorAgreementEquation (0 : MCAField) componentEquation 1 0
      (Polynomial.C 0) 0 ∈ componentIdeal := by
  have hcut : jointTaylorAgreementEquation (0 : MCAField) componentEquation 1 0
      (Polynomial.C 0) 0 = jointInitialJetEquation (0 : MCAField) componentEquation := by
    simp [jointTaylorAgreementEquation, jointInitialJetEquation, taylorAgreementEquationOver,
      commonTaylorNumeratorOver, rationalTaylorNumeratorOver,
      initialJetEquation, initialJetSeparant, separant, componentEquation, Fin.last]
  rw [hcut]
  exact componentInitialEquation_mem

private theorem componentZero_mem_zeroLocus :
    (fun _ : Option (Fin 1) ↦ (0 : MCAField)) ∈ zeroLocus MCAField componentIdeal := by
  change (fun _ : Option (Fin 1) ↦ (0 : MCAField)) ∈
    zeroLocus MCAField (Ideal.span {componentVariable})
  rw [zeroLocus_span]
  simp [componentVariable]

/-- A positive-dimensional prime component with a nonzero separant yields a concrete graph pair. -/
example : ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
    P₀.eval 0 = 0 ∧ P₁.eval 0 = 0 := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsample, -, -, -, -, -, -⟩ :=
    @exists_graphLine_pair_of_regular_component MCAField inferInstance 0 ℚ inferInstance 1 1 1
      inferInstance
      componentDomain (fun _ ↦ 0) (fun _ ↦ 0) Finset.univ (by simp)
      (algebraMap ℚ MCAField) 0 componentEquation (by omega) 0
      (by intro l; fin_cases l; norm_num [TaylorExponentSufficient]) componentIdeal
      componentIdeal_prime
      componentSeparant_notMem componentIdeal_positiveDimension componentInitialEquation_mem
      (by intro l hl; omega)
      (by
        intro i hi
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [componentDomain_zero, map_zero]
        rw [show Polynomial.C (0 : MCAField) + Polynomial.X * Polynomial.C 0 = 0 by simp]
        exact componentAgreementCut_mem)
  have hvalues := hsample 0 (by simp)
  exact ⟨P₀, P₁, hP₀, hP₁, by simpa only [componentDomain_zero] using hvalues.1,
    by simpa only [componentDomain_zero] using hvalues.2⟩

/-- The zero point of the same positive-dimensional component lies on a Frobenius pair graph. -/
example : ∃ x : Option (Fin 1) → MCAField,
    x ∈ zeroLocus MCAField componentIdeal ∧
      aeval x (jointInitialJetSeparant (0 : MCAField) componentEquation) ≠ 0 ∧
      x ∈ admissibleFrobeniusPairGraphLocus componentDomain (fun _ ↦ 0) (fun _ ↦ 0)
        (algebraMap ℚ MCAField) (fun _ ↦ 0) 0 componentEquation 1 1 0 1 := by
  have hsubset := principalOpen_subset_admissibleFrobeniusPairGraphLocus
    (n := 1) (k := 1) (K := 1) componentDomain (fun _ ↦ 0) (fun _ ↦ 0)
    (algebraMap ℚ MCAField) 1 0
    (fun _ ↦ (0 : MCAField)) (by
      intro i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [componentDomain_zero]
      simp)
    0 componentEquation (by omega) (by omega) 0
    (by intro l; fin_cases l; norm_num [TaylorExponentSufficient]) componentIdeal
    (hI := componentIdeal_prime)
    componentSeparant_notMem componentInitialEquation_mem
    (by simp [frobeniusSparseTaylorCuts]) componentIdeal_positiveDimension
    (by
      apply Nat.succ_le_of_lt
      apply (Set.ncard_pos).2
      refine ⟨0, ?_⟩
      simp only [Set.mem_ofPred_eq]
      rw [pow_zero, pow_one]
      have hmap0 : algebraMap ℚ MCAField (0 : ℚ) = 0 := map_zero _
      repeat rw [hmap0]
      rw [show Polynomial.C (0 : MCAField) + Polynomial.X * Polynomial.C 0 = 0 by simp]
      exact componentAgreementCut_mem)
  refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
  · exact componentZero_mem_zeroLocus
  · simp [jointInitialJetSeparant, initialJetSeparant, separant, componentEquation, Fin.last]
  · simpa only [pow_zero, one_pow] using hsubset (by
      constructor
      · exact componentZero_mem_zeroLocus
      · simp [jointInitialJetSeparant, initialJetSeparant, separant, componentEquation,
          Fin.last])

private def recognitionDomain : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private theorem recognitionDomain_zero : recognitionDomain 0 = 0 := rfl

private def recognitionWords : Fin 2 → Fin 1 → ZMod 3 :=
  fun t _ ↦ if t = 0 then 2 else 1

private def recognitionChart : DifferentialPolynomial (Polynomial (ZMod 3)) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

private def recognitionChartAt : DifferentialPolynomial (ZMod 3) 0 :=
  MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 3)) recognitionChart

private def recognitionJet : Fin 1 → ZMod 3 := fun _ ↦ 0

/-- A sample with a nonzero second word component determines a concrete polynomial graph. -/
example : ∃ P : Fin 2 → Polynomial (ZMod 3), (∀ t, (P t).degree < 1) ∧
    (∀ i ∈ ({0} : Finset (Fin 1)), ∀ t, (P t).eval (recognitionDomain i) = recognitionWords t i) ∧
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
      recognitionDomain recognitionWords {0} (by simp) (RingHom.id _) 0 recognitionChart
      (by omega) 4 (taylorExponentSufficient_two_mul 0 2)
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
    simp [hc0, recognitionWords, Fin.sum_univ_succ, recognitionDomain_zero,
      show (2 + 1 : ZMod 3) = 0 by decide]

local instance : DecidableEq MCAField := Classical.decEq _

private abbrev badChallengeEquation : DifferentialPolynomial MCAField[X] 1 :=
  MvPolynomial.X (some (Fin.last 1))

private def positiveChallengeDomain : Fin 2 ↪ MCAField where
  toFun i := (i.val : MCAField)
  inj' _ _ h := Fin.ext (Nat.cast_inj.mp h)

private def positiveChallengeWords : Fin 2 → Fin 2 → MCAField :=
  fun t i ↦ if t.val = 0 then 0 else i.val

private def positiveChallenges : Finset MCAField := {0}
private def positiveChallengeWitness (_ : MCAField) : MCAField[X] := 0
private def positiveChallengeJet (_ : MCAField) : Fin 2 → MCAField := fun _ ↦ 0

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
    let Qz := MvPolynomial.map (Polynomial.evalRingHom (0 : MCAField))
      badChallengeEquation
    (0 : MCAField[X]).degree < 1 ∧
      aeval (fun _ : Fin 2 ↦ (0 : MCAField)) (initialJetEquation 0 Qz) = 0 ∧
      aeval (fun _ : Fin 2 ↦ (0 : MCAField)) (initialJetSeparant 0 Qz) ≠ 0 ∧
      (∀ l : Fin 2, 0 ≤ l.val → aeval (fun _ : Fin 2 ↦ (0 : MCAField))
        (commonTaylorNumerator 0 Qz 2 l.val) = 0) ∧
      rationalTaylorPolynomial 0 Qz 2 (fun _ : Fin 2 ↦ 0) = 0 := by
  let Qz := MvPolynomial.map (Polynomial.evalRingHom (0 : MCAField)) badChallengeEquation
  have hsep : aeval (fun _ : Fin 2 ↦ (0 : MCAField))
      (initialJetSeparant 0 Qz) ≠ 0 := by simp [Qz, initialJetSeparant, separant, Fin.last]
  have hsolution : differentialSpecialization Qz (0 : MCAField[X]) = 0 := by
    simp [Qz, differentialSpecialization, differentialSpecializationHom]
  have hseparant : jetEvaluation (separant Qz (Fin.last 1)) 0
      (polynomialJet 0 (0 : MCAField[X])) ≠ 0 := by
    simp [Qz, separant, jetEvaluation, polynomialJet, Fin.last]
  have hjet : (fun _ : Fin 2 ↦ (0 : MCAField)) =
      polynomialJet 0 (0 : MCAField[X]) := by ext j; fin_cases j <;> simp [polynomialJet]
  have hcoeff : ∀ l : Fin 2,
      rationalTaylorCoefficient 0 Qz (fun _ ↦ (0 : MCAField)) l.val = 0 := fun l ↦ by
    simpa using rationalTaylorCoefficient_initial 0 Qz (fun _ : Fin 2 ↦ 0) l
  have hpoly := rationalTaylorPolynomial_polynomialJet 0 Qz (0 : MCAField[X])
    hsolution hseparant (K := 2) (WithBot.bot_lt_coe 2) (by intro i hi hil; omega)
  rw [← hjet] at hpoly
  refine ⟨by simp, ?_, hsep, ?_, ?_⟩
  · simp [initialJetEquation, badChallengeEquation]
  · intro l _
    exact aeval_commonTaylorNumerator_eq_zero 0 Qz (fun _ ↦ 0) 2 hsep (hcoeff l)
  · exact hpoly

private theorem positiveChallenge_no_common (P : Fin 2 → MCAField[X])
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
      (RingHom.id MCAField) 1 0 0 := by
  rintro ⟨P, hdegree, -, hsets⟩
  apply positiveChallenge_no_common P hdegree
  rw [← hsets]
  ext i
  simp [polynomialAgreementSet, positiveChallengeDomain, positiveChallengeWords,
    powerBatchedWord]

private theorem positiveChallenge_two_agreements :
    2 ≤ (polynomialAgreementSet positiveChallengeDomain
      (powerBatchedWord positiveChallengeWords 0) 0).card := by
  exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨0,
    by simp [polynomialAgreementSet, positiveChallengeDomain, positiveChallengeWords,
      powerBatchedWord], 1,
    by simp [polynomialAgreementSet, positiveChallengeDomain, positiveChallengeWords,
      powerBatchedWord], by decide⟩)

private abbrev positiveDerivativeBound :=
  regularPowerBatchedDerivativeCappedBoundTwo 2 1 2 1 1 1 1 1 1 2

/-- The nonempty bad challenge set satisfies its derivative-capped bound. -/
example : positiveChallenges.Nonempty ∧
    (positiveChallenges.card : ℚ) ≤ positiveDerivativeBound := by
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
    exact ⟨hd, hi, hs, (fun l hl ↦ hc l (by omega)), by
      change rationalTaylorPolynomial 0
        (MvPolynomial.map (Polynomial.evalRingHom 0) badChallengeEquation) 2
        (fun _ : Fin 2 ↦ (0 : MCAField)) = 0
      exact ht⟩
  have hagree : ∀ z ∈ positiveChallenges, 1 ≤
      (polynomialAgreementSet positiveChallengeDomain
        (powerBatchedWord positiveChallengeWords z) (positiveChallengeWitness z)).card := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    simpa [positiveChallengeWitness] using
      (Nat.le_trans (by decide : 1 ≤ 2) positiveChallenge_two_agreements)
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
    badChallengeEquation_jetDegree badChallengeEquation_height
    (by simp [badChallengeEquation]) positiveChallenges positiveChallengeWitness
    positiveChallengeJet hchart hagree hbad
  exact ⟨by simp [positiveChallenges], hbound⟩

end
