/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusAdmissibility
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedDerivativeImage
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleSeparableBound
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
  ReedSolomon.powerAgreement_one_of_exactCorrelatedPair pointDomain (fun _ ↦ 1) (fun _ ↦ 0)
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

private def componentWords : Fin 2 → Fin 1 → ℚ := fun _ _ ↦ 0

local instance : DecidableEq ℚ := Classical.decEq _

private theorem componentWordPolynomial_zero :
    powerBatchedCoordinate (fun t ↦ (algebraMap ℚ MCAField) (componentWords t 0)) = 0 := by
  rw [powerBatchedCoordinate_eq_zero_iff]
  funext t
  simp [componentWords]

private theorem componentSampleCut :
    jointTaylorAgreementEquation (0 : MCAField) componentEquation 1 0
      (Polynomial.C ((algebraMap ℚ MCAField) (componentDomain 0)))
      (powerBatchedCoordinate (fun t ↦ (algebraMap ℚ MCAField) (componentWords t 0))) ∈
        componentIdeal := by
  rw [componentWordPolynomial_zero]
  simpa [componentDomain_zero] using componentAgreementCut_mem

private theorem componentZero_mem_zeroLocus :
    (fun _ : Option (Fin 1) ↦ (0 : MCAField)) ∈ zeroLocus MCAField componentIdeal := by
  change (fun _ : Option (Fin 1) ↦ (0 : MCAField)) ∈
    zeroLocus MCAField (Ideal.span {componentVariable})
  rw [zeroLocus_span]
  simp [componentVariable]

private theorem componentZero_regular :
    (fun _ : Option (Fin 1) ↦ (0 : MCAField)) ∈ zeroLocus MCAField componentIdeal ∧
      aeval (fun _ : Option (Fin 1) ↦ (0 : MCAField))
        (jointInitialJetSeparant (0 : MCAField) componentEquation) ≠ 0 := by
  exact ⟨componentZero_mem_zeroLocus, by
    simp [jointInitialJetSeparant, initialJetSeparant, separant, componentEquation, Fin.last]⟩

/-- A positive-dimensional prime component with a nonzero separant yields a concrete graph pair. -/
example : ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
    P₀.eval 0 = 0 ∧ P₁.eval 0 = 0 ∧
    ∃ z : MCAField, (fun _ : Option (Fin 1) ↦ (0 : MCAField)) = fun i ↦
      (affinePairCurve (0 : MCAField) (P₀.map (algebraMap ℚ MCAField))
        (P₁.map (algebraMap ℚ MCAField)) i).eval z := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsample, hgraph, -, -, -, -, -⟩ :=
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
  have hregular := componentZero_regular
  obtain ⟨z, hz⟩ := hgraph _ hregular
  have hvalues := hsample 0 (by simp)
  exact ⟨P₀, P₁, hP₀, hP₁, by simpa only [componentDomain_zero] using hvalues.1,
    by simpa only [componentDomain_zero] using hvalues.2, z, hz⟩

example : ∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
    1 ≤ (commonCurveAgreementSet componentDomain componentWords P).card := by
  obtain ⟨P, hdegree, hcommon, -, -, -, -⟩ :=
    @exists_polynomialGraph_of_primeTaylorComponent_agreements ℚ MCAField
      inferInstance inferInstance 1 1 1 0 1 inferInstance 1 componentDomain componentWords
      ({0} : Finset (Fin 1)) (by simp) (by norm_num) (algebraMap ℚ MCAField) 0
      componentEquation (by omega) 0 (by intro l; norm_num [TaylorExponentSufficient])
      componentIdeal componentIdeal_prime componentSeparant_notMem componentIdeal_positiveDimension
      (by intro l hl; omega) (by
        intro i hi
        simp only [Finset.mem_singleton] at hi
        subst i
        exact componentSampleCut)
  exact ⟨P, hdegree, hcommon⟩

example : ∃ P : Fin 2 → ℚ[X],
    IsAdmissibleChartTupleAtExponent componentDomain componentWords
      (algebraMap ℚ MCAField) 0 componentEquation 1 1 1 0 P ∧
    (fun _ : Option (Fin 1) ↦ (0 : MCAField)) ∈
      admissibleChartTupleGraphLocus componentDomain componentWords
        (algebraMap ℚ MCAField) 0 componentEquation 1 1 1 0 := by
  obtain ⟨P, hP, hgraph⟩ :=
    exists_admissibleChartTuple_of_primeTaylorComponent_agreements
      (K := 1) (k := 1) (L := 1) (r := 0) (ℓ := 1) componentDomain
      componentWords ({0} : Finset (Fin 1)) (by simp) (by norm_num)
      (algebraMap ℚ MCAField) 0 componentEquation (by omega) 0
      (by intro l; norm_num [TaylorExponentSufficient]) componentIdeal
      componentIdeal_prime componentSeparant_notMem
      componentIdeal_positiveDimension componentInitialEquation_mem
      (by intro l hl; omega) (by
        intro i hi
        simp only [Finset.mem_singleton] at hi
        subst i
        exact componentSampleCut)
  refine ⟨P, hP, ?_⟩
  change ∃ P', IsAdmissibleChartTupleAtExponent componentDomain componentWords
      (algebraMap ℚ MCAField) 0 componentEquation 1 1 1 0 P' ∧
    (fun _ : Option (Fin 1) ↦ (0 : MCAField)) = fun j ↦
      (powerBatchedJetGraphMap (r := 0) 0 (fun t ↦ (P' t).map (algebraMap ℚ MCAField)) j).eval 0
  exact ⟨P, hP, hgraph _ componentZero_regular⟩

example : (fun _ : Option (Fin 1) ↦ (0 : MCAField)) ∈
    admissibleChartTupleGraphLocus componentDomain componentWords
      (algebraMap ℚ MCAField) 0 componentEquation 1 1 1 0 := by
  have hcuts : 1 ≤ {i : Fin 1 | jointTaylorAgreementEquation (0 : MCAField)
      componentEquation 1 0 (Polynomial.C ((algebraMap ℚ MCAField) (componentDomain i)))
      (powerBatchedCoordinate (fun t ↦
        (algebraMap ℚ MCAField) (componentWords t i))) ∈ componentIdeal}.ncard := by
    apply Nat.succ_le_of_lt
    apply (Set.ncard_pos).2
    exact ⟨0, componentSampleCut⟩
  have hsubset := principalOpen_subset_admissibleChartTupleGraphLocus
    (n := 1) (r := 0) (ℓ := 1) componentDomain
    componentWords (algebraMap ℚ MCAField) 0 componentEquation 1 1 1 0
    (by omega) (by omega) (by intro l; omega) componentIdeal componentIdeal_prime
    componentSeparant_notMem componentIdeal_positiveDimension componentInitialEquation_mem
    (by intro l hl; omega) hcuts
  exact hsubset componentZero_regular

example : ∃ F₀ G₀ : ℚ[X],
    IsAdmissibleFrobeniusPair componentDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (algebraMap ℚ MCAField) (fun _ ↦ (0 : MCAField)) 0 componentEquation 1 1 0 1 F₀ G₀ ∧
    (fun _ : Option (Fin 1) ↦ (0 : MCAField)) = fun i ↦
      (frobeniusInitialGraph 0 1 (F₀.map (algebraMap ℚ MCAField))
        (G₀.map (algebraMap ℚ MCAField)) i).eval 0 := by
  obtain ⟨F₀, G₀, hP, hgraph⟩ :=
    @exists_admissibleFrobeniusPair_of_symbolic_prime_sample ℚ MCAField (Fin 1)
    inferInstance inferInstance 1 1 inferInstance
    componentDomain (fun _ ↦ 0) (fun _ ↦ 0) univ (by simp) (algebraMap ℚ MCAField) 1 0
    inferInstance (fun _ ↦ 0) (by
      intro i hi
      have hi' : i = 0 := by simpa using hi
      subst i
      simp [componentDomain_zero])
    0 componentEquation (by omega) (by norm_num) 0
    (by intro l; fin_cases l; norm_num [TaylorExponentSufficient]) componentIdeal
    componentIdeal_prime componentSeparant_notMem componentInitialEquation_mem
    componentIdeal_positiveDimension (by intro l hl; simp at hl)
    (by
      intro i hi
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simpa [componentDomain_zero, pow_one] using componentAgreementCut_mem)
  exact ⟨F₀, G₀, hP, hgraph _ componentZero_regular⟩

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
  · exact componentZero_regular.1
  · exact componentZero_regular.2
  · simpa only [pow_zero, one_pow] using hsubset componentZero_regular

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

private def regularBoundValues : Fin 2 → Fin 2 → MCAField :=
  fun t i ↦ if t.val = 0 then 0 else i.val

private def regularBoundConstantValues : Fin 2 → Fin 2 → MCAField := fun _ _ ↦ 0

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

private theorem badChallengeExponent : TaylorExponentSufficient 1 2 2 := by intro l; omega

private theorem componentEquation_jetDegree : jetTotalDegree componentEquation ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  rintro u hu
  simp [componentEquation, MvPolynomial.support_X] at hu
  subst u
  simp [totalJetDegree_eq_sum]

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
    (hcommon : commonCurveAgreementSet positiveChallengeDomain regularBoundValues P = univ) :
    False := by
  have h0 := ((mem_commonCurveAgreementSet positiveChallengeDomain
    regularBoundValues P 0).mp (by rw [hcommon]; simp)) 1
  have h1 := ((mem_commonCurveAgreementSet positiveChallengeDomain
    regularBoundValues P 1).mp (by rw [hcommon]; simp)) 1
  rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp (hdegree 1))] at h0 h1
  norm_num [positiveChallengeDomain, regularBoundValues] at h0 h1
  exact zero_ne_one (h0.symm.trans h1)

private theorem positiveChallenge_isBad :
    ¬ HasExactPowerAgreement positiveChallengeDomain regularBoundValues
      (RingHom.id MCAField) 1 0 0 := by
  rintro ⟨P, hdegree, -, hsets⟩
  apply positiveChallenge_no_common P hdegree
  rw [← hsets]
  ext i
  simp [polynomialAgreementSet, positiveChallengeDomain, regularBoundValues,
    powerBatchedWord]

private theorem positiveChallenge_two_agreements :
    2 ≤ (polynomialAgreementSet positiveChallengeDomain
      (powerBatchedWord regularBoundValues 0) 0).card := by
  exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨0,
    by simp [polynomialAgreementSet, positiveChallengeDomain, regularBoundValues,
      powerBatchedWord], 1,
    by simp [polynomialAgreementSet, positiveChallengeDomain, regularBoundValues,
      powerBatchedWord], by decide⟩)

private abbrev positiveDerivativeBound :=
  regularPowerBatchedDerivativeCappedBoundTwo 2 1 2 1 1 1 1 1 1 2

/-- A nonempty positive-rate bad set has the derivative-capped finite and exceptional bounds. -/
example : (positiveChallenges.card : ℚ) ≤ positiveDerivativeBound ∧
    ∃ exceptional : Finset MCAField,
      (exceptional.card : ℚ) ≤ positiveDerivativeBound ∧ 0 ∈ exceptional ∧
    ∃ regularExceptional : Finset MCAField,
      regularExceptional.card ≤ 1 ∧ 0 ∈ regularExceptional ∧
    ∃ curveExceptional : Finset MCAField,
      curveExceptional.card ≤ 1 ∧
    ∃ w : MCAField, w ∉ curveExceptional ∧
      HasExactPowerAgreement positiveChallengeDomain regularBoundConstantValues
        (RingHom.id MCAField) 2 w 0 := by
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
    exact ⟨hd, hi, hs, (fun l hl ↦ hc l (by omega)), by
      change rationalTaylorPolynomial 0 _ 2 (fun _ : Fin 2 ↦ (0 : MCAField)) = 0
      simpa [positiveChallengeWitness] using ht⟩
  have hagree : ∀ z ∈ positiveChallenges, 1 ≤
      (polynomialAgreementSet positiveChallengeDomain
        (powerBatchedWord regularBoundValues z) (positiveChallengeWitness z)).card := by
    intro z hz; obtain rfl := Finset.mem_singleton.mp hz
    simpa [positiveChallengeWitness] using
      (Nat.le_trans (by decide : 1 ≤ 2) positiveChallenge_two_agreements)
  have hbad : ∀ z ∈ positiveChallenges,
      ¬ HasExactPowerAgreement positiveChallengeDomain regularBoundValues
        (RingHom.id _) 1 z (positiveChallengeWitness z) := by
    intro z hz; obtain rfl := Finset.mem_singleton.mp hz; exact positiveChallenge_isBad
  have hbound := finite_powerBatchedBadChallenges_card_le_derivativeCapped_of_exponent
    positiveChallengeDomain regularBoundValues (RingHom.id _) 0 badChallengeEquation
    2 1 1 1 1 1 1 2 badChallengeExponent (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hjet hheight
    (by simp [badChallengeEquation]) positiveChallenges positiveChallengeWitness
    positiveChallengeJet hchart hagree hbad
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent
      positiveChallengeDomain regularBoundValues (RingHom.id _) badChallengeEquation
      2 1 1 1 1 1 1 2 badChallengeExponent (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hjet hheight
      (by simp [badChallengeEquation]) (by omega)
  have hzero : (0 : MCAField) ∈ exceptional := by
    by_contra hz
    apply hbad 0 (by simp [positiveChallenges])
    exact hgood 0 hz 0 (by simp) (hagree 0 (by simp [positiveChallenges]))
      (by simp [badChallengeEquation, challengeSpecialization, differentialSpecialization,
        differentialSpecializationHom])
      (by simp [badChallengeEquation, challengeSpecialization, separant,
        differentialSpecialization, differentialSpecializationHom, Fin.last])
  obtain ⟨regularExceptional, hregularCard, hregularGood⟩ :=
    exists_exceptional_frobeniusPowerSeparableSolutions_at
      (n := 2) (k := 1) (K := 1) (ℓ := 1) (L := 2)
      positiveChallengeDomain regularBoundValues
      (RingHom.id MCAField) positiveChallengeDomain
      componentEquation 1 0 1 0 1 2 (by simp)
      (by norm_num) (by norm_num)
      ((taylorExponentSufficient_two_mul_sub_three 0 1).mono (by omega))
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (coeffNatDegreeLE_X (some (0 : Fin 1)))
      componentEquation_jetDegree (MvPolynomial.X_prime).irreducible
      (by simp [componentEquation, MvPolynomial.pderiv_X])
      (by simp [componentEquation])
  have hregularZero : (0 : MCAField) ∈ regularExceptional := by
    by_contra hz
    apply positiveChallenge_isBad
    simpa [regularBoundValues, RingHom.id_apply] using
      hregularGood 0 hz 0 (by norm_num) (by
        simp [componentEquation, challengeSpecialization, differentialSpecialization,
          differentialSpecializationHom]) (by
        simpa [RingHom.id_apply] using positiveChallenge_two_agreements)
  obtain ⟨curveExceptional, hcurveCard, hcurveGood⟩ :=
    exists_exceptional_frobeniusPowerFactorSolutions (n := 2) (ℓ := 1)
      positiveChallengeDomain regularBoundConstantValues (RingHom.id _)
      componentEquation 1 0 1 0 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (coeffNatDegreeLE_X (some (0 : Fin 1))) componentEquation_jetDegree
      MvPolynomial.X_prime.irreducible (by simp [componentEquation])
      (by simp [componentEquation])
  refine ⟨hbound, exceptional, hcard, hzero, regularExceptional,
    (by norm_num at hregularCard; exact_mod_cast hregularCard), hregularZero,
    curveExceptional,
    (by norm_num [ordinaryCurveFactorRaw] at hcurveCard; exact_mod_cast hcurveCard), ?_⟩
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := curveExceptional) (t := {(0 : MCAField), 1})
      (Nat.lt_of_le_of_lt (by exact_mod_cast (by simpa [ordinaryCurveFactorRaw] using hcurveCard))
        (by norm_num))
  exact ⟨w, hw, by
    simpa [pow_one] using hcurveGood w (by simpa [pow_one] using hw) 0
      (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe 2)
      (by simp [componentEquation, challengeSpecialization, differentialSpecialization,
        differentialSpecializationHom])
      (by norm_num [polynomialAgreementSet, positiveChallengeDomain,
        regularBoundConstantValues, powerBatchedWord])⟩

private theorem positiveChallenge_no_correlatedPair :
    ¬ HasExactCorrelatedPair positiveChallengeDomain (regularBoundValues 0)
      (regularBoundValues 1) (RingHom.id MCAField) 1 0 0 := by
  rintro ⟨⟨P₀, P₁⟩, hP₀, hP₁, -, hsets⟩
  apply positiveChallenge_no_common ![P₀, P₁] ?_
    (by simpa [commonCurveAgreementSet, commonPolynomialAgreementSet,
      positiveChallengeDomain, regularBoundValues, polynomialAgreementSet] using hsets.symm)
  intro t; fin_cases t <;> assumption
/-- The ordinary two-message bound applies to the nonempty challenge set. -/
example : positiveChallenges.Nonempty ∧ (positiveChallenges.card : ℚ) ≤ 2 := by
  have hregularBound := finite_frobeniusRegularBadChallenges_card_le
    (F := MCAField) (E := MCAField) (n := 2) (k := 1) (K := 1)
    (domain := positiveChallengeDomain) (f := regularBoundValues 0)
    (g := regularBoundValues 1) (ι := RingHom.id MCAField)
    (roots := positiveChallengeDomain) (center := 0) (Q := componentEquation)
    (p := 1) (e := 0) (τ := 2) (h := 0) (b := 1) (A := 2) (by simp)
    (by norm_num) (by norm_num) (taylorExponentSufficient_two_mul 0 1)
    (by norm_num) (by norm_num) (by norm_num)
    (coeffNatDegreeLE_X (some (0 : Fin 1))) componentEquation_jetDegree
    (by simp [jointInitialJetEquation, initialJetEquation, componentEquation])
    (by simpa [jointInitialJetEquation, initialJetEquation, componentEquation,
      componentIdeal, componentVariable] using componentIdeal_prime.ne_top)
    positiveChallenges positiveChallengeWitness
    (by simp [positiveChallenges, positiveChallengeWitness])
    (by simp [positiveChallenges, positiveChallengeWitness, componentEquation,
      challengeSpecialization, differentialSpecialization, differentialSpecializationHom])
    (by simp [positiveChallenges, componentEquation, challengeSpecialization, separant,
      jetEvaluation, polynomialJet])
    (by intro z hz; obtain rfl := Finset.mem_singleton.mp hz; norm_num
      [positiveChallengeDomain, regularBoundValues, positiveChallengeWitness,
        polynomialAgreementSet])
    (by simpa [positiveChallenges, positiveChallengeWitness] using
      positiveChallenge_no_correlatedPair)
  exact ⟨by simp [positiveChallenges], by
    convert hregularBound using 1; norm_num [positiveChallenges]⟩
private def incidencePoint : Option (Fin 2) → MCAField := fun _ ↦ 0

private theorem incidencePoint_regular :
    aeval incidencePoint (jointInitialJetEquation 0 badChallengeEquation) = 0 ∧
      aeval incidencePoint (jointInitialJetSeparant 0 badChallengeEquation) ≠ 0 ∧
      (∀ l : Fin 2, 0 ≤ l.val →
        aeval incidencePoint (jointCommonTaylorNumerator 0 badChallengeEquation 2 l) = 0) := by
  let x : Option (Fin 2) → MCAField := incidencePoint
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
  exact jointInitialJetEquation_ne_zero_of_regular (center := (0 : MCAField))
    (z := (0 : MCAField)) badChallengeEquation (fun _ ↦ 0)
    (badChallengeChartAtZero).2.2.1

private def positiveIncidencePoints : Finset (Option (Fin 2) → MCAField) :=
  {incidencePoint}

private theorem positiveIncidencePoint_offGraph :
    incidencePoint ∉ admissibleChartTupleGraphLocus positiveChallengeDomain
      regularBoundValues (RingHom.id _) 0 badChallengeEquation 2 1 2 2 := by
  rintro ⟨P, hP, -⟩
  apply positiveChallenge_no_common P hP.degree
  exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hP.common)

private theorem positiveIncidencePoint_agrees (i : Fin 2) :
    aeval incidencePoint (jointTaylorAgreementEquation 0 badChallengeEquation 2 2
      (Polynomial.C (positiveChallengeDomain i))
      (powerBatchedCoordinate (fun t ↦ regularBoundValues t i))) = 0 := by
  rw [aeval_jointTaylorAgreementEquation]
  have hcut := aeval_taylorAgreementEquation 0
    (MvPolynomial.map (Polynomial.evalRingHom (0 : MCAField)) badChallengeEquation)
    badChallengeExponent (fun _ : Fin 2 ↦ (0 : MCAField))
    (badChallengeChartAtZero).2.2.1 (positiveChallengeDomain i) 0
  have ht := (badChallengeChartAtZero).2.2.2.2
  rw [ht] at hcut
  simpa [incidencePoint, positiveChallengeDomain, regularBoundValues,
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
      x ∉ admissibleChartTupleGraphLocus positiveChallengeDomain regularBoundValues
        (RingHom.id _) 0 badChallengeEquation 2 1 2 2 := by
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨(incidencePoint_regular).1, (incidencePoint_regular).2.1,
      fun l hl ↦ (incidencePoint_regular).2.2 l (by omega),
      positiveIncidencePoint_offGraph⟩
  have hA : ∀ x ∈ positiveIncidencePoints, 2 ≤
      ({i : Fin 2 | aeval x (jointTaylorAgreementEquation 0 badChallengeEquation 2 2
        (Polynomial.C (positiveChallengeDomain i))
        (powerBatchedCoordinate (fun t ↦ regularBoundValues t i))) = 0} : Set (Fin 2)).ncard := by
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    have hset : {i : Fin 2 | aeval incidencePoint
        (jointTaylorAgreementEquation 0 badChallengeEquation 2 2
          (Polynomial.C (positiveChallengeDomain i))
          (powerBatchedCoordinate (fun t ↦ regularBoundValues t i))) = 0} =
        Set.univ := by
      ext i
      simp [positiveIncidencePoint_agrees]
    rw [hset]
    simp
  have hbound := finite_powerBatched_regular_points_off_graphs_card_le_derivativeCapped_of_exponent
    positiveChallengeDomain regularBoundValues (RingHom.id _) 0 badChallengeEquation
    2 1 2 2 1 1 1 2 badChallengeExponent (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) badChallengeEquation_regular
    badChallengeEquation_jetDegree badChallengeEquation_height (by simp [badChallengeEquation])
    positiveIncidencePoints hS hA
  exact ⟨by simp [positiveIncidencePoints], by simpa using hbound⟩

end
