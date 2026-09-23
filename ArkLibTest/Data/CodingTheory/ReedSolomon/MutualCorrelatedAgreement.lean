/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Extension

/-!
# Acceptance tests for power-batched point recognition

These examples check a concrete extension-field agreement bound and mapped set, a nonconstant
batched Hasse jet, and reconstruction from one symbolic agreement sample with a high cut.
-/

open MvPolynomial Polynomial PolynomialDifferential

namespace ReedSolomon.PowerBatchedPointRecognitionTest

noncomputable section

private abbrev E₉ := FiniteField.Extension (ZMod 3) 3 2

/-- The one-point evaluation domain at zero over `ZMod 3`. -/
private def domain : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

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
    · have hcoeff := aeval_commonTaylorNumerator_polynomialJet (0 : ZMod 3)
        recognitionChartAt (0 : Polynomial (ZMod 3)) hsolution hseparant
        (τ := 4) (l := 1) (by norm_num) (by
          intro i hir hi
          have : i = 1 := by omega
          subst i
          norm_num)
      have hjetZero : recognitionJet = polynomialJet 0 (0 : Polynomial (ZMod 3)) := by
        funext j
        fin_cases j
        simp [recognitionJet, polynomialJet, Polynomial.hasseJet]
      have hcoeffZero : MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
          (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0 := by
        change MvPolynomial.aeval recognitionJet
          (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0
        rw [hjetZero, hcoeff]
        simp [polynomialJet, Polynomial.hasseJet]
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

end

end ReedSolomon.PowerBatchedPointRecognitionTest
