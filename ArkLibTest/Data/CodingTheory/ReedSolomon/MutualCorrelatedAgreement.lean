/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for power-batched point recognition

These examples check a concrete extension-field agreement bound, a nonconstant batched Hasse jet,
and reconstruction from one symbolic agreement sample with a regular jet.
-/

open MvPolynomial Polynomial PolynomialDifferential

namespace ReedSolomon.PowerBatchedPointRecognitionTest

/-- The one-point evaluation domain at zero over `ZMod 3`. -/
private def domain : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- A tuple of zero polynomials and words has one common agreement point. -/
example : (commonCurveAgreementSet (ℓ := 0) domain (fun _ _ : Fin 1 ↦ (0 : ZMod 3))
    (fun _ ↦ (0 : Polynomial (ZMod 3)))).card = 1 := by
  norm_num [commonCurveAgreementSet, domain]

/-- No exceptional challenge is needed when the only constituent polynomial agrees everywhere. -/
example : ∃ exceptional : Finset (ZMod 3), exceptional.card ≤ 0 := by
  obtain ⟨exceptional, hcard, _⟩ :=
    exists_exceptional_powerBatched_extension domain
      (fun _ _ : Fin 1 ↦ (0 : ZMod 3)) (fun _ : Fin 1 ↦ (0 : Polynomial (ZMod 3)))
      (RingHom.id _)
      1 (by norm_num [commonCurveAgreementSet, domain])
  exact ⟨exceptional, by simpa using hcard⟩

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

/-- A regular symbolic chart point with one sample reconstructs the zero graph. -/
example :
    ∃ P : Fin 1 → Polynomial (ZMod 3),
      (∀ t, (P t).degree < 1) ∧
      (∀ i ∈ ({0} : Finset (Fin 1)), ∀ t, (P t).eval (domain i) = 0) ∧
      rationalTaylorPolynomial (0 : ZMod 3)
        (MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 3))
          (MvPolynomial.X (some (0 : Fin 1)) :
            DifferentialPolynomial (Polynomial (ZMod 3)) 0))
        1 (fun _ ↦ 0) = powerBatchedPolynomial P 1 := by
  let w : Fin 1 → Fin 1 → ZMod 3 := fun _ _ ↦ 0
  let Q : DifferentialPolynomial (Polynomial (ZMod 3)) 0 := MvPolynomial.X (some 0)
  let Qz : DifferentialPolynomial (ZMod 3) 0 :=
    MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 3)) Q
  obtain ⟨P, hP, hs, hrecognize⟩ :=
    exists_polynomialGraph_of_symbolic_sample_of_exponent (k := 1) (K := 1) (r := 0)
      domain w {0} (by simp) (RingHom.id _) 0 Q (by omega) 2
      (taylorExponentSufficient_two_mul 0 1)
  refine ⟨P, hP, ?_, ?_⟩
  · simpa [w] using hs
  · have hS : MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
        (initialJetSeparant (0 : ZMod 3)
          Qz) ≠ 0 := by
      simp [Qz, Q, initialJetSeparant, separant]
    have hhigh : ∀ l : Fin 1, 1 ≤ l.val →
        MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
          (commonTaylorNumerator (0 : ZMod 3)
            Qz 2 l.val) = 0 := by
      intro l hl
      omega
    have hcuts : ∀ i ∈ ({0} : Finset (Fin 1)),
        MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
          (taylorAgreementEquation (0 : ZMod 3) Qz 1 2
            (RingHom.id _ (domain i))
            (Polynomial.eval 1 (powerBatchedCoordinate (fun t : Fin 1 ↦ w t i)))) = 0 := by
      intro i hi
      fin_cases i
      apply (taylorAgreementEquation_eq_zero_iff (0 : ZMod 3) Qz
        (taylorExponentSufficient_two_mul 0 1) (fun _ ↦ 0) hS
        (RingHom.id _ (domain 0))
        (Polynomial.eval 1 (powerBatchedCoordinate (fun t : Fin 1 ↦ w t 0)))).2
      rw [eval_rationalTaylorPolynomial]
      simp [rationalTaylorCoefficient, rationalTaylorNumerator, initialJetSeparant,
        Qz, Q, powerBatchedCoordinate, w]
    simpa [Q] using (hrecognize 1 (fun _ ↦ 0) hS hhigh hcuts).1

end ReedSolomon.PowerBatchedPointRecognitionTest
