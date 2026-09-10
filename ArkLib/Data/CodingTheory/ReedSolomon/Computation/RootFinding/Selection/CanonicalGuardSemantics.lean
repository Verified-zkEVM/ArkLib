/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Completeness
/-!
# Exact canonical-guard acceptance

The guard accepts precisely when all supplied earlier differential equations vanish on the
candidate and its center is the first sample where the supplied separant does not vanish.
This result includes the actual terminating execution and its work bound. It does not assume
or prove that the supplied equations form a separant chain: chain generation and the resulting
unique-stage theorem are separate consumers.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalGuardMachine

open Polynomial MvPolynomial CompPoly PolynomialDifferential

variable {F : Type*}

section Semiring

variable [CommSemiring F] [DecidableEq F]

/-- Acceptance executes every previous zero test and the ordered center comparison. -/
theorem result_eq_true_iff (input : Input F) (ps : List (Equation F)) :
    result input ps = true ↔
      (∀ q ∈ ps, ResidualZeroMachine.result (residualInput input q) input.samples = true) ∧
      ResidualWitnessMachine.result (residualInput input input.separant) input.samples =
        some input.center := by
  induction ps with
  | nil => simp [result, witnessSpec]
  | cons q ps ih =>
      cases hz : ResidualZeroMachine.result (residualInput input q) input.samples <;>
        simp [result, hz, ih]

end Semiring

section Field

variable [Field F] [DecidableEq F] {r D L : ℕ}

/-- A zero-translation identity checker tests exactly the global differential specialization. -/
theorem zero_result_iff (Q : CPoly.CMvPolynomial (r + 2) F) (P : CPolynomial F)
    (cs : List F) (terms : Equation F) (samples : List F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (points : Fin L ↪ F) (hpoints : samples = List.ofFn (fun i ↦ points i))
    (hdegree : P.natDegree ≤ D) (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    ResidualZeroMachine.result ⟨cs, terms, 0, r⟩ samples = true ↔
      differentialSpecialization (semanticEquation Q) P.toPoly = 0 := by
  rw [ResidualZeroMachine.result_eq_true_iff, ← ResidualWitnessMachine.result_eq_none_iff,
    ResidualWitnessMachine.result_eq_none_iff_residual_zero Q 0 P cs terms samples hP hQ
      points hpoints hdegree hweight, effectiveResidual_eq_zero_iff]
  simp only [unshift, neg_zero, taylor_zero]

/-- Pointwise sparse representations transport the actual previous-equation checks in order. -/
theorem previous_results_iff (P : CPolynomial F) (cs : List F) (samples : List F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (points : Fin L ↪ F) (hpoints : samples = List.ofFn (fun i ↦ points i))
    (hdegree : P.natDegree ≤ D)
    (qs : List (Equation F)) (Qs : List (CPoly.CMvPolynomial (r + 2) F))
    (hrepr : List.Forall₂ (fun terms Q ↦ EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) qs Qs)
    (hweight : ∀ Q ∈ Qs, differentialWeightedDegree D (semanticEquation Q) < L) :
    (∀ q ∈ qs, ResidualZeroMachine.result ⟨cs, q, 0, r⟩ samples = true) ↔
      ∀ Q ∈ Qs, differentialSpecialization (semanticEquation Q) P.toPoly = 0 := by
  revert hweight
  induction hrepr with
  | nil => simp
  | @cons q Q qs Qs hq htail ih =>
      intro hweight
      simp only [List.forall_mem_cons]
      exact and_congr
        (zero_result_iff Q P cs q samples hP hq points hpoints hdegree (hweight Q (by simp)))
        (ih (fun R hR ↦ hweight R (by simp [hR])))

/-- The same bounded execution checks earlier global identities and the first nonzero center.
Sparse representations, degree bounds and materialized distinct samples are explicit inputs. -/
theorem evaluation_runFuel_correct (H : CPoly.CMvPolynomial (r + 2) F)
    (P : CPolynomial F) (cs : List F) (samples : List F) (center : F) (terms : Equation F)
    (qs : List (Equation F)) (Qs : List (CPoly.CMvPolynomial (r + 2) F))
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hH : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial H))
    (hrepr : List.Forall₂ (fun ts Q ↦ EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) qs Qs)
    (points : Fin L ↪ F) (hpoints : samples = List.ofFn (fun i ↦ points i))
    (hdegree : P.natDegree ≤ D)
    (hweight : ∀ Q ∈ Qs, differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨cs, samples, r, center, terms⟩
    ∃ b c, runFuel input (fuel input qs) (.start qs) = (.done b, c) ∧
      c ≤ workBound input qs ∧
      (b = true ↔ (∀ Q ∈ Qs, differentialSpecialization (semanticEquation Q) P.toPoly = 0) ∧
        ∃ pre post, samples = pre ++ center :: post ∧
          (∀ v ∈ pre, (differentialSpecialization (semanticEquation H) P.toPoly).eval v = 0) ∧
          (differentialSpecialization (semanticEquation H) P.toPoly).eval center ≠ 0) := by
  let input : Input F := ⟨cs, samples, r, center, terms⟩
  obtain ⟨c, hr, hc⟩ := evaluation_runFuel input qs
  refine ⟨result input qs, c, hr, hc, ?_⟩
  rw [result_eq_true_iff]
  change ((∀ q ∈ qs, ResidualZeroMachine.result ⟨cs, q, 0, r⟩ samples = true) ∧
    ResidualWitnessMachine.result ⟨cs, terms, 0, r⟩ samples = some center) ↔ _
  rw [previous_results_iff P cs samples hP points hpoints hdegree qs Qs hrepr hweight,
    ResidualWitnessMachine.result_eq_some_iff_residual H 0 P cs terms samples center hP hH]
  simp only [eval_effectiveResidual_eq_jet, zero_add, ← eval_differentialSpecialization]

end Field

end ReedSolomon.HiddenDerivative.CanonicalGuardMachine
