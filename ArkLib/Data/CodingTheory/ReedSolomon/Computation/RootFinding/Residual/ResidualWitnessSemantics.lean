/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualWitnessMachine
/-!
# Ordered residual witnesses

The emitted point is characterized by a list prefix of zero samples followed by a nonzero
sample. A degree bound and sufficiently many distinct samples make failure equivalent to the
full differential identity. Ordering is significant; no distinctness is needed for the search
itself. The same terminating execution and primitive-work bound accompany these semantics.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualWitnessMachine

open PolynomialDifferential
open Polynomial MvPolynomial CompPoly

variable {F : Type*}

section Semiring

variable [CommSemiring F] [DecidableEq F]

/-- The mathematical result follows one ordered zero test at the head of the sample list. -/
theorem result_cons (input : Input F) (u : F) (ps : List F) :
    result input (u :: ps) =
      if ResidualBatchMachine.sampleValue input u = 0 then result input ps else some u := by
  simp [result, ResidualBatchMachine.outputSpec, scanSpec]

/-- Failure means every supplied sample vanishes, including for empty or repeated samples. -/
theorem result_eq_none_iff (input : Input F) (ps : List F) :
    result input ps = none ↔ ∀ u ∈ ps, ResidualBatchMachine.sampleValue input u = 0 := by
  induction ps with
  | nil => simp [result, ResidualBatchMachine.outputSpec, scanSpec]
  | cons u ps ih =>
      by_cases hu : ResidualBatchMachine.sampleValue input u = 0 <;>
        simp [result_cons, hu, ih]

/-- A successful witness has an all-zero prefix and a nonzero value at its selected position. -/
theorem result_eq_some_iff (input : Input F) (ps : List F) (u : F) :
    result input ps = some u ↔ ∃ pre post, ps = pre ++ u :: post ∧
      (∀ v ∈ pre, ResidualBatchMachine.sampleValue input v = 0) ∧
      ResidualBatchMachine.sampleValue input u ≠ 0 := by
  induction ps with
  | nil => simp [result, ResidualBatchMachine.outputSpec, scanSpec]
  | cons a ps ih =>
      rw [result_cons]
      by_cases ha : ResidualBatchMachine.sampleValue input a = 0
      · rw [if_pos ha, ih]
        constructor
        · rintro ⟨pre, post, hps, hpre, hu⟩
          exact ⟨a :: pre, post, by simp [hps], by simpa using And.intro ha hpre, hu⟩
        · rintro ⟨pre, post, hps, hpre, hu⟩
          cases pre with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at hps
              exact False.elim (hu (hps.1 ▸ ha))
          | cons b pre =>
              simp only [List.cons_append, List.cons.injEq] at hps
              exact ⟨pre, post, hps.2, fun v hv ↦ hpre v (by simp [hv]), hu⟩
      · rw [if_neg ha]
        constructor
        · intro h
          cases h
          exact ⟨[], ps, rfl, by simp, ha⟩
        · rintro ⟨pre, post, hps, hpre, _hu⟩
          cases pre with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at hps
              exact congrArg some hps.1
          | cons b pre =>
              simp only [List.cons_append, List.cons.injEq] at hps
              exact False.elim (ha (hps.1 ▸ hpre b (by simp)))

omit [DecidableEq F] in
/-- Two descriptions of the first nonzero sample necessarily select the same point. -/
theorem witness_unique (input : Input F) (ps : List F) {u v : F}
    (hu : ∃ pre post, ps = pre ++ u :: post ∧
      (∀ x ∈ pre, ResidualBatchMachine.sampleValue input x = 0) ∧
      ResidualBatchMachine.sampleValue input u ≠ 0)
    (hv : ∃ pre post, ps = pre ++ v :: post ∧
      (∀ x ∈ pre, ResidualBatchMachine.sampleValue input x = 0) ∧
      ResidualBatchMachine.sampleValue input v ≠ 0) : u = v := by
  classical
  have hu' := (result_eq_some_iff input ps u).mpr hu
  have hv' := (result_eq_some_iff input ps v).mpr hv
  exact Option.some.inj (hu'.symm.trans hv')

end Semiring

section Field

variable [Field F] [DecidableEq F] {r D L : ℕ}

/-- Exact sample semantics: the selected center follows an all-zero residual prefix. -/
theorem result_eq_some_iff_residual (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (cs : List F)
    (terms : List (EvaluationMachine.Term F)) (samples : List F) (u : F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) :
    result ⟨cs, terms, center, r⟩ samples = some u ↔
      ∃ pre post, samples = pre ++ u :: post ∧
        (∀ v ∈ pre, (effectiveResidual Q center P).toPoly.eval v = 0) ∧
        (effectiveResidual Q center P).toPoly.eval u ≠ 0 := by
  rw [result_eq_some_iff]
  simp only [ResidualBatchMachine.sampleValue_eq_effectiveResidual Q center _ P cs terms hP hQ]

/-- Distinct samples exceeding the residual degree make failure equivalent to a full identity. -/
theorem result_eq_none_iff_residual_zero (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (cs : List F)
    (terms : List (EvaluationMachine.Term F)) (samples : List F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (points : Fin L ↪ F) (hpoints : samples = List.ofFn (fun i ↦ points i))
    (hdegree : P.natDegree ≤ D) (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    result ⟨cs, terms, center, r⟩ samples = none ↔ effectiveResidual Q center P = 0 := by
  rw [result_eq_none_iff, effectiveResidual_eq_zero_iff_samples Q center P hdegree hweight points]
  simp only [hpoints, List.mem_ofFn, forall_exists_index]
  constructor
  · intro h i
    have hi := h (points i) i rfl
    rw [ResidualBatchMachine.sampleValue_eq_effectiveResidual Q center (points i) P cs terms hP hQ,
      eval_effectiveResidual_eq_jet] at hi
    exact hi
  · intro h u i hi
    subst u
    rw [ResidualBatchMachine.sampleValue_eq_effectiveResidual Q center (points i) P cs terms hP hQ,
      eval_effectiveResidual_eq_jet]
    exact h i

/-- One actual bounded execution returns a canonical nonzero residual witness or certifies zero. -/
theorem witness_runFuel_correct (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (cs : List F)
    (terms : List (EvaluationMachine.Term F)) (samples : List F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (points : Fin L ↪ F) (hpoints : samples = List.ofFn (fun i ↦ points i))
    (hdegree : P.natDegree ≤ D) (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨cs, terms, center, r⟩
    ∃ out c, runFuel input (fuel input samples.length) (.start samples) = (.done out, c) ∧
      c.total ≤ workBound input samples.length ∧
      (out = none ↔ effectiveResidual Q center P = 0) ∧
      (∀ u, out = some u ↔ ∃ pre post, samples = pre ++ u :: post ∧
        (∀ v ∈ pre, (effectiveResidual Q center P).toPoly.eval v = 0) ∧
        (effectiveResidual Q center P).toPoly.eval u ≠ 0) := by
  obtain ⟨c, hrun, hcost⟩ := witness_runFuel (⟨cs, terms, center, r⟩ : Input F) samples
  exact ⟨_, c, hrun, hcost,
    result_eq_none_iff_residual_zero Q center P cs terms samples hP hQ points hpoints
      hdegree hweight,
    fun u ↦ result_eq_some_iff_residual Q center P cs terms samples u hP hQ⟩

/-- With global coefficients, center zero searches the global differential specialization.
The supplied point list fixes a unique first regular center when the equation is a separant. -/
theorem global_witness_runFuel_correct (Q : CPoly.CMvPolynomial (r + 2) F)
    (P : CPolynomial F) (cs : List F)
    (terms : List (EvaluationMachine.Term F)) (samples : List F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (points : Fin L ↪ F) (hpoints : samples = List.ofFn (fun i ↦ points i))
    (hdegree : P.natDegree ≤ D) (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨cs, terms, 0, r⟩
    ∃ out c, runFuel input (fuel input samples.length) (.start samples) = (.done out, c) ∧
      c.total ≤ workBound input samples.length ∧
      (out = none ↔ differentialSpecialization (semanticEquation Q) P.toPoly = 0) ∧
      (∀ u, out = some u ↔ ∃ pre post, samples = pre ++ u :: post ∧
        (∀ v ∈ pre, (differentialSpecialization (semanticEquation Q) P.toPoly).eval v = 0) ∧
        (differentialSpecialization (semanticEquation Q) P.toPoly).eval u ≠ 0) := by
  have h := witness_runFuel_correct Q 0 P cs terms samples hP hQ points hpoints hdegree hweight
  have hz : effectiveResidual Q 0 P = 0 ↔
      differentialSpecialization (semanticEquation Q) P.toPoly = 0 := by
    constructor
    · intro he
      have hpoly := congrArg CPolynomial.toPoly he
      simpa only [effectiveResidual_toPoly, ← taylor_differentialSpecialization,
        unshift, neg_zero, taylor_zero, CPolynomial.toPoly_zero] using hpoly
    · intro he
      apply CPolynomial.ringEquiv.injective
      simpa only [CPolynomial.ringEquiv_apply, effectiveResidual_toPoly,
        ← taylor_differentialSpecialization, unshift, neg_zero, taylor_zero,
        CPolynomial.toPoly_zero] using he
  simpa only [hz,
    eval_effectiveResidual_eq_jet, zero_add, ← eval_differentialSpecialization] using h

end Field

end ReedSolomon.HiddenDerivative.ResidualWitnessMachine
