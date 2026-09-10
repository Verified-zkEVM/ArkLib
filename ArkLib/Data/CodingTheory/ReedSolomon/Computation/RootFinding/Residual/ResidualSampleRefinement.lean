/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSampleMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Residual.SampledResidual
/-!
# Concrete residual refinement for the closed sample machine

The descending coefficient list and sparse term list are supplied as materialized inputs, with
explicit equalities to their concrete polynomial interpretations. Finite variable renaming proves
the arity bound. No noncomputable list construction is used by the machine, and input preparation
remains outside its stated costs.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualSampleMachine

open PolynomialDifferential
open Polynomial MvPolynomial CompPoly
open scoped Matrix

variable {F : Type*} [Field F] [DecidableEq F] {r D L : ℕ}

omit [DecidableEq F] in
/-- Finite concrete equation variables imply the sample machine's arity bound. -/
theorem renamed_equation_arity (Q : CPoly.CMvPolynomial (r + 2) F) :
    ∀ i ∈ (MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)).vars, i < r + 2 := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := MvPolynomial.mem_vars_rename Fin.val (CPoly.fromCMvPolynomial Q) hi
  exact j.isLt

omit [DecidableEq F] in
private theorem renamed_equation_eval (Q : CPoly.CMvPolynomial (r + 2) F)
    (center u : F) (P : CPolynomial F)
    (cs : List F) (terms : List (EvaluationMachine.Term F)) :
    MvPolynomial.eval (jetValuation ⟨cs, terms, center, u, r⟩ P.toPoly)
      (MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) =
        jetEvaluation (semanticEquation Q) (center + u) (polynomialJet u P.toPoly) := by
  rw [MvPolynomial.eval_rename, jetEvaluation, semanticEquation, MvPolynomial.eval_rename]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [finToJetVariable, jetValuation]
  · simp [finToJetVariable, jetValuation, polynomialJet,
      Polynomial.hasseJet, Polynomial.hasseCoeffAt]

/-- Actual closed execution returns the concrete residual's scalar sample. Only representation
proofs are supplied; no evaluator callback or arbitrary output value is passed to the machine. -/
theorem evaluation_runFuel_eq_effectiveResidual
    (Q : CPoly.CMvPolynomial (r + 2) F) (center u : F) (P : CPolynomial F)
    (cs : List F) (terms : List (EvaluationMachine.Term F))
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) :
    let input : Input F := ⟨cs, terms, center, u, r⟩
    runFuel input (fuel input) .start =
      (.done ((effectiveResidual Q center P).toPoly.eval u), cost input) := by
  have h := evaluation_runFuel_eq_jet (⟨cs, terms, center, u, r⟩ : Input F)
    P.toPoly (MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) hP hQ
    (renamed_equation_arity Q)
  rw [renamed_equation_eval, ← eval_effectiveResidual_eq_jet] at h
  exact h

/-- A mathematically correct solve on values produced by the closed sample machine recovers
actual residual coefficients. This attaches no execution or cost claim to the supplied solve. -/
theorem coefficients_eq_of_sample_runs
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (cs : List F) (terms : List (EvaluationMachine.Term F))
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hdegree : P.natDegree ≤ D) (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (points : Fin L ↪ F) (values coefficients : Fin L → F)
    (hrun : ∀ i, let input : Input F := ⟨cs, terms, center, points i, r⟩
      runFuel input (fuel input) .start = (.done (values i), cost input))
    (hsolve : Matrix.vandermonde (fun i ↦ points i) *ᵥ coefficients = values) :
    coefficients = fun j : Fin L ↦ (effectiveResidual Q center P).coeff j := by
  have hvalues : values = fun i ↦ jetEvaluation (semanticEquation Q) (center + points i)
      (polynomialJet (points i) P.toPoly) := by
    funext i
    have h := congrArg Prod.fst ((hrun i).symm.trans
      (evaluation_runFuel_eq_effectiveResidual Q center (points i) P cs terms hP hQ))
    have hvalue := Configuration.done.inj h
    simpa only [eval_effectiveResidual_eq_jet] using hvalue
  exact effectiveResidual_coefficients_of_samples Q center P hdegree hweight points coefficients
    (hsolve.trans hvalues)

/-- Under the explicit degree budget, zero outputs at all distinct samples are equivalent to the
full concrete residual being zero. The equality includes each run's exact cost. -/
theorem effectiveResidual_eq_zero_iff_zero_runs
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (cs : List F) (terms : List (EvaluationMachine.Term F))
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hdegree : P.natDegree ≤ D) (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (points : Fin L ↪ F) :
    effectiveResidual Q center P = 0 ↔ ∀ i,
      let input : Input F := ⟨cs, terms, center, points i, r⟩
      runFuel input (fuel input) .start = (.done 0, cost input) := by
  rw [effectiveResidual_eq_zero_iff_samples Q center P hdegree hweight points]
  apply forall_congr'
  intro i
  dsimp only
  rw [evaluation_runFuel_eq_effectiveResidual Q center (points i) P cs terms hP hQ]
  simp only [Prod.mk.injEq, Configuration.done.injEq, and_true, eval_effectiveResidual_eq_jet]

end ReedSolomon.HiddenDerivative.ResidualSampleMachine
