/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSystemMachine
/-!
# Coefficient meaning of the executed residual system

The actual sample/matrix/elimination computation produces equations whose solutions are exactly
the coefficient vectors of the concrete residual. The input representations, strict residual
degree bound, and distinct materialized sample points are explicit hypotheses. No linear-system
solver is assumed: the conclusion characterizes the equations returned by actual execution.
Back-substitution is the remaining step needed to return their unique coefficient vector.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualSystemMachine

open PolynomialDifferential
open Polynomial Matrix CompPoly
open scoped Matrix

variable {F : Type*} [Field F] [DecidableEq F] {r D L : ℕ}

/-- The ordered pairs emitted by residual sampling represent the intended finite sample vector. -/
theorem outputSpec_eq_samples (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (cs : List F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) :
    ResidualBatchMachine.outputSpec (⟨cs, terms, center, r⟩ : Input F) samples =
      List.ofFn (fun i ↦ (points i, (effectiveResidual Q center P).toPoly.eval (points i))) := by
  rw [hsamples]
  simp only [ResidualBatchMachine.outputSpec, List.map_ofFn, Function.comp_def]
  congr 1
  funext i
  rw [ResidualBatchMachine.sampleValue_eq_effectiveResidual Q center (points i) P cs terms hP hQ]

/-- Executed echelon equations determine precisely every residual coefficient below its degree
budget. The cost bounds the same execution producing those equations, not an abstract solve. -/
theorem computation_runFuel_coefficients (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (cs : List F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hdegree : P.natDegree ≤ D)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨cs, terms, center, r⟩
    ∃ ps rest c, runFuel input L (fuel input L samples.length) (.start samples) =
      (.done ps rest, c) ∧ ForwardEchelonMachine.Echelon L 0 ps rest ∧
      totalCost c ≤ workBound input L samples.length ∧
      (∀ x : ℕ → F, ForwardEchelonMachine.Solutions ps rest x ↔
        ∀ i : Fin L, x i.val = (effectiveResidual Q center P).coeff i.val) := by
  dsimp only
  obtain ⟨ps, rest, c, hrun, hechelon, _hcount, hsystem, hcost⟩ :=
    computation_runFuel (⟨cs, terms, center, r⟩ : Input F) L samples
  refine ⟨ps, rest, c, hrun, hechelon, hcost, ?_⟩
  intro x
  rw [hsystem x, outputSpec_eq_samples Q center P cs terms points samples hsamples hP hQ,
    VandermondeMachine.rowsSpec_satisfies]
  change Matrix.vandermonde (fun i ↦ points i) *ᵥ (fun i ↦ x i.val) =
      (fun i ↦ (effectiveResidual Q center P).toPoly.eval (points i)) ↔ _
  have hdeg := natDegree_effectiveResidual_lt Q center P hdegree hweight
  constructor
  · intro hsolve
    have hcoeff := Polynomial.coefficients_eq_of_vandermonde_solve points
      (effectiveResidual Q center P).toPoly hdeg (fun i ↦ x i.val) hsolve
    intro i
    simpa only [CPolynomial.coeff_toPoly] using congrFun hcoeff i
  · intro hcoeff
    have hx : (fun i : Fin L ↦ x i.val) =
        (fun i : Fin L ↦ (effectiveResidual Q center P).toPoly.coeff i.val) := by
      funext i
      simpa only [CPolynomial.coeff_toPoly] using hcoeff i
    rw [hx]
    exact Polynomial.vandermonde_coefficients_eq_samples (fun i ↦ points i) _ hdeg

end ReedSolomon.HiddenDerivative.ResidualSystemMachine
