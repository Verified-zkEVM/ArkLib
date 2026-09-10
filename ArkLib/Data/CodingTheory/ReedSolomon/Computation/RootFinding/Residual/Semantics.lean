/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualCoefficientMachine
/-!
# Executed residual coefficient recovery

Strict degree, distinct samples and concrete input representations discharge consistency and
identify every coefficient emitted by the actual sampling/elimination/back-substitution machine.
The same execution includes charged zero-seed allocation and satisfies the primitive work bound.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualCoefficientMachine

open PolynomialDifferential
open Polynomial Matrix CompPoly
open scoped Matrix

variable {F : Type*} [Field F] [DecidableEq F] {r D L : ℕ}

/-- The executed machine emits precisely the residual coefficients, with no assumed solver. -/
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
    ∃ out c, runFuel input L (fuel input L samples.length) (.start samples) =
      (.done (some out), c) ∧ out.length = L ∧
      (∀ i : Fin L, out.getD i.val 0 = (effectiveResidual Q center P).coeff i.val) ∧
      totalCost c ≤ workBound input L samples.length := by
  dsimp only
  have hdeg := natDegree_effectiveResidual_lt Q center P hdegree hweight
  have hc : ∃ x : ℕ → F, PivotSelectionMachine.Satisfies
      (VandermondeMachine.rowsSpec L (ResidualBatchMachine.outputSpec
        (⟨cs, terms, center, r⟩ : Input F) samples)) x := by
    refine ⟨fun i ↦ (effectiveResidual Q center P).toPoly.coeff i, ?_⟩
    rw [ResidualSystemMachine.outputSpec_eq_samples Q center P cs terms points samples
      hsamples hP hQ, VandermondeMachine.rowsSpec_satisfies]
    exact Polynomial.vandermonde_coefficients_eq_samples (fun i ↦ points i) _ hdeg
  obtain ⟨out, c, hrun, hlen, hsolve, hcost⟩ :=
    computation_runFuel (⟨cs, terms, center, r⟩ : Input F) L samples hc
  refine ⟨out, c, hrun, hlen, ?_, hcost⟩
  rw [ResidualSystemMachine.outputSpec_eq_samples Q center P cs terms points samples
    hsamples hP hQ, VandermondeMachine.rowsSpec_satisfies] at hsolve
  have hcoeff := Polynomial.coefficients_eq_of_vandermonde_solve points
    (effectiveResidual Q center P).toPoly hdeg (fun i ↦ out.getD i.val 0) hsolve
  intro i
  simpa only [CPolynomial.coeff_toPoly] using congrFun hcoeff i

end ReedSolomon.HiddenDerivative.ResidualCoefficientMachine
