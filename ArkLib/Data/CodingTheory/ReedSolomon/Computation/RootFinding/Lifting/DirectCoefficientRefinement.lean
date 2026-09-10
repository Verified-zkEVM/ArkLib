/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectCoefficientMachine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.DirectRegularCoefficient
/-!
# Same-run refinement of direct coefficient computation

Concrete representation and degree premises connect both executed coefficient recoveries to the
zero/one affine evaluations. The actual indexed update supplies the second representation. Every
requested coefficient is obtained through the machine's cursor, and the cost bound covers that
same execution. Positive lift order is required only for the final affine soundness consequence.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.DirectCoefficientMachine

open Polynomial Matrix CompPoly PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Uniform polynomial fuel for both recoveries, update, two lookups and scalar instructions. -/
def fuel (input : Input F) (L k n : ℕ) : ℕ :=
  2 * ResidualCoefficientMachine.fuel input L n + 2 * input.coefficients.length + 2 * k + 20
/-- Full inherited recovery work plus every wrapper, update, lookup and quotient operation. -/
def workBound (input : Input F) (L k n : ℕ) : ℕ :=
  2 * ResidualCoefficientMachine.workBound input L n +
    6 * ResidualCoefficientMachine.fuel input L n + 40 * (input.coefficients.length + 1) +
    14 * k + 100

omit [DecidableEq F] in
private theorem recovery_fuel_eq (input : Input F) (cs : List F) (L n : ℕ)
    (h : cs.length = input.coefficients.length) :
    ResidualCoefficientMachine.fuel (withCoefficients input cs) L n =
      ResidualCoefficientMachine.fuel input L n := by
  simp only [ResidualCoefficientMachine.fuel, ResidualSystemMachine.fuel,
    ResidualBatchMachine.fuel, ResidualBatchMachine.singleFuel, ResidualBatchMachine.sampleInput,
    ResidualSampleMachine.fuel, ResidualSampleMachine.jetFuel, ResidualSampleMachine.scalarFuel,
    withCoefficients, h]

omit [DecidableEq F] in
private theorem recovery_work_eq (input : Input F) (cs : List F) (L n : ℕ)
    (h : cs.length = input.coefficients.length) :
    ResidualCoefficientMachine.workBound (withCoefficients input cs) L n =
      ResidualCoefficientMachine.workBound input L n := by
  simp only [ResidualCoefficientMachine.workBound, ResidualSystemMachine.workBound,
    ResidualSystemMachine.fuel, ResidualBatchMachine.fuel, ResidualBatchMachine.cost,
    ResidualBatchMachine.itemCost, ResidualBatchMachine.singleCost, ResidualBatchMachine.singleFuel,
    ResidualBatchMachine.sampleInput, ResidualSampleMachine.fuel, ResidualSampleMachine.cost,
    ResidualSampleMachine.jetFuel, ResidualSampleMachine.scalarFuel, withCoefficients, h]

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, ResidualCoefficientMachine.totalCost, ResidualCoefficientMachine.cost_add,
    PivotSelectionMachine.totalCost, PivotEliminationMachine.cost_add, RowReductionMachine.cost_add]
  omega

private theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n := by
  simp [totalCost, ResidualCoefficientMachine.totalCost, wrapperCost,
    ResidualCoefficientMachine.wrapperCost, PivotSelectionMachine.totalCost]
  omega

private theorem total_update (c : CoefficientUpdateMachine.Cost) :
    totalCost (updateCost c) = CoefficientUpdateMachine.totalCost c := by
  simp only [totalCost, ResidualCoefficientMachine.totalCost, updateCost,
    PivotSelectionMachine.totalCost, CoefficientUpdateMachine.totalCost]
  omega

private theorem total_traversal (n : ℕ) : totalCost (traversalCost n) = 7 * n := by
  simp [totalCost, ResidualCoefficientMachine.totalCost, traversalCost,
    PivotSelectionMachine.totalCost]
  omega

/-- Actual execution equals the direct regular coefficient solver. Both residuals obey the
strict degree budget, and physical width/index premises justify the executed update and lookups. -/
theorem computation_runFuel_correct {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (cs : List F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (w k : ℕ)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hwidth : cs.length = w) (hindex : k + r < w) (hk : k < L)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hdegree : P.natDegree ≤ D)
    (hdegreeOne : (effectiveRegularCandidate k r P 1).natDegree ≤ D)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨cs, terms, center, r⟩
    ∃ c, runFuel input w L k (fuel input L k samples.length) (.start samples) =
      (.done (effectiveDirectRegularCoefficient Q center P k), c) ∧
      totalCost c ≤ workBound input L k samples.length := by
  dsimp only
  let input : Input F := ⟨cs, terms, center, r⟩
  have hj : w - 1 - (k + r) < cs.length := by omega
  obtain ⟨updated, hupdate, hlen, hpoly, hucost⟩ :=
    CoefficientUpdateMachine.update_runFuel (1 : F) (w - 1 - (k + r)) cs hj
  have hexp : cs.length - 1 - (w - 1 - (k + r)) = k + r := by omega
  have hplus : JetHornerMachine.coefficientPolynomial updated =
      (effectiveRegularCandidate k r P 1).toPoly := by
    rw [hpoly, hP, hexp, effectiveRegularCandidate_toPoly, C_mul_X_pow_eq_monomial]
  have hPzero : JetHornerMachine.coefficientPolynomial cs =
      (effectiveRegularCandidate k r P 0).toPoly := by
    simpa [effectiveRegularCandidate_toPoly] using hP
  have hdegreeZero : (effectiveRegularCandidate k r P 0).natDegree ≤ D := by
    simpa [CPolynomial.natDegree_toPoly, effectiveRegularCandidate_toPoly] using hdegree
  obtain ⟨outZero, cz, hz, hlenz, hcoeffz, hcz⟩ :=
    ResidualCoefficientMachine.computation_runFuel_coefficients Q center
      (effectiveRegularCandidate k r P 0) cs terms points samples hsamples hPzero hQ
      hdegreeZero hweight
  obtain ⟨outOne, co, ho, hleno, hcoeffo, hco⟩ :=
    ResidualCoefficientMachine.computation_runFuel_coefficients Q center
      (effectiveRegularCandidate k r P 1) updated terms points samples hsamples hplus hQ
      hdegreeOne hweight
  obtain ⟨nz, hnz, htz⟩ := ResidualCoefficientMachine.runFuel_refines
    input L (ResidualCoefficientMachine.fuel input L samples.length) (.start samples)
  change ResidualCoefficientMachine.runFuel input L _ _ = _ at hz
  rw [hz] at htz
  obtain ⟨no, hno, hto⟩ := ResidualCoefficientMachine.runFuel_refines
    (withCoefficients input updated) L
    (ResidualCoefficientMachine.fuel (withCoefficients input updated) L samples.length)
    (.start samples)
  change ResidualCoefficientMachine.runFuel (withCoefficients input updated) L
    (ResidualCoefficientMachine.fuel (withCoefficients input updated) L samples.length)
    (.start samples) = (.done (some outOne), co) at ho
  rw [ho] at hto
  rw [recovery_fuel_eq input updated L samples.length hlen] at hno
  change totalCost cz ≤ ResidualCoefficientMachine.workBound input L samples.length at hcz
  change totalCost co ≤
    ResidualCoefficientMachine.workBound (withCoefficients input updated) L samples.length at hco
  rw [recovery_work_eq input updated L samples.length hlen] at hco
  obtain ⟨nu, hnu, htu⟩ := CoefficientUpdateMachine.runFuel_refines (1 : F)
    (2 * cs.length + 5) (.start cs (w - 1 - (k + r)))
  rw [hupdate] at htu
  obtain ⟨tailz, hlz⟩ := lookup_trace input w L k none samples outZero k (by omega)
  obtain ⟨tailo, hlo⟩ := lookup_trace input w L k (some (outZero.getD k 0)) samples outOne k
    (by omega)
  obtain ⟨na, ca, hta, hna, hca⟩ := arithmetic_trace input w L k
    (outZero.getD k 0) (outOne.getD k 0)
  have hfirst : withCoefficients input input.coefficients = input := rfl
  rw [← hfirst] at htz
  have ht := Trace.cons (Step.start (input := input) (w := w) (L := L) (k := k))
    ((lift_recover input w L k none input.coefficients samples htz).trans
      (Trace.cons Step.recoverReturn (hlz.trans (Trace.cons Step.selectZero
        ((lift_update input w L k (outZero.getD k 0) samples htu).trans
          (Trace.cons Step.updateReturn
            ((lift_recover input w L k (some (outZero.getD k 0)) updated samples hto).trans
              (Trace.cons Step.recoverReturn
                (hlo.trans (Trace.cons Step.selectOne hta))))))))))
  have hresult : result (outZero.getD k 0) (outOne.getD k 0) =
      effectiveDirectRegularCoefficient Q center P k := by
    have hzcoeff := hcoeffz ⟨k, hk⟩
    have hocoeff := hcoeffo ⟨k, hk⟩
    change outZero.getD k 0 = effectiveResidualCoeff Q center P k 0 at hzcoeff
    change outOne.getD k 0 = effectiveResidualCoeff Q center P k 1 at hocoeff
    simp only [result, hzcoeff, hocoeff, effectiveDirectRegularCoefficient]
  rw [hresult] at ht
  dsimp only [input] at hnz hno hcz hco
  have hf : nz + ((k + ((nu + ((no + ((k + (na + 1)) + 1)) + 1)) + 1)) + 1) + 1 ≤
      fuel input L k samples.length := by
    dsimp [fuel, input]
    omega
  have hr := ht.runFuel_done (fuel input L k samples.length -
    (nz + ((k + ((nu + ((no + ((k + (na + 1)) + 1)) + 1)) + 1)) + 1) + 1))
  rw [Nat.add_sub_of_le hf] at hr
  refine ⟨_, hr, ?_⟩
  simp only [total_add, total_wrapper, total_update, total_traversal]
  change 6 + (totalCost cz + 3 * nz + (5 + (7 * k +
    (14 + (CoefficientUpdateMachine.totalCost (CoefficientUpdateMachine.successCost
      (w - 1 - (k + r))) + 3 * nu + (7 + (totalCost co + 3 * no +
        (5 + (7 * k + (5 + totalCost ca)))))))))) ≤ _
  dsimp [workBound, input]
  change totalCost ca ≤ 27 at hca
  omega

/-- A scalar emitted at positive lift order is the unique annihilating next coefficient.
The existence and cost statement refer to the actual execution, including both lookups. -/
theorem computation_runFuel_sound_unique {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (cs : List F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (w k : ℕ)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hwidth : cs.length = w) (hindex : k + r < w) (hk : k < L) (hpositive : 0 < k)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hdegree : P.natDegree ≤ D)
    (hdegreeOne : (effectiveRegularCandidate k r P 1).natDegree ≤ D)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨cs, terms, center, r⟩
    ∃ out c, runFuel input w L k (fuel input L k samples.length) (.start samples) =
      (.done out, c) ∧ totalCost c ≤ workBound input L k samples.length ∧
      (∀ gamma, out = some gamma → effectiveResidualCoeff Q center P k gamma = 0 ∧
        ∀ other, effectiveResidualCoeff Q center P k other = 0 → other = gamma) := by
  obtain ⟨c, hrun, hcost⟩ := computation_runFuel_correct Q center P cs terms w k points samples
    hsamples hwidth hindex hk hP hQ hdegree hdegreeOne hweight
  refine ⟨effectiveDirectRegularCoefficient Q center P k, c, hrun, hcost, ?_⟩
  intro gamma hgamma
  exact effectiveDirectRegularCoefficient_sound_unique Q center P k hpositive gamma hgamma

end ReedSolomon.HiddenDerivative.DirectCoefficientMachine
