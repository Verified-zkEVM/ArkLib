/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Machine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.DirectRegularIteration
public import ArkLib.Data.Polynomial.DegreeTruncationSemantics
/-!
# Whole-candidate refinement of the regular lifting loop

A fixed physical width supplies every intermediate degree bound. The actual loop agrees with
functional direct lifting on the complete represented polynomial, including early failure.
Regularity identifies its result with the exhaustive prefix interface. Full residual acceptance
is deliberately separate: a completed prefix is not yet certified as a differential root.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.RegularLiftMachine

open Polynomial Matrix CompPoly PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Proof-only forward iteration, parameterized by the next residual order. -/
def liftFrom {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (k : ℕ) : ℕ → CPolynomial F → Option (CPolynomial F)
  | 0, P => some P
  | n + 1, P => (effectiveDirectRegularCoefficient Q center P k).bind fun gamma ↦
      liftFrom Q center (k + 1) n (effectiveRegularCandidate k r P gamma)

/-- Forward iteration composes with every already-computed functional prefix. -/
theorem liftFrom_iteration {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CPolynomial F) (n s : ℕ) :
    (directRegularIteration Q center P s).bind (liftFrom Q center (s + 1) n) =
      directRegularIteration Q center P (s + n) := by
  induction n generalizing s with
  | zero => simp [liftFrom]
  | succ n ih =>
      rw [show s + (n + 1) = (s + 1) + n by omega, ← ih (s + 1)]
      rw [directRegularIteration]
      simp only [liftFrom, Option.bind_assoc, Option.bind_map, Function.comp_def]

/-- The stage fuel includes one direct solve, one vector update and administrative transitions. -/
def stageFuel (input : Input F) (D L n : ℕ) : ℕ :=
  DirectCoefficientMachine.fuel input L (D + 1) n + 2 * (D + 1) + 10
/-- Retain all inner costs and all direct/update wrapper transitions. -/
def stageWork (input : Input F) (D L n : ℕ) : ℕ :=
  DirectCoefficientMachine.workBound input L (D + 1) n +
    3 * DirectCoefficientMachine.fuel input L (D + 1) n + 40 * (D + 2) + 40
/-- Uniform fuel through ambient degree, including initialization and final emission. -/
def fuel (input : Input F) (D L n : ℕ) : ℕ :=
  (D - input.order) * stageFuel input D L n + 3
/-- Polynomial primitive work through ambient degree. -/
def workBound (input : Input F) (D L n : ℕ) : ℕ :=
  (D - input.order) * stageWork input D L n + 16

omit [DecidableEq F] in
private theorem direct_bounds (input : Input F) (cs : List F) (D L k n : ℕ)
    (hlen : cs.length = input.coefficients.length) (hk : k ≤ D + 1) :
    DirectCoefficientMachine.fuel (withCoefficients input cs) L k n ≤
      DirectCoefficientMachine.fuel input L (D + 1) n ∧
    DirectCoefficientMachine.workBound (withCoefficients input cs) L k n ≤
      DirectCoefficientMachine.workBound input L (D + 1) n := by
  simp only [DirectCoefficientMachine.fuel, DirectCoefficientMachine.workBound,
    ResidualCoefficientMachine.fuel, ResidualCoefficientMachine.workBound,
    ResidualSystemMachine.fuel, ResidualSystemMachine.workBound,
    ResidualBatchMachine.fuel, ResidualBatchMachine.cost, ResidualBatchMachine.itemCost,
    ResidualBatchMachine.singleFuel, ResidualBatchMachine.singleCost,
    ResidualBatchMachine.sampleInput, ResidualSampleMachine.fuel, ResidualSampleMachine.cost,
    ResidualSampleMachine.jetFuel, ResidualSampleMachine.scalarFuel,
    withCoefficients, DirectCoefficientMachine.withCoefficients, hlen]
  constructor <;> omega

omit [DecidableEq F] in
private theorem represented_degree (cs : List F) (P : CPolynomial F) (D : ℕ)
    (hlen : cs.length = D + 1) (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly) :
    P.natDegree ≤ D := by
  classical
  have h := JetHornerMachine.degree_coefficientPolynomial_lt_length cs
  rw [hP, hlen] at h
  rw [CPolynomial.natDegree_toPoly]
  by_cases hp : P.toPoly = 0
  · simp [hp]
  · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hp).mpr h)

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost,
    ResidualCoefficientMachine.cost_add, PivotSelectionMachine.totalCost,
    PivotEliminationMachine.cost_add, RowReductionMachine.cost_add]
  omega

private theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n := by
  simp [totalCost, DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost,
    wrapperCost, DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
    PivotSelectionMachine.totalCost]
  omega

private theorem total_update (c : CoefficientUpdateMachine.Cost) :
    totalCost (updateCost c) = CoefficientUpdateMachine.totalCost c := by
  simp only [totalCost, DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost,
    updateCost, DirectCoefficientMachine.updateCost, PivotSelectionMachine.totalCost,
    CoefficientUpdateMachine.totalCost]
  omega

/-- Every permitted continuation terminates with the entire functional lift, preserving width.
No degree hypothesis is assumed for intermediate polynomials: their materialized width proves it. -/
theorem loop_trace {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (initial : List F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (hwidth : initial.length = D + 1) (remaining k : ℕ) (cs : List F) (P : CPolynomial F)
    (hlen : cs.length = D + 1) (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hindex : k + remaining + r ≤ D + 1) (hlookup : k + remaining ≤ L) :
    let input : Input F := ⟨initial, terms, center, r⟩
    ∃ out steps c, Trace input D L steps (.loop k remaining cs samples) c (.done out) ∧
      out.map JetHornerMachine.coefficientPolynomial = (liftFrom Q center k remaining P).map
        CPolynomial.toPoly ∧
      (∀ xs, out = some xs → xs.length = D + 1) ∧
      steps ≤ remaining * stageFuel input D L samples.length + 2 ∧
      totalCost c ≤ remaining * stageWork input D L samples.length + 8 := by
  let input : Input F := ⟨initial, terms, center, r⟩
  induction remaining generalizing k cs P with
  | zero =>
      refine ⟨some cs, 2, finishCost + (emitCost + 0),
        Trace.cons Step.finish (Trace.cons Step.emit (Trace.nil _)), ?_, ?_, by simp, ?_⟩
      · simp [liftFrom, hP]
      · intro xs hxs; cases hxs; exact hlen
      · simp only [Nat.zero_mul, Nat.zero_add]
        decide
  | succ remaining ih =>
      have hk : k < L := by omega
      have hkr : k + r < D + 1 := by omega
      have hdegree := represented_degree cs P D hlen hP
      have hdegreeOne : (effectiveRegularCandidate k r P 1).natDegree ≤ D := by
        rw [effectiveRegularCandidate]
        apply (CPolynomial.natDegree_add_le _ _).trans
        apply max_le hdegree
        rw [CPolynomial.natDegree_monomial one_ne_zero]
        omega
      obtain ⟨cd, hd, hcd⟩ := DirectCoefficientMachine.computation_runFuel_correct Q center P cs
        terms (D + 1) k points samples hsamples hlen hkr hk hP hQ hdegree hdegreeOne hweight
      obtain ⟨nd, hnd, htd⟩ := DirectCoefficientMachine.runFuel_refines
        (withCoefficients input cs) (D + 1) L k
        (DirectCoefficientMachine.fuel (withCoefficients input cs) L k samples.length)
        (.start samples)
      change DirectCoefficientMachine.runFuel (withCoefficients input cs) (D + 1) L k
        (DirectCoefficientMachine.fuel (withCoefficients input cs) L k samples.length)
        (.start samples) = (.done (effectiveDirectRegularCoefficient Q center P k), cd) at hd
      rw [hd] at htd
      obtain ⟨hdfuel, hdwork⟩ := direct_bounds input cs D L k samples.length
        (by dsimp [input]; omega) (by omega)
      change totalCost cd ≤
        DirectCoefficientMachine.workBound (withCoefficients input cs) L k samples.length at hcd
      have hnd' := hnd.trans hdfuel
      have hcd' := hcd.trans hdwork
      cases hgamma : effectiveDirectRegularCoefficient Q center P k with
      | none =>
          rw [hgamma] at htd
          have ht := Trace.cons Step.stage ((lift_direct input D L k remaining cs samples htd).trans
            (Trace.cons Step.directReject (Trace.cons Step.emit (Trace.nil _))))
          refine ⟨none, _, _, ht, by simp [liftFrom, hgamma], by simp, ?_, ?_⟩
          · dsimp [stageFuel]
            nlinarith
          · simp only [total_add, total_wrapper]
            change 9 + (totalCost cd + 3 * nd + (3 + (4 + 0))) ≤ _
            dsimp [stageWork]
            nlinarith
      | some gamma =>
          rw [hgamma] at htd
          have hj : D - (k + r) < cs.length := by omega
          obtain ⟨updated, hu, hlenu, hpolyu, hcu⟩ :=
            CoefficientUpdateMachine.update_runFuel gamma (D - (k + r)) cs hj
          have hrep : JetHornerMachine.coefficientPolynomial updated =
              (effectiveRegularCandidate k r P gamma).toPoly := by
            have hexp : cs.length - 1 - (D - (k + r)) = k + r := by omega
            rw [hpolyu, hP, hexp, effectiveRegularCandidate_toPoly, C_mul_X_pow_eq_monomial]
          obtain ⟨nu, hnu, htu⟩ := CoefficientUpdateMachine.runFuel_refines gamma
            (2 * cs.length + 5) (.start cs (D - (k + r)))
          rw [hu] at htu
          obtain ⟨out, nt, ct, htt, hspec, hwidthout, hnt, hct⟩ := ih (k + 1) updated
            (effectiveRegularCandidate k r P gamma) (by omega) hrep (by omega) (by omega)
          have ht := Trace.cons Step.stage ((lift_direct input D L k remaining cs samples htd).trans
            (Trace.cons Step.directReturn
              ((lift_update input D L k remaining samples gamma htu).trans
                (Trace.cons Step.updateReturn htt))))
          refine ⟨out, _, _, ht, ?_, hwidthout, ?_, ?_⟩
          · simpa [liftFrom, hgamma] using hspec
          · dsimp [stageFuel] at hnt ⊢
            nlinarith
          · simp only [total_add, total_wrapper, total_update]
            change 9 + (totalCost cd + 3 * nd + (9 +
              (CoefficientUpdateMachine.totalCost (CoefficientUpdateMachine.successCost
                (D - (k + r))) + 3 * nu + (7 + totalCost ct)))) ≤ _
            dsimp [stageWork] at hct ⊢
            nlinarith

/-- The bounded interpreter emits exactly the whole functional lift in coefficient form.
The initial padded jet and sample vector are supplied; no input materialization is hidden here. -/
theorem computation_runFuel_correct {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (initial : List F) (P : CPolynomial F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hwidth : initial.length = D + 1)
    (hP : JetHornerMachine.coefficientPolynomial initial = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨initial, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done out, c) ∧
      out.map JetHornerMachine.coefficientPolynomial =
        (directRegularIteration Q center P (D - r)).map CPolynomial.toPoly ∧
      (∀ xs, out = some xs → xs.length = D + 1) ∧
      totalCost c ≤ workBound input D L samples.length := by
  let input : Input F := ⟨initial, terms, center, r⟩
  obtain ⟨out, steps, c, ht, hspec, hlen, hf, hc⟩ := loop_trace Q center terms initial points
    samples hsamples hQ hweight hwidth (D - r) 1 initial P hwidth hP (by omega) (by omega)
  have hfrom := liftFrom_iteration Q center P (D - r) 0
  simp only [directRegularIteration, Option.bind_some, Nat.zero_add] at hfrom
  rw [hfrom] at hspec
  have hentry := Trace.cons (Step.start (input := input)) ht
  have hbound : steps + 1 ≤ fuel input D L samples.length := by
    dsimp [fuel, input]
    omega
  have hrun := hentry.runFuel_done (fuel input D L samples.length - (steps + 1))
  rw [Nat.add_sub_of_le hbound] at hrun
  refine ⟨out, startCost + c, hrun, hspec, hlen, ?_⟩
  rw [total_add]
  change 8 + totalCost c ≤ _
  dsimp [workBound, input]
  omega

/-- For a regular initial jet below the characteristic, the executed whole candidate is the
unique survivor of the existing exhaustive prefix interface. A full residual check remains
necessary before treating that prefix as a root. -/
theorem computation_runFuel_regular [Fintype F] {r D L : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (initial : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hwidth : initial.length = D + 1)
    (hP : JetHornerMachine.coefficientPolynomial initial = (effectiveInitialPrefix jet).toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (hchar : D < ringChar F) :
    let input : Input F := ⟨initial, terms, center, r⟩
    ∃ out P c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ out.length = D + 1 ∧
      JetHornerMachine.coefficientPolynomial out = P.toPoly ∧
      (effectiveRegularIteration Q center (effectiveInitialPrefix jet) (D - r)).candidates = {P} ∧
      totalCost c ≤ workBound input D L samples.length := by
  obtain ⟨out, c, hrun, hspec, hlen, hcost⟩ := computation_runFuel_correct Q center initial
    (effectiveInitialPrefix jet) terms points samples hsamples hwidth hP hQ hr hlookup hweight
  obtain ⟨P, hdirect, hcandidates⟩ := directRegularIteration_eq_some_and_candidates
    Q center jet hregular D hchar (D - r) le_rfl
  rw [hdirect, Option.map_some] at hspec
  obtain ⟨xs, hxs, hpoly⟩ := Option.map_eq_some_iff.mp hspec
  rw [hxs] at hrun
  exact ⟨xs, P, c, hrun, hlen xs hxs, hpoly, hcandidates, hcost⟩

end ReedSolomon.HiddenDerivative.RegularLiftMachine
