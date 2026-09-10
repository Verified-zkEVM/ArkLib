/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.RegularRootMachine
-- The completeness witness is constructed through `ringEquiv.symm`; expose the defining
-- implementation modules so its forward image reduces to `toPoly`.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv
/-!
# Accepted global root semantics

The actual local residual test determines acceptance before actual translation. Whole-vector
refinement includes failure, soundness and completeness for a regular compatible initial jet.
Input jet padding and sample construction remain explicit representation obligations.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.RegularRootMachine

open Polynomial Matrix CompPoly PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Uniform translation fuel at the fixed physical width. -/
def shiftFuel (D : ℕ) : ℕ := (D + 2) * (2 * (D + 1) + 3) + D + 8
/-- Full sampled residual-check work, including its early-exit cursor and wrappers. -/
def zeroWork (input : Input F) (n : ℕ) : ℕ :=
  (ResidualBatchMachine.cost input n).total + 3 * ResidualBatchMachine.fuel input n + 6 * n + 15
/-- Fuel for local identity checking, translation and final tagged output. -/
def suffixFuel (input : Input F) (D n : ℕ) : ℕ :=
  ResidualZeroMachine.fuel input n + shiftFuel D + 3
/-- Full check/translation work with every caller dispatch and output. -/
def suffixWork (input : Input F) (D n : ℕ) : ℕ :=
  zeroWork input n + 3 * ResidualZeroMachine.fuel input n +
    160 * (D + 2) ^ 2 + 3 * shiftFuel D + 13
/-- Uniform fuel for one accepted-root pipeline. -/
def fuel (input : Input F) (D L n : ℕ) : ℕ :=
  RegularLiftMachine.fuel input D L n + suffixFuel input D n + 2
/-- Polynomial primitive work, preserving the full lift, check and translation costs. -/
def workBound (input : Input F) (D L n : ℕ) : ℕ :=
  RegularLiftMachine.workBound input D L n + 3 * RegularLiftMachine.fuel input D L n +
    suffixWork input D n + 10

omit [DecidableEq F] in
private theorem zero_bounds_eq (input : Input F) (cs : List F) (n : ℕ)
    (hlen : cs.length = input.coefficients.length) :
    ResidualZeroMachine.fuel (withCoefficients input cs) n = ResidualZeroMachine.fuel input n ∧
      zeroWork (withCoefficients input cs) n = zeroWork input n := by
  simp only [ResidualZeroMachine.fuel, zeroWork, ResidualBatchMachine.fuel,
    ResidualBatchMachine.cost, ResidualBatchMachine.itemCost, ResidualBatchMachine.singleFuel,
    ResidualBatchMachine.singleCost, ResidualBatchMachine.sampleInput, ResidualSampleMachine.fuel,
    ResidualSampleMachine.cost, ResidualSampleMachine.jetFuel, ResidualSampleMachine.scalarFuel,
    withCoefficients, RegularLiftMachine.withCoefficients,
    DirectCoefficientMachine.withCoefficients, hlen]
  trivial

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
  simp only [totalCost, RegularLiftMachine.totalCost, DirectCoefficientMachine.totalCost,
    ResidualCoefficientMachine.totalCost, ResidualCoefficientMachine.cost_add,
    PivotSelectionMachine.totalCost, PivotEliminationMachine.cost_add, RowReductionMachine.cost_add]
  omega

private theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n := by
  simp [totalCost, RegularLiftMachine.totalCost, DirectCoefficientMachine.totalCost,
    ResidualCoefficientMachine.totalCost, wrapperCost, RegularLiftMachine.wrapperCost,
    DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
    PivotSelectionMachine.totalCost]
  omega

private theorem total_zero (c : ResidualZeroMachine.Cost) : totalCost (zeroCost c) = c.total := by
  simp only [totalCost, RegularLiftMachine.totalCost, DirectCoefficientMachine.totalCost,
    ResidualCoefficientMachine.totalCost, zeroCost, PivotSelectionMachine.totalCost,
    ResidualZeroMachine.Cost.total, JetHornerMachine.Cost.total]
  omega

private theorem total_shift (c : CenterShiftMachine.Cost) : totalCost (shiftCost c) = c.total := by
  simp only [totalCost, RegularLiftMachine.totalCost, DirectCoefficientMachine.totalCost,
    ResidualCoefficientMachine.totalCost, shiftCost, PivotSelectionMachine.totalCost,
    CenterShiftMachine.Cost.total, JetHornerMachine.Cost.total]
  omega

/-- The actual residual Boolean controls the translated output, with no assumed acceptance. -/
theorem suffix_trace {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (initial cs : List F) (P : CPolynomial F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hwidth : initial.length = D + 1) (hlen : cs.length = D + 1)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨initial, terms, center, r⟩
    ∃ out steps c, Trace input D L steps (.check cs (.start samples)) c (.done out) ∧
      out.map JetHornerMachine.coefficientPolynomial =
        (if effectiveResidual Q center P = 0 then some (unshift center P) else none) ∧
      (∀ xs, out = some xs → xs.length = D + 1) ∧
      steps ≤ suffixFuel input D samples.length ∧
      totalCost c ≤ suffixWork input D samples.length := by
  let input : Input F := ⟨initial, terms, center, r⟩
  have hdegree := represented_degree cs P D hlen hP
  obtain ⟨b, hb, hbiff⟩ := ResidualZeroMachine.zero_runFuel_iff_residual_zero Q center P cs
    terms samples hP hQ points hsamples hdegree hweight
  obtain ⟨nz, hnz, htz⟩ := ResidualZeroMachine.runFuel_refines (withCoefficients input cs)
    (ResidualZeroMachine.fuel (withCoefficients input cs) samples.length) (.start samples)
  change ResidualZeroMachine.runFuel (withCoefficients input cs)
    (ResidualZeroMachine.fuel (withCoefficients input cs) samples.length) (.start samples) =
      (.done b, ResidualZeroMachine.cost (withCoefficients input cs) samples) at hb
  rw [hb] at htz
  have hcz := ResidualZeroMachine.cost_total_le (withCoefficients input cs) samples
  change (ResidualZeroMachine.cost (withCoefficients input cs) samples).total ≤
    zeroWork (withCoefficients input cs) samples.length at hcz
  obtain ⟨hfeq, hweq⟩ := zero_bounds_eq input cs samples.length (by dsimp [input]; omega)
  rw [hfeq] at hnz
  rw [hweq] at hcz
  dsimp only [input] at hnz hcz
  cases b with
  | false =>
      have hnot : effectiveResidual Q center P ≠ 0 := by simpa using hbiff.symm
      have ht := (lift_check input D L cs htz).trans
        (Trace.cons Step.rejected (Trace.cons Step.emit (Trace.nil _)))
      refine ⟨none, _, _, ht, by simp [hnot], by simp, ?_, ?_⟩
      · dsimp [suffixFuel]
        omega
      · simp only [total_add, total_zero, total_wrapper]
        change (ResidualZeroMachine.cost (withCoefficients input cs) samples).total +
          3 * nz + (6 + (4 + 0)) ≤ _
        dsimp [suffixWork, input]
        omega
  | true =>
      have hzero : effectiveResidual Q center P = 0 := hbiff.mp rfl
      obtain ⟨global, hs, hglength, hgpoly⟩ := CenterShiftMachine.shift_correct
        ⟨cs, center, D⟩ P.toPoly hP hlen
      obtain ⟨ns, hns, hts⟩ := CenterShiftMachine.runFuel_refines
        (⟨cs, center, D⟩ : CenterShiftMachine.Input F)
        (CenterShiftMachine.fuel ⟨cs, center, D⟩) .start
      rw [hs] at hts
      have hsf : CenterShiftMachine.fuel (⟨cs, center, D⟩ : CenterShiftMachine.Input F) =
          shiftFuel D := by
        simp [CenterShiftMachine.fuel, CenterShiftMachine.jetFuel,
          CenterShiftMachine.preparationFuel, shiftFuel, hlen, Nat.add_assoc]
      rw [hsf] at hns
      have hsc := CenterShiftMachine.cost_total_le ⟨cs, center, D⟩ hlen
      change (CenterShiftMachine.cost ⟨cs, center, D⟩).total ≤ 160 * (D + 2) ^ 2 at hsc
      have ht := (lift_check input D L cs htz).trans
        (Trace.cons Step.accepted ((lift_shift input D L cs hts).trans
          (Trace.cons Step.shifted (Trace.cons Step.emit (Trace.nil _)))))
      refine ⟨some global, _, _, ht, ?_, ?_, ?_, ?_⟩
      · simp only [Option.map_some, hzero, ↓reduceIte, Option.some.injEq]
        rw [hgpoly, unshift, taylor_apply]
        simp [sub_eq_add_neg]
      · intro xs hxs; cases hxs; exact hglength
      · dsimp [suffixFuel]
        omega
      · simp only [total_add, total_zero, total_shift, total_wrapper]
        change (ResidualZeroMachine.cost (withCoefficients input cs) samples).total +
          3 * nz + (6 + ((CenterShiftMachine.cost ⟨cs, center, D⟩).total +
            3 * ns + (3 + (4 + 0)))) ≤ _
        dsimp [suffixWork, input]
        omega

private theorem Trace.runFuel_of_le {input : Input F} {D L n budget : ℕ}
    {s : Configuration F} {c : Cost} {out : Option (List F)}
    (h : Trace input D L n s c (.done out)) (hle : n ≤ budget) :
    runFuel input D L budget s = (.done out, c) := by
  have hr := h.runFuel_done (budget - n)
  rwa [Nat.add_sub_of_le hle] at hr

/-- The same bounded run equals the whole lift/filter/translate specification, including none.
All intermediate degree bounds come from physical width; the residual test is executed. -/
theorem computation_runFuel_correct {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (jet : Fin (r + 1) → F) (initial : List F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hwidth : initial.length = D + 1)
    (hP : JetHornerMachine.coefficientPolynomial initial = (effectiveInitialPrefix jet).toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨initial, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done out, c) ∧ out.map JetHornerMachine.coefficientPolynomial =
        (directRegularSolution Q center jet D).map (unshift center) ∧
      (∀ xs, out = some xs → xs.length = D + 1) ∧
      totalCost c ≤ workBound input D L samples.length := by
  let input : Input F := ⟨initial, terms, center, r⟩
  obtain ⟨localOut, cl, hl, hspec, hlen, hcl⟩ := RegularLiftMachine.computation_runFuel_correct
    Q center initial (effectiveInitialPrefix jet) terms points samples hsamples hwidth hP hQ
    hr hlookup hweight
  obtain ⟨nl, hnl, htl⟩ := RegularLiftMachine.runFuel_refines input D L
    (RegularLiftMachine.fuel input D L samples.length) (.start samples)
  change RegularLiftMachine.runFuel input D L (RegularLiftMachine.fuel input D L samples.length)
    (.start samples) = (.done localOut, cl) at hl
  rw [hl] at htl
  change totalCost cl ≤ RegularLiftMachine.workBound input D L samples.length at hcl
  dsimp only [input] at hnl hcl
  cases hiter : directRegularIteration Q center (effectiveInitialPrefix jet) (D - r) with
  | none =>
      have ho : localOut = none := by simpa [hiter] using hspec
      rw [ho] at htl
      have ht := Trace.cons Step.start ((lift_lift input D L samples htl).trans
        (Trace.cons Step.liftReject (Trace.cons Step.emit (Trace.nil _))))
      have hrun := ht.runFuel_of_le (budget := fuel input D L samples.length) (by
        dsimp [fuel, suffixFuel, input]
        omega)
      refine ⟨none, _, hrun, by simp [directRegularSolution, hiter], by simp, ?_⟩
      simp only [total_add, total_wrapper]
      change 4 + (totalCost cl + 3 * nl + (3 + (4 + 0))) ≤ _
      dsimp [workBound, suffixWork, input]
      omega
  | some P =>
      rw [hiter, Option.map_some] at hspec
      obtain ⟨cs, hcs, hpoly⟩ := Option.map_eq_some_iff.mp hspec
      have hwidthcs := hlen cs hcs
      have hdegree := represented_degree cs P D hwidthcs hpoly
      rw [hcs] at htl
      obtain ⟨out, ns, c, hts, hs, hwidthout, hns, hc⟩ := suffix_trace Q center initial cs P
        terms points samples hsamples hwidth hwidthcs hpoly hQ hweight
      have ht := Trace.cons Step.start ((lift_lift input D L samples htl).trans
        (Trace.cons Step.liftReturn hts))
      have hrun := ht.runFuel_of_le (budget := fuel input D L samples.length) (by
        dsimp [fuel, input]
        omega)
      refine ⟨out, _, hrun, ?_, hwidthout, ?_⟩
      · rw [hs]
        by_cases hz : effectiveResidual Q center P = 0 <;>
          simp [directRegularSolution, hiter, hdegree, hz]
      · simp only [total_add, total_wrapper]
        change 4 + (totalCost cl + 3 * nl + (6 + totalCost c)) ≤ _
        dsimp [workBound, input]
        omega

private theorem solution_sound {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (jet : Fin (r + 1) → F) (D : ℕ) (P : CPolynomial F)
    (h : directRegularSolution Q center jet D = some P) :
    differentialSpecialization (semanticEquation Q) (unshift center P) = 0 := by
  obtain ⟨previous, _hprevious, hfilter⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at hfilter with hchecked
  · cases hfilter
    exact (effectiveResidual_eq_zero_iff Q center P).mp hchecked.2

/-- Every emitted global vector is an actual differential root, without a regularity assumption. -/
theorem computation_runFuel_sound {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (jet : Fin (r + 1) → F) (initial : List F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hwidth : initial.length = D + 1)
    (hP : JetHornerMachine.coefficientPolynomial initial = (effectiveInitialPrefix jet).toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨initial, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done out, c) ∧ totalCost c ≤ workBound input D L samples.length ∧
      (∀ xs, out = some xs → xs.length = D + 1 ∧
        differentialSpecialization (semanticEquation Q)
          (JetHornerMachine.coefficientPolynomial xs) = 0) := by
  obtain ⟨out, c, hrun, hspec, hlen, hcost⟩ := computation_runFuel_correct Q center jet initial
    terms points samples hsamples hwidth hP hQ hr hlookup hweight
  refine ⟨out, c, hrun, hcost, ?_⟩
  intro xs hxs
  refine ⟨hlen xs hxs, ?_⟩
  rw [hxs, Option.map_some] at hspec
  obtain ⟨P, hsol, hpoly⟩ := Option.map_eq_some_iff.mp hspec.symm
  rw [← hpoly]
  exact solution_sound Q center jet D P hsol

/-- A genuine bounded root with this regular compatible jet is emitted in the global coordinate.
Finite enumeration and initial vector construction are not part of this one-jet execution. -/
theorem computation_runFuel_complete [Finite F] {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (jet : Fin (r + 1) → F) (initial : List F)
    (terms : List (MvPolynomial.EvaluationMachine.Term F)) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hwidth : initial.length = D + 1)
    (hP : JetHornerMachine.coefficientPolynomial initial = (effectiveInitialPrefix jet).toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (f : F[X]) (hdegree : f.natDegree ≤ D)
    (hroot : differentialSpecialization (semanticEquation Q) f = 0)
    (hjet : polynomialJet center f = jet)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (hchar : D < ringChar F) :
    let input : Input F := ⟨initial, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ out.length = D + 1 ∧
      JetHornerMachine.coefficientPolynomial out = f ∧
      totalCost c ≤ workBound input D L samples.length := by
  let P : CPolynomial F := CPolynomial.ringEquiv.symm (taylor center f)
  have hp : P.toPoly = taylor center f := CPolynomial.ringEquiv.apply_symm_apply _
  have hunshift : unshift center P = f := by
    simp [unshift, hp, taylor_taylor]
  have hdegreeP : P.natDegree ≤ D := by
    simpa only [CPolynomial.natDegree_toPoly, hp, natDegree_taylor] using hdegree
  have hsolution : directRegularSolution Q center jet D = some P :=
    (directRegularSolution_eq_some_iff Q center jet hregular D hchar P).mpr
      ⟨hdegreeP, by simpa [hunshift] using hroot, by simpa [hunshift] using hjet⟩
  obtain ⟨out, c, hrun, hspec, hlen, hcost⟩ := computation_runFuel_correct Q center jet initial
    terms points samples hsamples hwidth hP hQ hr hlookup hweight
  rw [hsolution, Option.map_some, hunshift] at hspec
  obtain ⟨xs, hxs, hpoly⟩ := Option.map_eq_some_iff.mp hspec
  rw [hxs] at hrun
  exact ⟨xs, c, hrun, hlen xs hxs, hpoly, hcost⟩

end ReedSolomon.HiddenDerivative.RegularRootMachine
