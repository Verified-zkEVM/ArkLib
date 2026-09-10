/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsBounds
-- The completeness witness is constructed through `ringEquiv.symm`; expose the defining
-- implementation modules so its forward image reduces to `toPoly`.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv
/-!
# All-jet root collection semantics

The mathematical filter-map describes the ordered output of actual preparation and root calls.
Every tuple and padding cell is already materialized by the operational pipeline.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.JetRootsMachine

open Polynomial Matrix CompPoly List PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Proof-only view of the materialized ascending jet tuple. -/
def jetFunction (r : ℕ) (js : List F) : Fin (r + 1) → F := fun i ↦ js.getD i.val 0
/-- The finite-jet functional specification, returning a global polynomial or no root. -/
noncomputable def jetSolution {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (D : ℕ) (js : List F) : Option F[X] :=
  (directRegularSolution Q center (jetFunction r js) D).map (unshift center)

/-- The actual preparation specification represents exactly the initial jet polynomial. -/
theorem prepared_represents (r D : ℕ) (js : List F) (hlen : js.length = r + 1) :
    JetHornerMachine.coefficientPolynomial (JetPreparationMachine.prepared D js) =
      (effectiveInitialPrefix (jetFunction r js)).toPoly := by
  ext i
  rw [JetPreparationMachine.prepared_coeff, ← CPolynomial.coeff_toPoly]
  by_cases hi : i < r + 1
  · exact (coeff_effectiveInitialPrefix (jetFunction r js) ⟨i, hi⟩).symm
  · rw [coeff_effectiveInitialPrefix_of_lt _ i (by omega)]
    simp [List.getD, List.getElem?_eq_none (show js.length ≤ i by omega)]

omit [DecidableEq F] in
/-- Reversal allocates each retained output cell and charges its final emission. -/
theorem reverse_trace (input : Input F) (D L : ℕ) (as out : List (List F)) :
    ∃ c, Trace input D L (as.length + 2) (.reverse as out) c
      (.done (some (as.reverse ++ out))) ∧ totalCost c ≤ 6 * as.length + 7 := by
  induction as generalizing out with
  | nil =>
      refine ⟨charge 2 0 0 + (charge 2 0 1 + 0), ?_, ?_⟩
      · simpa using Trace.cons (Step.reversed (input := input) (D := D) (L := L))
          (Trace.cons Step.emit (Trace.nil _))
      · change totalCost (charge 2 0 0 + (charge 2 0 1 + 0)) ≤ 7
        decide
  | cons a as ih =>
      obtain ⟨c, ht, hc⟩ := ih (a :: out)
      refine ⟨charge 5 0 0 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverse ht
      · rw [total_add, total_charge]
        simp only [List.length_cons]
        omega

/-- The complete consumer performs actual preparation/root calls and collects only successes. -/
theorem scan_trace {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (jets acc : List (List F)) (hjets : ∀ js ∈ jets, js.length = r + 1)
    (hacc : ∀ xs ∈ acc, xs.length = D + 1) :
    let input : Input F := ⟨alphabet, terms, center, r⟩
    ∃ out steps c, Trace input D L steps (.scan jets acc samples) c (.done (some out)) ∧
      out.map JetHornerMachine.coefficientPolynomial =
        acc.reverse.map JetHornerMachine.coefficientPolynomial ++
          jets.filterMap (jetSolution Q center D) ∧
      (∀ xs ∈ out, xs.length = D + 1) ∧ out.length ≤ acc.length + jets.length ∧
      steps ≤ jets.length * itemFuel input D L samples.length + acc.length + 3 ∧
      totalCost c ≤ jets.length * itemWork input D L samples.length + 6 * acc.length + 10 := by
  let input : Input F := ⟨alphabet, terms, center, r⟩
  induction jets generalizing acc with
  | nil =>
      obtain ⟨c, ht, hc⟩ := reverse_trace input D L acc []
      simp only [List.append_nil] at ht
      refine ⟨acc.reverse, _, charge 2 0 0 + c, Trace.cons Step.scanned ht, by simp, ?_,
        by simp, by simp, ?_⟩
      · simpa using hacc
      · rw [total_add, total_charge]
        simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
        omega
  | cons js jets ih =>
      have hjs := hjets js (by simp)
      have htail : ∀ j ∈ jets, j.length = r + 1 := fun j hj ↦ hjets j (by simp [hj])
      let prepared := JetPreparationMachine.prepared D js
      have hwidth : prepared.length = D + 1 :=
        JetPreparationMachine.prepared_length D js (by omega)
      have hrep := prepared_represents r D js hjs
      obtain ⟨rootOut, cr, hroot, hspec, hrootlen, hcr⟩ :=
        RegularRootMachine.computation_runFuel_correct Q center (jetFunction r js) prepared
          terms points samples hsamples hwidth hrep hQ hr hlookup hweight
      obtain ⟨nr, hnr, htr⟩ := RegularRootMachine.runFuel_refines (rootInput input prepared) D L
        (RegularRootMachine.fuel (rootInput input prepared) D L samples.length) (.start samples)
      change RegularRootMachine.runFuel (rootInput input prepared) D L
        (RegularRootMachine.fuel (rootInput input prepared) D L samples.length) (.start samples) =
          (.done rootOut, cr) at hroot
      rw [hroot] at htr
      obtain ⟨hfeq, hweq⟩ := root_budgets input D L samples.length prepared hwidth
      rw [hfeq] at hnr
      change totalCost cr ≤ RegularRootMachine.workBound (rootInput input prepared) D L
        samples.length at hcr
      rw [hweq] at hcr
      dsimp only [input] at hnr hcr
      have htp := JetPreparationMachine.preparation_trace D js (by omega)
      have hcp := JetPreparationMachine.successCost_total_le D js.length (by omega)
      rw [hjs] at hcp
      cases rootOut with
      | none =>
          have hjnone : jetSolution Q center D js = none := hspec.symm
          obtain ⟨out, nt, ct, htt, hsem, hwidthout, hcount, hnt, hct⟩ := ih acc htail hacc
          have ht := Trace.cons Step.next ((lift_prepare input D L jets acc samples htp).trans
            (Trace.cons Step.prepared ((lift_root input D L jets acc samples prepared htr).trans
              (Trace.cons Step.skipped htt))))
          refine ⟨out, _, _, ht, ?_, hwidthout, ?_, ?_, ?_⟩
          · simpa [List.filterMap_cons, hjnone] using hsem
          · simp only [List.length_cons]
            omega
          · dsimp [itemFuel, input] at hnt ⊢
            nlinarith
          · simp only [total_add, total_charge, total_preparation, total_wrapper]
            change 7 + ((JetPreparationMachine.successCost D js.length).total + 3 * (D + 5) +
              (6 + (totalCost cr + 3 * nr + (3 + totalCost ct)))) ≤ _
            rw [hjs]
            dsimp [itemWork, input] at hct ⊢
            nlinarith
      | some candidate =>
          have hjsome : jetSolution Q center D js =
              some (JetHornerMachine.coefficientPolynomial candidate) := hspec.symm
          have hcandidate := hrootlen candidate rfl
          obtain ⟨out, nt, ct, htt, hsem, hwidthout, hcount, hnt, hct⟩ :=
            ih (candidate :: acc) htail (by
              intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact hcandidate
              · exact hacc a ha)
          have ht := Trace.cons Step.next ((lift_prepare input D L jets acc samples htp).trans
            (Trace.cons Step.prepared ((lift_root input D L jets acc samples prepared htr).trans
              (Trace.cons Step.success (Trace.cons Step.save htt)))))
          refine ⟨out, _, _, ht, ?_, hwidthout, ?_, ?_, ?_⟩
          · simpa [List.filterMap_cons, hjsome, List.reverse_cons, List.map_append,
              List.append_assoc] using hsem
          · simp only [List.length_cons] at hcount ⊢
            omega
          · dsimp [itemFuel, input] at hnt ⊢
            nlinarith
          · simp only [total_add, total_charge, total_preparation, total_wrapper]
            change 7 + ((JetPreparationMachine.successCost D js.length).total + 3 * (D + 5) +
              (6 + (totalCost cr + 3 * nr + (3 + (6 + totalCost ct))))) ≤ _
            rw [hjs]
            dsimp [itemWork, input] at hct ⊢
            nlinarith

private theorem Trace.runFuel_of_le {input : Input F} {D L n budget : ℕ}
    {s : Configuration F} {c : Cost} {out : Option (List (List F))}
    (h : Trace input D L n s c (.done out)) (hle : n ≤ budget) :
    runFuel input D L budget s = (.done out, c) := by
  have hr := h.runFuel_done (budget - n)
  rwa [Nat.add_sub_of_le hle] at hr

/-- Actual all-jet enumeration/preparation/root execution equals the ordered finite specification.
Its sole exponential factor is the number of initial jets, including all materialization costs. -/
theorem computation_runFuel_correct {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < alphabet.length)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨alphabet, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ out.map JetHornerMachine.coefficientPolynomial =
        (tuples alphabet (r + 1)).filterMap (jetSolution Q center D) ∧
      (∀ xs ∈ out, xs.length = D + 1) ∧ out.length ≤ alphabet.length ^ (r + 1) ∧
      totalCost c ≤ workBound input D L samples.length := by
  let input : Input F := ⟨alphabet, terms, center, r⟩
  obtain ⟨ne, ce, he, hne, hce⟩ := enumeration_trace input D L samples hq
  obtain ⟨out, ns, cs, hs, hspec, hwidth, hcount, hns, hcs⟩ := scan_trace Q center alphabet terms
    points samples hsamples hQ hr hlookup hweight (tuples alphabet (r + 1)) []
    (tuples_width alphabet (r + 1)) (by simp)
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at hspec
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero, Nat.mul_zero, tuples_length]
    at hcount hns hcs
  dsimp only [input] at hne hce
  have ht := he.trans hs
  have hrun := ht.runFuel_of_le (budget := fuel input D L samples.length) (by
    dsimp [fuel, input]
    nlinarith)
  refine ⟨out, _, hrun, hspec, hwidth, hcount, ?_⟩
  rw [total_add]
  dsimp [workBound, input]
  nlinarith

private theorem iteration_jet {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (jet : Fin (r + 1) → F) (n : ℕ) (P : CPolynomial F)
    (h : directRegularIteration Q center (effectiveInitialPrefix jet) n = some P) :
    polynomialJet center (unshift center P) = jet := by
  induction n generalizing P with
  | zero =>
      cases h
      exact polynomialJet_taylor_effectiveInitialPrefix center jet
  | succ n ih =>
      obtain ⟨previous, hprevious, hstep⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨gamma, _hgamma, hP⟩ := Option.map_eq_some_iff.mp hstep
      rw [← hP, polynomialJet_unshift_effectiveRegularCandidate center previous gamma _ (by omega)]
      exact ih previous hprevious

/-- Each successful finite-jet specification is a root and retains the exact initial jet. -/
theorem jetSolution_sound {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (D : ℕ) (js : List F) (f : F[X]) (h : jetSolution Q center D js = some f) :
    differentialSpecialization (semanticEquation Q) f = 0 ∧
      polynomialJet center f = jetFunction r js := by
  obtain ⟨P, hsol, hf⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨previous, hprevious, hfilter⟩ := Option.bind_eq_some_iff.mp hsol
  split_ifs at hfilter with hchecked
  cases hfilter
  rw [← hf]
  exact ⟨(effectiveResidual_eq_zero_iff Q center P).mp hchecked.2,
    iteration_jet Q center (jetFunction r js) _ P hprevious⟩

omit [Field F] [DecidableEq F] in
/-- Every materialized tuple whose coordinates occur in the alphabet is enumerated. -/
theorem mem_tuples_of_entries (alphabet js : List F) (m : ℕ) (hlen : js.length = m)
    (h : ∀ x ∈ js, x ∈ alphabet) : js ∈ tuples alphabet m := by
  rw [tuples, CartesianProductMachine.mem_productSpec]
  apply List.forall₂_of_length_eq_of_get (by simpa using hlen)
  intro i hi hj
  simpa using h (js.get ⟨i, hi⟩) (List.get_mem js ⟨i, hi⟩)

omit [DecidableEq F] in
/-- The functional view of a proof-only finite tuple is its original jet. -/
theorem jetFunction_ofFn (r : ℕ) (jet : Fin (r + 1) → F) :
    jetFunction r (List.ofFn jet) = jet := by
  funext i
  simp only [jetFunction, List.getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

/-- Membership in the exact output specification certifies both a root and its enumerated jet. -/
theorem output_sound {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (D : ℕ)
    (alphabet : List F) (out : List (List F))
    (hspec : out.map JetHornerMachine.coefficientPolynomial =
      (tuples alphabet (r + 1)).filterMap (jetSolution Q center D))
    (xs : List F) (hxs : xs ∈ out) :
    differentialSpecialization (semanticEquation Q)
      (JetHornerMachine.coefficientPolynomial xs) = 0 ∧
      ∃ js ∈ tuples alphabet (r + 1), polynomialJet center
        (JetHornerMachine.coefficientPolynomial xs) = jetFunction r js := by
  have hm : JetHornerMachine.coefficientPolynomial xs ∈
      out.map JetHornerMachine.coefficientPolynomial := List.mem_map.mpr ⟨xs, hxs, rfl⟩
  rw [hspec] at hm
  obtain ⟨js, hjs, hsolution⟩ := List.mem_filterMap.mp hm
  obtain ⟨hroot, hjet⟩ := jetSolution_sound Q center D js _ hsolution
  exact ⟨hroot, js, hjs, hjet⟩

/-- Every actual bounded root with a regular jet at this center occurs in the collected output.
The complete supplied alphabet supplies finiteness; no field-enumeration instruction is used. -/
theorem computation_runFuel_complete {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hall : ∀ a : F, a ∈ alphabet)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (f : F[X]) (hdegree : f.natDegree ≤ D)
    (hroot : differentialSpecialization (semanticEquation Q) f = 0)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center (polynomialJet center f))
    (hchar : D < ringChar F) :
    let input : Input F := ⟨alphabet, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ (∀ xs ∈ out, xs.length = D + 1) ∧
      (∃ xs ∈ out, JetHornerMachine.coefficientPolynomial xs = f) ∧
      totalCost c ≤ workBound input D L samples.length := by
  let : Fintype F := Fintype.ofList alphabet hall
  have hq : 0 < alphabet.length := List.length_pos_of_mem (hall 0)
  obtain ⟨out, c, hrun, hspec, hwidth, _hcount, hcost⟩ := computation_runFuel_correct Q center
    alphabet terms points samples hsamples hq hQ hr hlookup hweight
  let jet : Fin (r + 1) → F := polynomialJet center f
  let js := List.ofFn jet
  have hmem : js ∈ tuples alphabet (r + 1) :=
    mem_tuples_of_entries alphabet js (r + 1) (by simp [js]) (fun a _ ↦ hall a)
  let P : CPolynomial F := CPolynomial.ringEquiv.symm (taylor center f)
  have hp : P.toPoly = taylor center f := CPolynomial.ringEquiv.apply_symm_apply _
  have hunshift : unshift center P = f := by simp [unshift, hp, taylor_taylor]
  have hdegreeP : P.natDegree ≤ D := by
    simpa only [CPolynomial.natDegree_toPoly, hp, natDegree_taylor] using hdegree
  have hsolution : directRegularSolution Q center jet D = some P :=
    (directRegularSolution_eq_some_iff Q center jet hregular D hchar P).mpr
      ⟨hdegreeP, by simpa [hunshift] using hroot, by simp [hunshift, jet]⟩
  have hjs : jetSolution Q center D js = some f := by
    rw [jetSolution, show jetFunction r js = jet from jetFunction_ofFn r jet, hsolution]
    simp [hunshift]
  have hfmem : f ∈ out.map JetHornerMachine.coefficientPolynomial := by
    rw [hspec]
    exact List.mem_filterMap.mpr ⟨js, hmem, hjs⟩
  obtain ⟨xs, hxs, hpoly⟩ := List.mem_map.mp hfmem
  exact ⟨out, c, hrun, hwidth, ⟨xs, hxs, hpoly⟩, hcost⟩

/-- Soundness and initial-jet preservation are attached to the same bounded all-jet execution. -/
theorem computation_runFuel_sound {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < alphabet.length)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨alphabet, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ totalCost c ≤ workBound input D L samples.length ∧
      (∀ xs ∈ out, xs.length = D + 1 ∧
        differentialSpecialization (semanticEquation Q)
          (JetHornerMachine.coefficientPolynomial xs) = 0 ∧
        ∃ js ∈ tuples alphabet (r + 1), polynomialJet center
          (JetHornerMachine.coefficientPolynomial xs) = jetFunction r js) := by
  obtain ⟨out, c, hrun, hspec, hwidth, _hcount, hcost⟩ := computation_runFuel_correct Q center
    alphabet terms points samples hsamples hq hQ hr hlookup hweight
  exact ⟨out, c, hrun, hcost, fun xs hxs ↦
    ⟨hwidth xs hxs, output_sound Q center D alphabet out hspec xs hxs⟩⟩

end ReedSolomon.HiddenDerivative.JetRootsMachine
