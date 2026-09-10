/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterRootsMachine

-- The completeness witness reduces `ringEquiv.symm` back to its polynomial semantics.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv
/-!
# Ordered center collection and its charged bounds

The specification projects explicit records to global polynomials. Pair and list allocation,
callee dispatch, and final reversal are included in the same execution bound.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CenterRootsMachine

open Polynomial Matrix CompPoly List PolynomialDifferential

/-- Total work is additive across composed transitions. -/
theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b :=
  JetRootsMachine.total_add a b

/-- A caller dispatch preserves its fixed register charge. -/
theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n :=
  JetRootsMachine.total_wrapper n

/-- Local operations retain control, allocation, arithmetic, and output charges. -/
theorem total_charge (d n o : ℕ) : totalCost (charge d n o) = 1 + d + n + o :=
  JetRootsMachine.total_charge d n o

variable {F : Type*} [Field F] [DecidableEq F]

/-- Mathematical projection of an allocated center/vector record. -/
noncomputable def recordPolynomial (record : Record F) : F × F[X] :=
  (record.1, JetHornerMachine.coefficientPolynomial record.2)

/-- Ordered mathematical specification for one center. -/
noncomputable def centerSpec {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (D : ℕ) (a : F) : List (F × F[X]) :=
  ((JetRootsMachine.tuples alphabet (r + 1)).filterMap
    (JetRootsMachine.jetSolution Q a D)).map (a, ·)

/-- Uniform per-center step budget; zero is used only to state a scalar-independent bound. -/
def centerFuel (input : Input F) (D L n : ℕ) : ℕ :=
  JetRootsMachine.fuel (centerInput input 0) D L n +
    3 * input.alphabet.length ^ (input.order + 1) + 3

/-- Uniform per-center work, including record allocations and their eventual reversal. -/
def centerWork (input : Input F) (D L n : ℕ) : ℕ :=
  JetRootsMachine.workBound (centerInput input 0) D L n +
    3 * JetRootsMachine.fuel (centerInput input 0) D L n +
    20 * input.alphabet.length ^ (input.order + 1) + 20

/-- Complete center-loop fuel. -/
def fuel (input : Input F) (D L n : ℕ) : ℕ :=
  input.alphabet.length * centerFuel input D L n + 4

/-- Complete center-loop work. -/
def workBound (input : Input F) (D L n : ℕ) : ℕ :=
  input.alphabet.length * centerWork input D L n + 16

omit [DecidableEq F] in
/-- Actual scalar centers have identical callee budgets. -/
theorem center_budgets (input : Input F) (D L n : ℕ) (a : F) :
    JetRootsMachine.fuel (centerInput input a) D L n =
      JetRootsMachine.fuel (centerInput input 0) D L n ∧
    JetRootsMachine.workBound (centerInput input a) D L n =
      JetRootsMachine.workBound (centerInput input 0) D L n := by
  constructor <;> rfl

omit [DecidableEq F] in
/-- Materialize each pair, then its outer-list cell, without a collection primitive. -/
theorem collect_trace (input : Input F) (D L : ℕ) (a : F)
    (candidates : List (List F)) (centers : List F) (acc : List (Record F)) (samples : List F) :
    ∃ c, Trace input D L (2 * candidates.length + 1)
      (.collect a candidates centers acc samples) c
      (.scan centers ((candidates.map (a, ·)).reverse ++ acc) samples) ∧
      totalCost c ≤ 13 * candidates.length + 3 := by
  induction candidates generalizing acc with
  | nil =>
      refine ⟨charge 2 0 0 + 0, ?_, ?_⟩
      · simpa using Trace.cons (Step.collected (input := input) (D := D) (L := L))
          (Trace.nil _)
      · change totalCost (charge 2 0 0 + 0) ≤ 3
        decide
  | cons candidate candidates ih =>
      obtain ⟨c, ht, hc⟩ := ih ((a, candidate) :: acc)
      refine ⟨charge 6 0 0 + (charge 5 0 0 + c), ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc] using
          Trace.cons Step.pair (Trace.cons Step.save ht)
      · simp only [total_add, total_charge,
          List.length_cons]
        omega

omit [DecidableEq F] in
/-- Reversal charges every outer record cell and final emission. -/
theorem reverse_trace (input : Input F) (D L : ℕ) (as out : List (Record F)) :
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

/-- The outer consumer executes every center and preserves the exact per-center output order. -/
theorem scan_trace {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < alphabet.length)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (centers : List F) (acc : List (Record F))
    (hacc : ∀ record ∈ acc, record.2.length = D + 1) :
    let input : Input F := ⟨alphabet, terms, r⟩
    ∃ out steps c, Trace input D L steps (.scan centers acc samples) c (.done (some out)) ∧
      out.map recordPolynomial =
        acc.reverse.map recordPolynomial ++ centers.flatMap (centerSpec Q alphabet D) ∧
      (∀ record ∈ out, record.2.length = D + 1) ∧
      out.length ≤ acc.length + centers.length * alphabet.length ^ (r + 1) ∧
      steps ≤ centers.length * centerFuel input D L samples.length + acc.length + 3 ∧
      totalCost c ≤ centers.length * centerWork input D L samples.length +
        6 * acc.length + 10 := by
  let input : Input F := ⟨alphabet, terms, r⟩
  induction centers generalizing acc with
  | nil =>
      obtain ⟨c, ht, hc⟩ := reverse_trace input D L acc []
      simp only [List.append_nil] at ht
      refine ⟨acc.reverse, _, charge 2 0 0 + c, Trace.cons Step.scanned ht, by simp, ?_,
        by simp, by simp, ?_⟩
      · simpa using hacc
      · rw [total_add, total_charge]
        simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
        omega
  | cons a centers ih =>
      obtain ⟨candidates, cj, hj, hspec, hwidth, hcount, hcj⟩ :=
        JetRootsMachine.computation_runFuel_correct Q a alphabet terms points samples
          hsamples hq hQ hr hlookup hweight
      obtain ⟨nj, hnj, htj⟩ := JetRootsMachine.runFuel_refines (centerInput input a) D L
        (JetRootsMachine.fuel (centerInput input a) D L samples.length) (.start samples)
      change JetRootsMachine.runFuel (centerInput input a) D L
        (JetRootsMachine.fuel (centerInput input a) D L samples.length) (.start samples) =
          (.done (some candidates), cj) at hj
      rw [hj] at htj
      obtain ⟨hfeq, hweq⟩ := center_budgets input D L samples.length a
      rw [hfeq] at hnj
      change totalCost cj ≤ JetRootsMachine.workBound (centerInput input a) D L
        samples.length at hcj
      rw [hweq] at hcj
      dsimp only [input] at hnj hcj
      obtain ⟨cc, htc, hcc⟩ := collect_trace input D L a candidates centers acc samples
      obtain ⟨out, nt, ct, htt, hsem, houtwidth, houtcount, hnt, hct⟩ :=
        ih ((candidates.map (a, ·)).reverse ++ acc) (by
          intro record hm
          rcases List.mem_append.mp hm with hm | hm
          · obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hm)
            exact hwidth xs hxs
          · exact hacc record hm)
      have ht := Trace.cons Step.next ((lift_jets input D L a centers acc samples htj).trans
        (Trace.cons Step.returned (htc.trans htt)))
      refine ⟨out, _, _, ht, ?_, houtwidth, ?_, ?_, ?_⟩
      · have hp : (candidates.map (a, ·)).map recordPolynomial = centerSpec Q alphabet D a := by
          simp only [List.map_map, recordPolynomial, Function.comp_def, centerSpec]
          rw [← hspec, List.map_map]
          rfl
        simpa only [List.reverse_append, List.reverse_reverse, List.map_append, hp,
          List.flatMap_cons, List.append_assoc] using hsem
      · simp only [List.length_append, List.length_reverse, List.length_map,
          List.length_cons] at houtcount ⊢
        nlinarith
      · simp only [List.length_append, List.length_reverse, List.length_map] at hnt
        dsimp [centerFuel, input] at hnt ⊢
        nlinarith
      · simp only [total_add, total_charge,
          total_wrapper]
        simp only [List.length_append, List.length_reverse, List.length_map] at hct
        dsimp [centerWork, input] at hct ⊢
        nlinarith

private theorem Trace.runFuel_of_le {input : Input F} {D L n budget : ℕ}
    {s : Configuration F} {c : Cost} {out : Option (List (Record F))}
    (h : Trace input D L n s c (.done out)) (hle : n ≤ budget) :
    runFuel input D L budget s = (.done out, c) := by
  have hr := h.runFuel_done (budget - n)
  rwa [Nat.add_sub_of_le hle] at hr

/-- The actual center/jet loop returns its exact ordered specification, retaining duplicates. -/
theorem computation_runFuel_correct {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < alphabet.length)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨alphabet, terms, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧
      out.map recordPolynomial = alphabet.flatMap (centerSpec Q alphabet D) ∧
      (∀ record ∈ out, record.2.length = D + 1) ∧
      out.length ≤ alphabet.length ^ (r + 2) ∧
      totalCost c ≤ workBound input D L samples.length := by
  let input : Input F := ⟨alphabet, terms, r⟩
  obtain ⟨out, n, c, ht, hspec, hwidth, hcount, hn, hc⟩ := scan_trace Q alphabet terms
    points samples hsamples hq hQ hr hlookup hweight alphabet [] (by simp)
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at hspec
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero, Nat.mul_zero] at hcount hn hc
  have ht' := Trace.cons Step.start ht
  have hrun := ht'.runFuel_of_le (budget := fuel input D L samples.length) (by
    dsimp [fuel, input]
    omega)
  refine ⟨out, _, hrun, hspec, hwidth, ?_, ?_⟩
  · simpa only [show r + 2 = (r + 1) + 1 from rfl, pow_succ, Nat.mul_comm] using hcount
  · rw [total_add, total_charge]
    dsimp [workBound, input]
    omega

/-- Exact ordered output membership certifies a root and its preserved enumerated jet. -/
theorem output_sound {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (D : ℕ)
    (alphabet : List F) (out : List (Record F))
    (hspec : out.map recordPolynomial = alphabet.flatMap (centerSpec Q alphabet D))
    (record : Record F) (hrecord : record ∈ out) :
    record.1 ∈ alphabet ∧ differentialSpecialization (semanticEquation Q)
      (JetHornerMachine.coefficientPolynomial record.2) = 0 ∧
      ∃ js ∈ JetRootsMachine.tuples alphabet (r + 1), polynomialJet record.1
        (JetHornerMachine.coefficientPolynomial record.2) = JetRootsMachine.jetFunction r js := by
  have hm : recordPolynomial record ∈ out.map recordPolynomial :=
    List.mem_map.mpr ⟨record, hrecord, rfl⟩
  rw [hspec] at hm
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨f, hf, heq⟩ := List.mem_map.mp hm
  obtain ⟨haeq, hfeq⟩ := Prod.mk.inj heq
  obtain ⟨js, hjs, hsol⟩ := List.mem_filterMap.mp hf
  obtain ⟨hroot, hjet⟩ := JetRootsMachine.jetSolution_sound Q a D js f hsol
  change a = record.1 at haeq
  change f = JetHornerMachine.coefficientPolynomial record.2 at hfeq
  subst a f
  exact ⟨ha, hroot, js, hjs, hjet⟩

/-- Soundness, global-vector width, and jet preservation belong to the same bounded execution. -/
theorem computation_runFuel_sound {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < alphabet.length)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨alphabet, terms, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ totalCost c ≤ workBound input D L samples.length ∧
      (∀ record ∈ out, record.2.length = D + 1 ∧ record.1 ∈ alphabet ∧
        differentialSpecialization (semanticEquation Q)
          (JetHornerMachine.coefficientPolynomial record.2) = 0 ∧
        ∃ js ∈ JetRootsMachine.tuples alphabet (r + 1), polynomialJet record.1
          (JetHornerMachine.coefficientPolynomial record.2) =
            JetRootsMachine.jetFunction r js) := by
  obtain ⟨out, c, hrun, hspec, hwidth, _hcount, hcost⟩ := computation_runFuel_correct Q
    alphabet terms points samples hsamples hq hQ hr hlookup hweight
  exact ⟨out, c, hrun, hcost, fun record hm ↦
    ⟨hwidth record hm, output_sound Q D alphabet out hspec record hm⟩⟩

/-- Any bounded root having a regular center is retained by the actual execution.
Completeness of the supplied alphabet constructs its center and jet memberships algebraically. -/
theorem computation_runFuel_complete {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hall : ∀ a : F, a ∈ alphabet)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L)
    (f : F[X]) (hdegree : f.natDegree ≤ D)
    (hroot : differentialSpecialization (semanticEquation Q) f = 0)
    (hregular : ∃ a, IsRegularJet (semanticEquation Q) (Fin.last r) a (polynomialJet a f))
    (hchar : D < ringChar F) :
    let input : Input F := ⟨alphabet, terms, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ (∀ record ∈ out, record.2.length = D + 1) ∧
      (∃ record ∈ out, JetHornerMachine.coefficientPolynomial record.2 = f ∧
        IsRegularJet (semanticEquation Q) (Fin.last r) record.1 (polynomialJet record.1 f)) ∧
      totalCost c ≤ workBound input D L samples.length := by
  let : Fintype F := Fintype.ofList alphabet hall
  have hq : 0 < alphabet.length := List.length_pos_of_mem (hall 0)
  obtain ⟨out, c, hrun, hspec, hwidth, _hcount, hcost⟩ := computation_runFuel_correct Q
    alphabet terms points samples hsamples hq hQ hr hlookup hweight
  obtain ⟨a, ha⟩ := hregular
  let jet : Fin (r + 1) → F := polynomialJet a f
  let js := List.ofFn jet
  have hmem : js ∈ JetRootsMachine.tuples alphabet (r + 1) :=
    JetRootsMachine.mem_tuples_of_entries alphabet js (r + 1) (by simp [js])
      (fun x _ ↦ hall x)
  let P : CPolynomial F := CPolynomial.ringEquiv.symm (taylor a f)
  have hp : P.toPoly = taylor a f := CPolynomial.ringEquiv.apply_symm_apply _
  have hunshift : unshift a P = f := by simp [unshift, hp, taylor_taylor]
  have hdegreeP : P.natDegree ≤ D := by
    simpa only [CPolynomial.natDegree_toPoly, hp, natDegree_taylor] using hdegree
  have hsolution : directRegularSolution Q a jet D = some P :=
    (directRegularSolution_eq_some_iff Q a jet ha D hchar P).mpr
      ⟨hdegreeP, by simpa [hunshift] using hroot, by simp [hunshift, jet]⟩
  have hjs : JetRootsMachine.jetSolution Q a D js = some f := by
    rw [JetRootsMachine.jetSolution,
      show JetRootsMachine.jetFunction r js = jet from JetRootsMachine.jetFunction_ofFn r jet,
      hsolution]
    simp [hunshift]
  have hfmem : (a, f) ∈ out.map recordPolynomial := by
    rw [hspec]
    apply List.mem_flatMap.mpr
    refine ⟨a, hall a, List.mem_map.mpr ⟨f, ?_, rfl⟩⟩
    exact List.mem_filterMap.mpr ⟨js, hmem, hjs⟩
  obtain ⟨record, hrecord, heq⟩ := List.mem_map.mp hfmem
  obtain ⟨hcenter, hpoly⟩ := Prod.mk.inj heq
  exact ⟨out, c, hrun, hwidth, ⟨record, hrecord, hpoly, by simpa [hcenter] using ha⟩, hcost⟩

end ReedSolomon.HiddenDerivative.CenterRootsMachine
