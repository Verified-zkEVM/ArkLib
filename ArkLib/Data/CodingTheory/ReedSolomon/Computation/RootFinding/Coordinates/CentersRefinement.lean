/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.CentersMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootsRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterRootsBounds
/-!
# Same-execution coordinate center enumeration

Every center, candidate record, duplicate and failure tag is retained. The fixed factor applies
once to the source trace; it is independent of the number of centers and candidates.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticCenterRootsMachine

open Polynomial QuadraticAlgebra CompPoly PolynomialDifferential
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

/-- Represent one record while preserving its center and complete coefficient vector. -/
def mapRecord {K J : Type*} (f : K → J) (r : CenterRootsMachine.Record K) :
    CenterRootsMachine.Record J := (f r.1, r.2.map f)
/-- Preserve record order and multiplicity. -/
def mapRecords {K J : Type*} (f : K → J) (rs : List (CenterRootsMachine.Record K)) :
    List (CenterRootsMachine.Record J) := rs.map (mapRecord f)
/-- Represent the supplied alphabet, sparse terms and order. -/
def mapInput {K J : Type*} (f : K → J) (input : CenterRootsMachine.Input K) :
    CenterRootsMachine.Input J :=
  ⟨input.alphabet.map f, input.terms.map (fun t => (f t.1, t.2)), input.order⟩

/-- Preserve all cursors, pending records and the exact retained all-jet payload. -/
def represent {K F : Type*} [One K] (a : F) (f : K → Pair F)
    (input : CenterRootsMachine.Input K) (D : ℕ) :
    CenterRootsMachine.Configuration K → Configuration F
  | .start xs => .start (xs.map f)
  | .scan xs out samples => .scan (xs.map f) (mapRecords f out) (samples.map f)
  | .jets x xs out samples s => .jets (f x) (xs.map f) (mapRecords f out) (samples.map f)
      (QuadraticJetRootsMachine.mapInput f (CenterRootsMachine.centerInput input x))
      (QuadraticJetRootsMachine.represent a f (CenterRootsMachine.centerInput input x) D s)
  | .collect x cs xs out samples => .collect (f x) (cs.map (List.map f)) (xs.map f)
      (mapRecords f out) (samples.map f)
  | .save r x cs xs out samples => .save (mapRecord f r) (f x) (cs.map (List.map f))
      (xs.map f) (mapRecords f out) (samples.map f)
  | .reverse xs out => .reverse (mapRecords f xs) (mapRecords f out)
  | .emit out => .emit (out.map (mapRecords f))
  | .done out => .done (out.map (mapRecords f))

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Raw materialized inputs survive their coordinate round trip. -/
theorem encode_decode_input (a : F) (input : Input F) :
    mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input := by
  cases input
  simp [mapInput, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

/-- Each all-jet instruction preserves its complete ledger and pays the outer wrapper. -/
theorem jets_trace {a : F} {input : Input F} {payload : QuadraticJetRootsMachine.Input F}
    {D L n : ℕ} (x : Pair F) (xs : List (Pair F)) (out : List (Record F))
    (samples : List (Pair F)) {s t : QuadraticJetRootsMachine.Configuration F} {c : Cost}
    (h : QuadraticJetRootsMachine.Trace a payload D L n s c t) :
    ∃ d, Trace a input D L n (.jets x xs out samples payload s) d
      (.jets x xs out samples payload t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Every source edge lowers with a factor independent of both center and candidate counts. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : CenterRootsMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : CenterRootsMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : CenterRootsMachine.Cost}, CenterRootsMachine.Step input D L s c t →
      ∃ n d, Trace a (mapInput encode input) D L n (represent a encode input D s) d
        (represent a encode input D t) ∧ n + d.total ≤ 1073741824 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | start => exact ⟨1, charge 4 0 0, single rfl, by decide⟩
  | next => exact ⟨1, charge 6 0 0 + allocation 4, single rfl, by decide⟩
  | jets h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticJetRootsMachine.step_lowering a ha _ D L h
      obtain ⟨d, hd, he⟩ := jets_trace (input := mapInput encode input) _ _ _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | returned => exact ⟨1, charge 4 0 0, single rfl, by decide⟩
  | failed => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | pair => exact ⟨1, charge 6 0 0, single rfl, by decide⟩
  | save => exact ⟨1, charge 5 0 0, single rfl, by decide⟩
  | collected => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | scanned => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | reverse => exact ⟨1, charge 5 0 0, single rfl, by decide⟩
  | reversed => exact ⟨1, charge 2 0 0 + allocation 1, single rfl, by decide⟩
  | emit => exact ⟨1, charge 2 0 1, single rfl, by decide⟩

/-- Compose the fixed factor over total source steps, with no per-iteration exponentiation. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : CenterRootsMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : CenterRootsMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : CenterRootsMachine.Cost}, CenterRootsMachine.Trace input D L n s c t →
      ∃ steps d, Trace a (mapInput encode input) D L steps (represent a encode input D s) d
        (represent a encode input D t) ∧ steps + d.total ≤ 1073741824 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha input D L head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- A finite source run reaches the identical represented candidate or failure. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a)
    (input : CenterRootsMachine.Input (QuadraticAlgebra F a 0)) (D L fuel : ℕ)
    (s : CenterRootsMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ steps d, runFuel a (mapInput encode input) D L steps (represent a encode input D s) =
      (represent a encode input D (CenterRootsMachine.runFuel input D L fuel s).1, d) ∧
      steps + d.total ≤ 1073741824 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := CenterRootsMachine.runFuel_refines input D L fuel s
  obtain ⟨steps, d, hd, hb⟩ := trace_lowering a ha input D L ht
  exact ⟨steps, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Completed source execution transfers directly to already materialized coordinate inputs. -/
theorem start_run_lowering (a : F) (ha : ¬IsSquare a) (input : Input F) (D L fuel : ℕ)
    (samples : List (Pair F))
    (out : Option (List (CenterRootsMachine.Record (QuadraticAlgebra F a 0))))
    (sourceCost : CenterRootsMachine.Cost) :
    letI := fieldOfNonsquare a ha
    CenterRootsMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L fuel
      (.start (samples.map (ArithmeticMachine.decode a))) = (.done out, sourceCost) →
    ∃ steps c, runFuel a input D L steps (.start samples) =
      (.done (out.map (mapRecords encode)), c) ∧ steps + c.total ≤ 1073741824 * fuel := by
  let := fieldOfNonsquare a ha
  intro hs
  obtain ⟨steps, c, hr, hb⟩ := run_lowering a ha (mapInput (ArithmeticMachine.decode a) input)
    D L fuel (.start (samples.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hi := encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (samples.map (ArithmeticMachine.decode a)).map encode = samples := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨steps, c, ?_, hb⟩
  simpa only [represent, hp] using hr

/-- Actual center records equal the ordered source specification, retaining all duplicates. -/
theorem computation_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (D L : ℕ)
    (samples : List (Pair F))
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (points : Fin L ↪ QuadraticAlgebra F a 0)
    (hsamples : samples.map (ArithmeticMachine.decode a) = List.ofFn (fun i => points i))
    (hq : 0 < input.alphabet.length)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial
      (mapInput (ArithmeticMachine.decode a) input).terms =
        MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : input.order ≤ D) (hlookup : D - input.order < L) :
    letI := fieldOfNonsquare a ha
    differentialWeightedDegree D (semanticEquation Q) < L →
    ∃ steps c out, runFuel a input D L steps (.start samples) = (.done (some out), c) ∧
      (mapRecords (ArithmeticMachine.decode a) out).map CenterRootsMachine.recordPolynomial =
        (input.alphabet.map (ArithmeticMachine.decode a)).flatMap
          (CenterRootsMachine.centerSpec Q (input.alphabet.map (ArithmeticMachine.decode a)) D) ∧
      (∀ r ∈ out, r.2.length = D + 1) ∧ out.length ≤ input.alphabet.length ^ (input.order + 2) ∧
      steps + c.total ≤ 1073741824 * CenterRootsMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) D L samples.length := by
  let := fieldOfNonsquare a ha
  intro hweight
  obtain ⟨out, sourceCost, hs, hspec, hwidth, hcount, _⟩ :=
    CenterRootsMachine.computation_runFuel_correct Q
      (input.alphabet.map (ArithmeticMachine.decode a))
      (mapInput (ArithmeticMachine.decode a) input).terms points
      (samples.map (ArithmeticMachine.decode a)) hsamples (by simpa using hq) hQ hr hlookup hweight
  change CenterRootsMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L
    (CenterRootsMachine.fuel (mapInput (ArithmeticMachine.decode a) input) D L
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a))) = (.done (some out), sourceCost) at hs
  obtain ⟨steps, c, ht, hb⟩ := start_run_lowering a ha input D L _ samples (some out) sourceCost hs
  refine ⟨steps, c, mapRecords encode out, ht, ?_, ?_, ?_, ?_⟩
  · simpa [mapRecords, mapRecord, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
      using hspec
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    simpa [mapRecord] using hwidth s hs
  · simpa [mapRecords] using hcount
  · simpa only [List.length_map] using hb

end ReedSolomon.HiddenDerivative.QuadraticCenterRootsMachine
