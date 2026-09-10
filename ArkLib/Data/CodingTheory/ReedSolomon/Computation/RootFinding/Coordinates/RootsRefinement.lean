/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootsMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootRefinement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.PreparationRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsSemantics
/-!
# Same-execution coordinate candidate enumeration

Pointwise representation preserves the entire ordered enumeration and output, including repeated
jets, skipped roots and preparation failures. Actual child instructions compose with one constant
factor over total source steps, never a factor compounded by the number of candidates.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticJetRootsMachine

open Polynomial QuadraticAlgebra CompPoly PolynomialDifferential
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

/-- Pointwise map of nested lists, used only to state representation. -/
def mapLists {K J : Type*} (f : K → J) (xs : List (List K)) : List (List J) :=
  xs.map (List.map f)

/-- Preserve every prefix-axis cursor and capacity, without executing conversion. -/
def mapAxes {K J : Type*} (f : K → J) :
    List.PrefixAxesMachine.Configuration K → List.PrefixAxesMachine.Configuration J
  | .start bs => .start bs
  | .scan bs axes => .scan bs (mapLists f axes)
  | .copy bs axes n xs rev => .copy bs (mapLists f axes) n (xs.map f) (rev.map f)
  | .reversePrefix bs axes xs out =>
      .reversePrefix bs (mapLists f axes) (xs.map f) (out.map f)
  | .save bs axes xs => .save bs (mapLists f axes) (xs.map f)
  | .reverseAxes xs out => .reverseAxes (mapLists f xs) (mapLists f out)
  | .emit out => .emit (out.map (mapLists f))
  | .done out => .done (out.map (mapLists f))

/-- Preserve all product cursors and the separately allocated pending tuple. -/
def mapProduct {K J : Type*} (f : K → J) :
    List.CartesianProductMachine.Configuration K → List.CartesianProductMachine.Configuration J
  | .start xs => .start (mapLists f xs)
  | .reverseAxes xs out => .reverseAxes (mapLists f xs) (mapLists f out)
  | .axes xs ps => .axes (mapLists f xs) (mapLists f ps)
  | .elements xs es ps out => .elements (mapLists f xs) (es.map f) (mapLists f ps) (mapLists f out)
  | .tuples xs x es ps ts out =>
      .tuples (mapLists f xs) (f x) (es.map f) (mapLists f ps) (mapLists f ts) (mapLists f out)
  | .save xs x es ps ts out t =>
      .save (mapLists f xs) (f x) (es.map f) (mapLists f ps) (mapLists f ts)
        (mapLists f out) (t.map f)
  | .reverseProduct xs ts out => .reverseProduct (mapLists f xs) (mapLists f ts) (mapLists f out)
  | .emit ps => .emit (mapLists f ps)
  | .done ps => .done (mapLists f ps)

/-- All scalar-free prefix rules commute with pointwise representation at identical cost. -/
theorem axes_step_map {K J : Type*} (f : K → J) {u : List K}
    {s t : List.PrefixAxesMachine.Configuration K} {c : List.PrefixAxesMachine.Cost}
    (h : List.PrefixAxesMachine.Step u s c t) :
    List.PrefixAxesMachine.Step (u.map f) (mapAxes f s) c (mapAxes f t) := by
  cases h <;> constructor

/-- All scalar-free product rules preserve order and duplicates at identical cost. -/
theorem product_step_map {K J : Type*} (f : K → J)
    {s t : List.CartesianProductMachine.Configuration K} {c : List.CartesianProductMachine.Cost}
    (h : List.CartesianProductMachine.Step s c t) :
    List.CartesianProductMachine.Step (mapProduct f s) c (mapProduct f t) := by
  cases h <;> constructor

/-- Represent alphabet, sparse terms, center and order registers. -/
def mapInput {K J : Type*} (f : K → J) (input : JetRootsMachine.Input K) :
    JetRootsMachine.Input J :=
  ⟨input.alphabet.map f, input.terms.map (fun t => (f t.1, t.2)), f input.center, input.order⟩

/-- Every candidate, reversed output and retained root input has an exact representation. -/
def represent {K F : Type*} [One K] (a : F) (f : K → Pair F)
    (input : JetRootsMachine.Input K) (D : ℕ) : JetRootsMachine.Configuration K → Configuration F
  | .start xs => .start (xs.map f)
  | .count xs q samples => .count (xs.map f) q (samples.map f)
  | .bounds n q bs xs => .bounds n q bs (xs.map f)
  | .axes xs s => .axes (xs.map f) (mapAxes f s)
  | .product xs s => .product (xs.map f) (mapProduct f s)
  | .scan js out xs => .scan (mapLists f js) (mapLists f out) (xs.map f)
  | .prepare js out xs s => .prepare (mapLists f js) (mapLists f out) (xs.map f)
      (QuadraticJetPreparationMachine.mapState f s)
  | .root js out xs cs s => .root (mapLists f js) (mapLists f out) (xs.map f)
      (QuadraticRegularRootMachine.mapInput f (JetRootsMachine.rootInput input cs))
      (QuadraticRegularRootMachine.represent a f (JetRootsMachine.rootInput input cs) D s)
  | .save js out xs candidate =>
      .save (mapLists f js) (mapLists f out) (xs.map f) (candidate.map f)
  | .reverse xs out => .reverse (mapLists f xs) (mapLists f out)
  | .emit out => .emit (out.map (mapLists f))
  | .done out => .done (out.map (mapLists f))

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Raw materialized inputs have their canonical decoded representation. -/
theorem encode_decode_input (a : F) (input : Input F) :
    mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input := by
  cases input
  simp [mapInput, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

/-- Every preparation instruction retains its full child cost and outer wrapper. -/
theorem preparation_trace {a : F} {input : Input F} {D L n : ℕ}
    (js out : List (List (Pair F))) (xs : List (Pair F))
    {s t : QuadraticJetPreparationMachine.Configuration F} {c : Cost}
    (h : QuadraticJetPreparationMachine.Trace n s c t) :
    ∃ d, Trace a input D L n (.prepare js out xs s) d (.prepare js out xs t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Every root instruction retains its full child cost and outer wrapper. -/
theorem root_trace {a : F} {input : Input F} {D L n : ℕ}
    {payload : QuadraticRegularRootMachine.Input F}
    (js out : List (List (Pair F))) (xs : List (Pair F))
    {s t : QuadraticRegularRootMachine.Configuration F} {c : Cost}
    (h : QuadraticRegularRootMachine.Trace a payload D L n s c t) :
    ∃ d, Trace a input D L n (.root js out xs payload s) d (.root js out xs payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- The factor is absolute and does not depend on the number of enumerated candidates. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : JetRootsMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : JetRootsMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : JetRootsMachine.Cost}, JetRootsMachine.Step input D L s c t →
      ∃ n d, Trace a (mapInput encode input) D L n (represent a encode input D s) d
        (represent a encode input D t) ∧ n + d.total ≤ 268435456 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | start => exact ⟨1, charge 4 1 0, single rfl, by decide⟩
  | count => exact ⟨1, charge 4 1 0, single rfl, by decide⟩
  | counted => exact ⟨1, charge 4 1 0, single rfl, by decide⟩
  | bound => exact ⟨1, charge 5 2 0, single rfl, by decide⟩
  | bounded => exact ⟨1, charge 3 1 0, single rfl, by decide⟩
  | @axes xs s t c h =>
      refine ⟨1, enumerationCost c + wrapper, single ?_, ?_⟩
      · simp only [represent, step, mapInput, (axes_step_map encode h).step_eq]
      · cases h <;> decide
  | axesDone => exact ⟨1, charge 4 0 0, single rfl, by decide⟩
  | axesFailed => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | @product xs s t c h =>
      refine ⟨1, enumerationCost c + wrapper, single ?_, ?_⟩
      · simp only [represent, step, (product_step_map encode h).step_eq]
      · cases h <;> decide
  | productDone => exact ⟨1, charge 4 0 0, single rfl, by decide⟩
  | next => exact ⟨1, charge 6 0 0, single rfl, by decide⟩
  | prepare h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticJetPreparationMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := preparation_trace (a := a) (input := mapInput encode input)
        (D := D) (L := L) _ _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | prepared => exact ⟨1, charge 5 0 0 + allocation 4, single rfl, by decide⟩
  | prepareFailed => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | root h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticRegularRootMachine.step_lowering a ha _ D L h
      obtain ⟨d, hd, he⟩ := root_trace (input := mapInput encode input) _ _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | success => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | skipped => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | save => exact ⟨1, charge 5 0 0, single rfl, by decide⟩
  | scanned => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | reverse => exact ⟨1, charge 5 0 0, single rfl, by decide⟩
  | reversed => exact ⟨1, charge 2 0 0 + allocation 1, single rfl, by decide⟩
  | emit => exact ⟨1, charge 2 0 1, single rfl, by decide⟩

/-- Compose the fixed factor over total source steps, with no per-iteration exponentiation. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : JetRootsMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : JetRootsMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : JetRootsMachine.Cost}, JetRootsMachine.Trace input D L n s c t →
      ∃ steps d, Trace a (mapInput encode input) D L steps (represent a encode input D s) d
        (represent a encode input D t) ∧ steps + d.total ≤ 268435456 * n := by
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
    (input : JetRootsMachine.Input (QuadraticAlgebra F a 0)) (D L fuel : ℕ)
    (s : JetRootsMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ steps d, runFuel a (mapInput encode input) D L steps (represent a encode input D s) =
      (represent a encode input D (JetRootsMachine.runFuel input D L fuel s).1, d) ∧
      steps + d.total ≤ 268435456 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := JetRootsMachine.runFuel_refines input D L fuel s
  obtain ⟨steps, d, hd, hb⟩ := trace_lowering a ha input D L ht
  exact ⟨steps, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Completed source execution transfers directly to already materialized coordinate inputs. -/
theorem start_run_lowering (a : F) (ha : ¬IsSquare a) (input : Input F) (D L fuel : ℕ)
    (samples : List (Pair F)) (out : Option (List (List (QuadraticAlgebra F a 0))))
    (sourceCost : JetRootsMachine.Cost) :
    letI := fieldOfNonsquare a ha
    JetRootsMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L fuel
      (.start (samples.map (ArithmeticMachine.decode a))) = (.done out, sourceCost) →
    ∃ steps c, runFuel a input D L steps (.start samples) =
      (.done (out.map (mapLists encode)), c) ∧ steps + c.total ≤ 268435456 * fuel := by
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

/-- Actual ordered output is the full finite-jet specification, with duplicates preserved. -/
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
      out.map (fun xs => JetHornerMachine.coefficientPolynomial
        (xs.map (ArithmeticMachine.decode a))) =
          (JetRootsMachine.tuples (input.alphabet.map (ArithmeticMachine.decode a))
            (input.order + 1)).filterMap
              (JetRootsMachine.jetSolution Q (ArithmeticMachine.decode a input.center) D) ∧
      (∀ xs ∈ out, xs.length = D + 1) ∧ out.length ≤ input.alphabet.length ^ (input.order + 1) ∧
      steps + c.total ≤ 268435456 * JetRootsMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) D L samples.length := by
  let := fieldOfNonsquare a ha
  intro hweight
  obtain ⟨out, sourceCost, hs, hspec, hwidth, hcount, _⟩ :=
    JetRootsMachine.computation_runFuel_correct Q
    (ArithmeticMachine.decode a input.center) (input.alphabet.map (ArithmeticMachine.decode a))
    (mapInput (ArithmeticMachine.decode a) input).terms points
    (samples.map (ArithmeticMachine.decode a)) hsamples (by simpa using hq) hQ hr hlookup hweight
  change JetRootsMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L
    (JetRootsMachine.fuel (mapInput (ArithmeticMachine.decode a) input) D L
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a))) = (.done (some out), sourceCost) at hs
  obtain ⟨steps, c, ht, hb⟩ := start_run_lowering a ha input D L _ samples (some out) sourceCost hs
  refine ⟨steps, c, mapLists encode out, ht, ?_, ?_, ?_, ?_⟩
  · simpa [mapLists, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode] using hspec
  · intro xs hx
    obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hx
    simpa using hwidth ys hy
  · simpa [mapLists] using hcount
  · simpa only [List.length_map] using hb

end ReedSolomon.HiddenDerivative.QuadraticJetRootsMachine
