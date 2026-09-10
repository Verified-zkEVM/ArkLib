/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateNormalizeMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Same-execution coordinate normalization

All insertion cursors, key comparisons and cancellation outcomes are retained. Each source edge
lowers to actual base instructions with an absolute factor and the identical emitted term list.
-/

@[expose] public section

namespace MvPolynomial.QuadraticNormalizeMachine

open QuadraticAlgebra
open QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Represent coefficients while sharing materialized factor lists. -/
def mapTerm {K J : Type*} (f : K → J) (t : EvaluationMachine.Term K) :
    EvaluationMachine.Term J := (f t.1, t.2)
/-- Preserve term order, duplicates and zero coefficients. -/
def mapTerms {K J : Type*} (f : K → J) (ts : List (EvaluationMachine.Term K)) := ts.map (mapTerm f)

/-- Pointwise representation of every insertion and key-comparison cursor. -/
def mapState {K J : Type*} (f : K → J) :
    DenseNormalizeMachine.Configuration K → DenseNormalizeMachine.Configuration J
  | .terms ts out => .terms (mapTerms f ts) (mapTerms f out)
  | .search c fs rest pre ts => .search (f c) fs (mapTerms f rest) (mapTerms f pre) (mapTerms f ts)
  | .compare c fs t is js rest pre ts => .compare (f c) fs (mapTerm f t) is js
      (mapTerms f rest) (mapTerms f pre) (mapTerms f ts)
  | .sum c fs rest pre ts => .sum (f c) fs (mapTerms f rest) (mapTerms f pre) (mapTerms f ts)
  | .restore pre out ts => .restore (mapTerms f pre) (mapTerms f out) (mapTerms f ts)
  | .done out => .done (mapTerms f out)

variable {F : Type*} [Field F] [DecidableEq F]

/-- The actual pair comparison is exactly the quadratic-algebra zero predicate. -/
theorem equality_spec (a : F) (v : QuadraticAlgebra F a 0) :
    ArithmeticMachine.specification ⟨a, encode v, (0, 0)⟩ .equal = .boolean (decide (v = 0)) := by
  by_cases hv : v = 0
  · subst v; simp [ArithmeticMachine.specification, encode]
  · have hz : ¬(v.re = 0 ∧ v.im = 0) := by
      intro h
      apply hv
      ext <;> simp [h.1, h.2]
    by_cases hr : v.re = 0
    · have hi : v.im ≠ 0 := fun hi => hz ⟨hr, hi⟩
      simp [ArithmeticMachine.specification, encode, hv, hr, hi]
    · simp [ArithmeticMachine.specification, encode, hv, hr]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Actual base instructions preserve their retained input and full ledger. -/
theorem arithmetic_trace {a : F} (k : Continuation F) {payload : ArithmeticMachine.Input F}
    {n : ℕ} {s t : ArithmeticMachine.Configuration F} {c : ArithmeticMachine.Cost}
    (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a n (.call k payload s) d (.call k payload t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨delegated c + d, .cons ?_ hd, ?_⟩
      · simp only [step, head.step_eq]
      · rw [total_add, delegated_total, he, base_total_add]
        omega

/-- A retained program and its actual return edge have bounded concrete work. -/
theorem call_lowering (a : F) (k : Continuation F) (payload : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (t : Configuration F) (d : Cost)
    (hd : d.total ≤ 16)
    (hr : step a (.call k payload (.done (ArithmeticMachine.specification payload op))) =
      some (t, d)) :
    ∃ n c, Trace a n (.call k payload (.start op)) c t ∧ n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace payload op
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) k ht
  refine ⟨n + 1, c + d, hc.trans (single hr), ?_⟩
  have hm := ArithmeticMachine.cost_total_le op
  rw [total_add, he]
  omega

/-- Each original rule lowers to the same coordinate cursor, including cancellations. -/
theorem step_lowering {a : F}
    {s t : DenseNormalizeMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : DenseNormalizeMachine.Cost} (h : DenseNormalizeMachine.Step s c t) :
    ∃ n d, Trace a n (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
      n + d.total ≤ 512 := by
  have prepend {s t : Configuration F} {k : Continuation F} {payload : ArithmeticMachine.Input F}
      {op : ArithmeticMachine.Operation} {d : Cost} (hd : d.total ≤ 16)
      (hs : step a s = some (.call k payload (.start op), d))
      (hr : ∃ n c, Trace a n (.call k payload (.start op)) c t ∧ n + c.total ≤ 256) :
      ∃ n c, Trace a n s c t ∧ n + c.total ≤ 512 := by
    obtain ⟨n, c, hc, hb⟩ := hr
    exact ⟨n + 1, d + c, .cons hs hc, by rw [total_add]; omega⟩
  cases h with
  | skipZero =>
      apply prepend (d := launch + zeroSeed) (by decide) rfl
      apply call_lowering _ _ _ .equal _
        (administrative (DenseNormalizeMachine.charge 0 2 0 1 0)) (by decide)
      simp [step, equality_spec, ArithmeticMachine.step, mapState, mapTerms, checked]
  | term hv =>
      apply prepend (d := launch + zeroSeed) (by decide) rfl
      apply call_lowering _ _ _ .equal _
        (administrative (DenseNormalizeMachine.charge 0 6 0 1 0)) (by decide)
      simp [step, equality_spec, ArithmeticMachine.step, mapState, mapTerms, checked, hv]
  | equal =>
      apply prepend (d := launch) (by decide) rfl
      exact call_lowering _ _ _ .add _
        (administrative (DenseNormalizeMachine.charge 1 4 0 0 0)) (by decide) rfl
  | zeroSum =>
      apply prepend (d := launch + zeroSeed) (by decide) rfl
      apply call_lowering _ _ _ .equal _
        (administrative (DenseNormalizeMachine.charge 0 3 0 1 0)) (by decide)
      simp [step, equality_spec, ArithmeticMachine.step, mapState, mapTerms, checked]
  | nonzeroSum hv =>
      apply prepend (d := launch + zeroSeed) (by decide) rfl
      apply call_lowering _ _ _ .equal _
        (administrative (DenseNormalizeMachine.charge 0 5 0 1 0)) (by decide)
      simp [step, equality_spec, ArithmeticMachine.step, mapState, mapTerms, mapTerm, checked, hv]
  | pair => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 4 2 0 0),
      single (by simp [mapState, mapTerms, mapTerm, step]), by decide⟩
  | @different c fs t i e k f is js rest pre ts h =>
      have hn : ¬(i = k ∧ e = f) := by omega
      exact ⟨1, administrative (DenseNormalizeMachine.charge 0 6 2 0 0),
        single (by simp [mapState, mapTerms, mapTerm, step, hn]), by decide⟩
  | emit => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 2 0 0 1),
      single rfl, by decide⟩
  | newKey => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 4 0 0 0),
      single rfl, by decide⟩
  | candidate => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 8 0 0 0),
      single rfl, by decide⟩
  | short => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 5 0 0 0),
      single rfl, by decide⟩
  | long => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 5 0 0 0),
      single rfl, by decide⟩
  | restore => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 5 0 0 0),
      single rfl, by decide⟩
  | restored => exact ⟨1, administrative (DenseNormalizeMachine.charge 0 3 0 0 0),
      single rfl, by decide⟩

/-- The same fixed factor covers the complete source trace. -/
theorem trace_lowering {a : F} {n : ℕ}
    {s t : DenseNormalizeMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : DenseNormalizeMachine.Cost} (h : DenseNormalizeMachine.Trace n s c t) :
    ∃ k d, Trace a k (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
      k + d.total ≤ 512 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Finite source execution lowers to the identical represented endpoint. -/
theorem run_lowering (a : F) (fuel : ℕ)
    (s : DenseNormalizeMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a k (.ready (mapState encode s)) =
      (.ready (mapState encode (DenseNormalizeMachine.runFuel fuel s).1), d) ∧
      k + d.total ≤ 512 * fuel := by
  obtain ⟨n, hn, ht⟩ := DenseNormalizeMachine.runFuel_refines fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

omit [DecidableEq F] in
/-- Decoding encoded insertion states preserves every term and key. -/
theorem decode_encode_state (a : F)
    (s : DenseNormalizeMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapTerms, mapTerm, List.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Raw coordinate insertion states survive the canonical round trip. -/
theorem encode_decode_state (a : F) (s : DenseNormalizeMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapTerms, mapTerm, List.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

/-- Arbitrary raw coordinates execute to the exact decoded source cursor and output. -/
theorem decoded_run_lowering (a : F) (fuel : ℕ)
    (s : DenseNormalizeMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (DenseNormalizeMachine.runFuel fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 512 * fuel := by
  obtain ⟨k, d, hr, hb⟩ := run_lowering a fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at hr
  exact ⟨k, d, _, hr, decode_encode_state a _, hb⟩

end MvPolynomial.QuadraticNormalizeMachine
