/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateDerivativeMachine
public import ArkLib.Data.MvPolynomial.CoordinateNormalizeRefinement

/-!
# Same-execution coordinate sparse derivative

Each repeated-addition and zero-test edge is implemented by retained base instructions. Factor
cursors, exponents, restoration order and characteristic cancellation match the original machine.
-/

@[expose] public section

namespace MvPolynomial.QuadraticDerivativeMachine

open QuadraticAlgebra
open QuadraticEvaluationMachine (Cost delegated total_add encode)
open QuadraticNormalizeMachine (mapTerm mapTerms equality_spec)

/-- Preserve coefficient, scaling counter, factor cursor and sparse-list order. -/
def mapState {K J : Type*} (f : K → J) :
    PartialDerivativeMachine.Configuration K → PartialDerivativeMachine.Configuration J
  | .terms ts out => .terms (mapTerms f ts) (mapTerms f out)
  | .scan c fs pre ts out => .scan (f c) fs pre (mapTerms f ts) (mapTerms f out)
  | .scale c n v fs pre ts out => .scale (f c) n (f v) fs pre (mapTerms f ts) (mapTerms f out)
  | .test c fs pre ts out => .test (f c) fs pre (mapTerms f ts) (mapTerms f out)
  | .restore c pre fs ts out => .restore (f c) pre fs (mapTerms f ts) (mapTerms f out)
  | .reverse ts out => .reverse (mapTerms f ts) (mapTerms f out)
  | .done out => .done (mapTerms f out)

variable {F : Type*} [Field F] [DecidableEq F]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Actual base instructions preserve their retained input and full ledger. -/
theorem arithmetic_trace {a : F} {j : ℕ} (k : Continuation F) {payload : ArithmeticMachine.Input F}
    {n : ℕ} {s t : ArithmeticMachine.Configuration F} {c : ArithmeticMachine.Cost}
    (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a j n (.call k payload s) d (.call k payload t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨delegated c + d, .cons ?_ hd, ?_⟩
      · simp only [step, head.step_eq]
      · rw [total_add, delegated_total, he, base_total_add]
        omega

/-- A retained program and its actual return edge have bounded concrete work. -/
theorem call_lowering (a : F) (j : ℕ) (k : Continuation F) (payload : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (t : Configuration F) (d : Cost)
    (hd : d.total ≤ 16)
    (hr : step a j (.call k payload (.done (ArithmeticMachine.specification payload op))) =
      some (t, d)) :
    ∃ n c, Trace a j n (.call k payload (.start op)) c t ∧ n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace payload op
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (j := j) k ht
  refine ⟨n + 1, c + d, hc.trans (single hr), ?_⟩
  have hm := ArithmeticMachine.cost_total_le op
  rw [total_add, he]
  omega

/-- Every source instruction lowers to the same sparse derivative state. -/
theorem step_lowering {a : F} {j : ℕ}
    {s t : PartialDerivativeMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : PartialDerivativeMachine.Cost} (h : PartialDerivativeMachine.Step j s c t) :
    ∃ n d, Trace a j n (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
      n + d.total ≤ 512 := by
  have prepend {s t : Configuration F} {k : Continuation F} {payload : ArithmeticMachine.Input F}
      {op : ArithmeticMachine.Operation} {d : Cost} (hd : d.total ≤ 16)
      (hs : step a j s = some (.call k payload (.start op), d))
      (hr : ∃ n c, Trace a j n (.call k payload (.start op)) c t ∧ n + c.total ≤ 256) :
      ∃ n c, Trace a j n s c t ∧ n + c.total ≤ 512 := by
    obtain ⟨n, c, hc, hb⟩ := hr
    exact ⟨n + 1, d + c, .cons hs hc, by rw [total_add]; omega⟩
  cases h with
  | add =>
      apply prepend (d := launch) (by decide) rfl
      exact call_lowering _ _ _ _ .add _
        (administrative (PartialDerivativeMachine.charge 1 5 2 0 0)) (by decide) rfl
  | zeroCoefficient =>
      apply prepend (d := launch + zeroSeed) (by decide) rfl
      apply call_lowering _ _ _ _ .equal _
        (administrative (PartialDerivativeMachine.charge 0 2 0 1 0)) (by decide)
      simp [step, equality_spec, ArithmeticMachine.step, mapState]
  | nonzero hv =>
      apply prepend (d := launch + zeroSeed) (by decide) rfl
      apply call_lowering _ _ _ _ .equal _
        (administrative (PartialDerivativeMachine.charge 0 2 0 1 0)) (by decide)
      simp [step, equality_spec, ArithmeticMachine.step, mapState, hv]
  | skip hi => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 6 1 0 0),
      single (by simp [step, mapState, hi]), by decide⟩
  | zeroExponent => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 2 2 0 0),
      single (by simp [step, mapState]), by decide⟩
  | hit => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 7 3 0 0) + zeroSeed,
      single (by simp [step, mapState, encode]), by decide⟩
  | term => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 4 0 0 0),
      single rfl, by decide⟩
  | finish => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 3 0 0 0),
      single rfl, by decide⟩
  | absent => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 1 0 0 0),
      single rfl, by decide⟩
  | scaled => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 1 1 0 0),
      single rfl, by decide⟩
  | restore => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 5 0 0 0),
      single rfl, by decide⟩
  | store => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 5 0 0 1),
      single rfl, by decide⟩
  | reverse => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 5 0 0 0),
      single rfl, by decide⟩
  | emit => exact ⟨1, administrative (PartialDerivativeMachine.charge 0 2 0 0 1),
      single rfl, by decide⟩

/-- The same fixed factor covers the complete source trace. -/
theorem trace_lowering {a : F} {j : ℕ} {n : ℕ}
    {s t : PartialDerivativeMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : PartialDerivativeMachine.Cost} (h : PartialDerivativeMachine.Trace j n s c t) :
    ∃ k d, Trace a j k (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
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
theorem run_lowering (a : F) (j fuel : ℕ)
    (s : PartialDerivativeMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a j k (.ready (mapState encode s)) =
      (.ready (mapState encode (PartialDerivativeMachine.runFuel j fuel s).1), d) ∧
      k + d.total ≤ 512 * fuel := by
  obtain ⟨n, hn, ht⟩ := PartialDerivativeMachine.runFuel_refines j fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

omit [DecidableEq F] in
/-- Decoding encoded insertion states preserves every term and key. -/
theorem decode_encode_state (a : F)
    (s : PartialDerivativeMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapTerms, mapTerm, List.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Raw coordinate insertion states survive the canonical round trip. -/
theorem encode_decode_state (a : F) (s : PartialDerivativeMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapTerms, mapTerm, List.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

/-- Arbitrary raw coordinates execute to the exact decoded source cursor and output. -/
theorem decoded_run_lowering (a : F) (j fuel : ℕ)
    (s : PartialDerivativeMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a j k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (PartialDerivativeMachine.runFuel j fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 512 * fuel := by
  obtain ⟨k, d, hr, hb⟩ := run_lowering a j fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at hr
  exact ⟨k, d, _, hr, decode_encode_state a _, hb⟩

end MvPolynomial.QuadraticDerivativeMachine
