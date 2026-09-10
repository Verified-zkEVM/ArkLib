/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticRowMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Same-execution refinement of coordinate row operations

Proof-only maps relate all source phases to their coordinate representations. Every source
step lowers to actual arithmetic instructions and list transitions, including rejection and
reversal. The decoded row result is the original ordered add-multiple result.
-/

@[expose] public section

namespace Matrix.QuadraticRowMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only representation of all source row registers and control phases. -/
def mapState {K J : Type*} (f : K → J) :
    RowReductionMachine.Configuration K → RowReductionMachine.Configuration J
  | .scan ts ss rev => .scan (ts.map f) (ss.map f) (rev.map f)
  | .multiply ts ss rev t s => .multiply (ts.map f) (ss.map f) (rev.map f) (f t) (f s)
  | .add ts ss rev t p => .add (ts.map f) (ss.map f) (rev.map f) (f t) (f p)
  | .reverse xs out => .reverse (xs.map f) (out.map f)
  | .done row => .done (row.map f)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding recovers every represented source register. -/
theorem decode_encode_state (a : F)
    (s : RowReductionMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Every materialized coordinate state has the canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : RowReductionMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Every actual base instruction retains its own ledger and the parent-state wrapper. -/
theorem arithmetic_trace {a : F} {scalar : Pair F} (cont : Continuation F)
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a scalar n (.call cont payload s) d (.call cont payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a scalar (.call cont payload s) =
          some (.call cont payload u, delegated c) := by simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- The selected literal program returns its actual materialized pair to its saved continuation. -/
theorem call_returns (a : F) (scalar : Pair F) (cont : Continuation F)
    (payload : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (p : Pair F)
    (hp : ArithmeticMachine.specification payload op = .pair p) :
    ∃ n c, Trace a scalar n (.call cont payload (.start op)) c (resume cont p) ∧
      n + c.total ≤ 189 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace payload op
  rw [hp] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (scalar := scalar) cont ht
  refine ⟨n + 1, c + returned, hc.trans (single rfl), ?_⟩
  have hb := ArithmeticMachine.cost_total_le op
  rw [total_add, he]
  change n + 1 + ((ArithmeticMachine.cost op).total + 3 * n + 4) ≤ 189
  omega

/-- A source product lowers to the actual base multiplication program and return. -/
theorem multiply_lowering (a : F) (scalar t s : QuadraticAlgebra F a 0)
    (ts ss rev : List (Pair F)) :
    ∃ k c, Trace a (encode scalar) k
      (.ready (.multiply ts ss rev (encode t) (encode s))) c
      (.ready (.add ts ss rev (encode t) (encode (scalar * s)))) ∧ k + c.total ≤ 256 := by
  have hm : ArithmeticMachine.specification ⟨a, encode scalar, encode s⟩ .mul =
      .pair (encode (scalar * s)) := by rw [← mulCoordinates_eq a scalar s]; rfl
  obtain ⟨k, c, hc, hb⟩ := call_returns a (encode scalar) (.product ts ss rev (encode t))
    ⟨a, encode scalar, encode s⟩ .mul (encode (scalar * s)) hm
  refine ⟨k + 1, (administrative RowReductionMachine.multiplyCost + launch) + c,
    .cons rfl hc, ?_⟩
  rw [total_add]
  change k + 1 + (11 + c.total) ≤ 256
  omega

/-- A source addition lowers to base addition followed by an explicit output-cell allocation. -/
theorem add_lowering (a : F) (scalar : Pair F) (t p : QuadraticAlgebra F a 0)
    (ts ss rev : List (Pair F)) :
    ∃ k c, Trace a scalar k (.ready (.add ts ss rev (encode t) (encode p))) c
      (.ready (.scan ts ss (encode (t + p) :: rev))) ∧ k + c.total ≤ 256 := by
  have hm : ArithmeticMachine.specification ⟨a, encode t, encode p⟩ .add =
      .pair (encode (t + p)) := rfl
  obtain ⟨k, c, hc, hb⟩ := call_returns a scalar (.sum ts ss rev)
    ⟨a, encode t, encode p⟩ .add (encode (t + p)) hm
  refine ⟨k + 1 + 1, launch + (c + saveCost), .cons rfl (hc.trans (single rfl)), ?_⟩
  rw [total_add, total_add]
  change k + 1 + 1 + (7 + (c.total + 6)) ≤ 256
  omega

/-- Every source step has a bounded same-endpoint base-instruction execution. -/
theorem step_lowering {a : F} {scalar : QuadraticAlgebra F a 0}
    {s t : RowReductionMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : RowReductionMachine.Cost} (h : RowReductionMachine.Step scalar s c t) :
    ∃ n d, Trace a (encode scalar) n (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ n + d.total ≤ 256 := by
  cases h with
  | multiply => exact multiply_lowering _ _ _ _ _ _ _
  | add => exact add_lowering _ _ _ _ _ _ _
  | take => exact ⟨1, administrative RowReductionMachine.takeCost, single rfl, by decide⟩
  | beginReverse =>
      exact ⟨1, administrative RowReductionMachine.beginReverseCost, single rfl, by decide⟩
  | reverse => exact ⟨1, administrative RowReductionMachine.reverseCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative RowReductionMachine.emitCost, single rfl, by decide⟩
  | shortTarget => exact ⟨1, administrative RowReductionMachine.rejectCost, single rfl, by decide⟩
  | shortSource => exact ⟨1, administrative RowReductionMachine.rejectCost, single rfl, by decide⟩

/-- Composition retains each child ledger and the actual represented endpoint. -/
theorem trace_lowering {a : F} {scalar : QuadraticAlgebra F a 0} {n : ℕ}
    {s t : RowReductionMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : RowReductionMachine.Cost} (h : RowReductionMachine.Trace scalar n s c t) :
    ∃ k d, Trace a (encode scalar) k (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ k + d.total ≤ 256 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Arbitrary source execution lowers to the same represented result, including partial phases. -/
theorem run_lowering (a : F) (scalar : QuadraticAlgebra F a 0) (fuel : ℕ)
    (s : RowReductionMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a (encode scalar) k (.ready (mapState encode s)) =
      (.ready (mapState encode (RowReductionMachine.runFuel scalar fuel s).1), d) ∧
      k + d.total ≤ 256 * fuel := by
  obtain ⟨n, hn, ht⟩ := RowReductionMachine.runFuel_refines scalar fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Coordinate input runs to the exact decoded source endpoint with a real execution ledger. -/
theorem decoded_run_lowering (a : F) (scalar : Pair F) (fuel : ℕ)
    (s : RowReductionMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a scalar k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (RowReductionMachine.runFuel (ArithmeticMachine.decode a scalar) fuel
          (mapState (ArithmeticMachine.decode a) s)).1 ∧ k + d.total ≤ 256 * fuel := by
  obtain ⟨k, d, he, hb⟩ := run_lowering a (ArithmeticMachine.decode a scalar) fuel
    (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- Equal-length materialized rows produce the ordered row formula, including any RHS entry. -/
theorem row_correct (a : F) (scalar : Pair F) (target source : List (Pair F))
    (hlen : target.length = source.length) :
    ∃ k c row, runFuel a scalar k (.ready (.scan target source [])) = (.ready (.done row), c) ∧
      row.map (ArithmeticMachine.decode a) = List.zipWith
        (fun t s => t + ArithmeticMachine.decode a scalar * s)
        (target.map (ArithmeticMachine.decode a)) (source.map (ArithmeticMachine.decode a)) ∧
      row.length = target.length ∧ k + c.total ≤ 1024 * target.length + 512 := by
  obtain ⟨k, c, t, he, ht, hb⟩ := decoded_run_lowering a scalar (4 * target.length + 2)
    (.scan target source [])
  have hs := RowReductionMachine.row_runFuel (ArithmeticMachine.decode a scalar)
    (target.map (ArithmeticMachine.decode a)) (source.map (ArithmeticMachine.decode a))
    (by simpa using hlen)
  simp only [List.length_map] at hs
  simp only [mapState, List.map_nil, hs] at ht
  cases t
  all_goals try contradiction
  case done row =>
    have hr := RowReductionMachine.Configuration.done.inj ht
    refine ⟨k, c, row, he, hr, ?_, ?_⟩
    · have hl := congrArg List.length hr
      simpa [hlen] using hl
    · omega

/-- Mismatched rows reject after their matching prefix, without returning a partial row. -/
theorem rejection_correct (a : F) (scalar : Pair F) (target source : List (Pair F))
    (hlen : target.length ≠ source.length) :
    ∃ k c, runFuel a scalar k (.ready (.scan target source [])) = (.ready .rejected, c) ∧
      k + c.total ≤ 768 * min target.length source.length + 256 := by
  obtain ⟨k, c, t, he, ht, hb⟩ := decoded_run_lowering a scalar
    (3 * min target.length source.length + 1) (.scan target source [])
  have hs := RowReductionMachine.rejection_runFuel (ArithmeticMachine.decode a scalar)
    (target.map (ArithmeticMachine.decode a)) (source.map (ArithmeticMachine.decode a))
    (by simpa using hlen)
  simp only [List.length_map] at hs
  simp only [mapState, List.map_nil, hs] at ht
  cases t
  all_goals try contradiction
  exact ⟨k, c, he, by omega⟩

end Matrix.QuadraticRowMachine
