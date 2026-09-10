/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticPivotSolveMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Same-execution coordinate pivot correction

Every source dot, scalar and indexed-update phase lowers to actual retained base instructions.
The source additive correction is preserved even for a nonzero initial pivot value. Proof-only
maps relate all partial states. Only inverse semantics require a certified nonsquare parameter.
-/

@[expose] public section

namespace Matrix.QuadraticPivotSolveMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only pointwise representation of every pivot-solve phase. -/
def mapState {K J : Type*} (f : K → J) :
    PivotSolveMachine.Configuration K → PivotSolveMachine.Configuration J
  | .dot cs vs s => .dot (cs.map f) (vs.map f) (f s)
  | .lookup xs i s => .lookup (xs.map f) i (f s)
  | .check p s => .check (f p) (f s)
  | .inverse p s => .inverse (f p) (f s)
  | .negate inv s => .negate (f inv) (f s)
  | .difference inv neg => .difference (f inv) (f neg)
  | .scale inv d => .scale (f inv) (f d)
  | .update xs i rev d => .update (xs.map f) i (rev.map f) (f d)
  | .restore rev out => .restore (rev.map f) (out.map f)
  | .done out => .done (out.map f)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

/-- Proof-only materialization of the immutable source input parameters. -/
def encodeInput (a : F) (r : PivotSolveMachine.Row (QuadraticAlgebra F a 0))
    (j : ℕ) (v : List (QuadraticAlgebra F a 0)) : Input F :=
  ⟨a, (r.1.map encode, encode r.2), j, v.map encode⟩

omit [DecidableEq F] in
/-- Decoding an encoded phase recovers the source phase. -/
theorem decode_encode_state (a : F)
    (s : PivotSolveMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Every raw coordinate phase has the canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : PivotSolveMachine.Configuration (Pair F)) :
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
theorem arithmetic_trace {input : Input F} (cont : Continuation F)
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace input n (.arithmetic cont payload s) d (.arithmetic cont payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step input (.arithmetic cont payload s) =
          some (.arithmetic cont payload u, delegated c) := by simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- An actual arithmetic program and its result branch execute with the full child ledger. -/
theorem arithmetic_returns (input : Input F) (cont : Continuation F)
    (payload : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (t : Configuration F) (r : Cost)
    (hr : resume input cont (ArithmeticMachine.specification payload op) = some (t, r))
    (hb : r.total ≤ 8) :
    ∃ n c, Trace input n (.arithmetic cont payload (.start op)) c t ∧ n + c.total ≤ 193 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace payload op
  obtain ⟨c, hc, he⟩ := arithmetic_trace (input := input) cont ht
  have hs : step input
      (.arithmetic cont payload (.done (ArithmeticMachine.specification payload op)))
      =
      some (t, r) := by simpa only [step, ArithmeticMachine.step] using hr
  refine ⟨n + 1, c + r, hc.trans (single hs), ?_⟩
  have hm := ArithmeticMachine.cost_total_le op
  rw [total_add, he]
  omega

/-- Launch, every actual arithmetic instruction and the result branch have bounded total work. -/
theorem scalar_lowering (input : Input F) (s t : Configuration F) (cont : Continuation F)
    (payload : ArithmeticMachine.Input F) (op : ArithmeticMachine.Operation) (c r : Cost)
    (hs : step input s = some (.arithmetic cont payload (.start op), c))
    (hr : resume input cont (ArithmeticMachine.specification payload op) = some (t, r))
    (hc : c.total ≤ 32) (hb : r.total ≤ 8) :
    ∃ n d, Trace input n s d t ∧ n + d.total ≤ 256 := by
  obtain ⟨n, d, hd, he⟩ := arithmetic_returns input cont payload op t r hr hb
  refine ⟨n + 1, c + d, .cons hs hd, ?_⟩
  rw [total_add]
  omega

/-- A source dot update runs multiplication then addition with their retained operands. -/
theorem dot_lowering (input : Input F) (cs vs : List (Pair F))
    (x y s : QuadraticAlgebra F input.parameter 0) :
    ∃ k c, Trace input k (.ready (.dot (encode x :: cs) (encode y :: vs) (encode s))) c
      (.ready (.dot cs vs (encode (s + x * y)))) ∧ k + c.total ≤ 512 := by
  have hm : ArithmeticMachine.specification ⟨input.parameter, encode x, encode y⟩ .mul =
      .pair (encode (x * y)) := by rw [← mulCoordinates_eq input.parameter x y]; rfl
  obtain ⟨n, c, hc, hb⟩ := scalar_lowering input
    (.ready (.dot (encode x :: cs) (encode y :: vs) (encode s))) _
    (.dotProduct cs vs (encode s))
    ⟨input.parameter, encode x, encode y⟩ .mul
    (administrative PivotSolveMachine.dotCost + launch) returned rfl
      (by rw [hm]; rfl) (by decide) (by decide)
  obtain ⟨m, d, hd, he⟩ := scalar_lowering input (.addDot cs vs (encode s) (encode (x * y)))
    (.ready (.dot cs vs (encode (s + x * y)))) (.dotSum cs vs)
    ⟨input.parameter, encode s, encode (x * y)⟩ .add launch returned rfl rfl (by decide) (by decide)
  refine ⟨n + m, c + d, hc.trans hd, ?_⟩
  rw [total_add]
  omega

/-- The pivot coordinate is incremented and its materialized cell is allocated separately. -/
theorem update_lowering (input : Input F) (xs rev : List (Pair F))
    (x d : QuadraticAlgebra F input.parameter 0) :
    ∃ k c, Trace input k (.ready (.update (encode x :: xs) 0 rev (encode d))) c
      (.ready (.restore rev (encode (x + d) :: xs))) ∧ k + c.total ≤ 512 := by
  obtain ⟨n, c, hc, hb⟩ := scalar_lowering input
    (.ready (.update (encode x :: xs) 0 rev (encode d))) (.saveUpdate rev xs (encode (x + d)))
    (.update rev xs) ⟨input.parameter, encode x, encode d⟩ .add launch returned rfl rfl
    (by decide) (by decide)
  refine ⟨n + 1, c + (administrative PivotSolveMachine.updateHitCost + allocation),
    hc.trans (single rfl), ?_⟩
  rw [total_add]
  change n + 1 + (c.total + 8) ≤ 512
  omega

/-- Every source step lowers to the same represented state and a bounded actual ledger. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (r : PivotSolveMachine.Row (QuadraticAlgebra F a 0)) (j : ℕ)
    (v : List (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : PivotSolveMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : PivotSolveMachine.Cost}, PivotSolveMachine.Step r j v s c t →
      ∃ n d, Trace (encodeInput a r j v) n (.ready (mapState encode s)) d
        (.ready (mapState encode t)) ∧ n + d.total ≤ 512 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  have small {s t : Configuration F}
      (h : ∃ n d, Trace (encodeInput a r j v) n s d t ∧ n + d.total ≤ 256) :
      ∃ n d, Trace (encodeInput a r j v) n s d t ∧ n + d.total ≤ 512 := by
    obtain ⟨n, d, hd, hb⟩ := h
    exact ⟨n, d, hd, by omega⟩
  cases h with
  | dot => exact dot_lowering _ _ _ _ _ _
  | dotEnd => exact ⟨1, administrative PivotSolveMachine.lookupStartCost, single rfl, by decide⟩
  | dotLeft => exact ⟨1, administrative PivotSolveMachine.rejectCost, single rfl, by decide⟩
  | dotRight => exact ⟨1, administrative PivotSolveMachine.rejectCost, single rfl, by decide⟩
  | seek => exact ⟨1, administrative PivotSolveMachine.seekCost, single rfl, by decide⟩
  | hit => exact ⟨1, administrative PivotSolveMachine.hitCost, single rfl, by decide⟩
  | missing => exact ⟨1, administrative PivotSolveMachine.rejectCost, single rfl, by decide⟩
  | zero =>
      apply small
      exact scalar_lowering _ _ _ _ _ .equal _
        (administrative PivotSolveMachine.zeroCost + returned) rfl
        (by simp [resume, ArithmeticMachine.specification, encode, mapState])
        (by decide) (by decide)
  | @check p s hp =>
      have hz : ¬(p.re = 0 ∧ p.im = 0) := by
        intro h
        apply hp
        ext <;> simp [h.1, h.2]
      apply small
      exact scalar_lowering _ _ _ _ _ .equal _
        (administrative PivotSolveMachine.checkCost + returned) rfl (by
          by_cases hr : p.re = 0
          · have hi : p.im ≠ 0 := fun hi => hz ⟨hr, hi⟩
            simp [resume, ArithmeticMachine.specification, encode, mapState, hr, hi]
          · simp [resume, ArithmeticMachine.specification, encode, mapState, hr])
        (by decide) (by decide)
  | @inverse p s =>
      have hm : ArithmeticMachine.specification ⟨a, encode p, encode p⟩ .inv =
          .pair (encode p⁻¹) := by
        rw [← invCoordinates_eq a ha p]
        simp only [ArithmeticMachine.specification, invCoordinates, encode, sub_eq_add_neg]
      apply small
      exact scalar_lowering _ _ _ _ _ .inv _ returned rfl
        (by dsimp only [encodeInput]; rw [hm]; rfl) (by decide) (by decide)
  | negate =>
      apply small
      exact scalar_lowering _ _ _ _ _ .neg _ returned rfl rfl (by decide) (by decide)
  | difference =>
      apply small
      exact scalar_lowering _ _ _ _ _ .add _ returned rfl rfl (by decide) (by decide)
  | @scale inv d =>
      have hm : ArithmeticMachine.specification ⟨a, encode d, encode inv⟩ .mul =
          .pair (encode (d * inv)) := by rw [← mulCoordinates_eq a d inv]; rfl
      apply small
      exact scalar_lowering _ _ _ _ _ .mul _ returned rfl
        (by dsimp only [encodeInput]; rw [hm]; rfl) (by decide) (by decide)
  | updateSeek =>
      exact ⟨1, administrative PivotSolveMachine.updateSeekCost + allocation,
        single rfl, by decide⟩
  | updateHit => exact update_lowering _ _ _ _ _
  | updateMissing => exact ⟨1, administrative PivotSolveMachine.rejectCost, single rfl, by decide⟩
  | restore =>
      exact ⟨1, administrative PivotSolveMachine.reverseCost + allocation, single rfl, by decide⟩
  | emit => exact ⟨1, administrative PivotSolveMachine.emitCost, single rfl, by decide⟩

/-- Actual traces compose without dropping arithmetic or indexed-update work. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (r : PivotSolveMachine.Row (QuadraticAlgebra F a 0)) (j : ℕ)
    (v : List (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : PivotSolveMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : PivotSolveMachine.Cost}, PivotSolveMachine.Trace r j v n s c t →
      ∃ k d, Trace (encodeInput a r j v) k (.ready (mapState encode s)) d
        (.ready (mapState encode t)) ∧ k + d.total ≤ 512 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha r j v head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Every finite source execution lowers to its exact represented endpoint. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a)
    (r : PivotSolveMachine.Row (QuadraticAlgebra F a 0)) (j : ℕ)
    (v : List (QuadraticAlgebra F a 0)) (fuel : ℕ)
    (s : PivotSolveMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel (encodeInput a r j v) k (.ready (mapState encode s)) =
      (.ready (mapState encode (PivotSolveMachine.runFuel r j v fuel s).1), d) ∧
      k + d.total ≤ 512 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := PivotSolveMachine.runFuel_refines r j v fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha r j v ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Raw retained inputs and partial states execute to the exact decoded source endpoint. -/
theorem decoded_run_lowering (input : Input F) (ha : ¬IsSquare input.parameter) (fuel : ℕ)
    (s : PivotSolveMachine.Configuration (Pair F)) :
    letI := fieldOfNonsquare input.parameter ha
    ∃ k d t, runFuel input k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode input.parameter) t =
        (PivotSolveMachine.runFuel
          (input.row.1.map (ArithmeticMachine.decode input.parameter),
            ArithmeticMachine.decode input.parameter input.row.2) input.index
          (input.values.map (ArithmeticMachine.decode input.parameter)) fuel
          (mapState (ArithmeticMachine.decode input.parameter) s)).1 ∧
      k + d.total ≤ 512 * fuel := by
  let := fieldOfNonsquare input.parameter ha
  obtain ⟨k, d, he, hb⟩ := run_lowering input.parameter ha
    (input.row.1.map (ArithmeticMachine.decode input.parameter),
      ArithmeticMachine.decode input.parameter input.row.2) input.index
    (input.values.map (ArithmeticMachine.decode input.parameter)) fuel
    (mapState (ArithmeticMachine.decode input.parameter) s)
  rw [encode_decode_state] at he
  have hi : encodeInput input.parameter
      (input.row.1.map (ArithmeticMachine.decode input.parameter),
        ArithmeticMachine.decode input.parameter input.row.2) input.index
      (input.values.map (ArithmeticMachine.decode input.parameter)) = input := by
    cases input
    simp [encodeInput, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  rw [hi] at he
  exact ⟨k, d, _, he, decode_encode_state input.parameter _, hb⟩

/-- A valid pivot performs exactly the source additive correction with an input-only bound. -/
theorem evaluation_correct (a : F) (ha : ¬IsSquare a)
    (r : PivotSolveMachine.Row (QuadraticAlgebra F a 0)) (j : ℕ)
    (v : List (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    r.1.length = v.length → j < r.1.length → r.1.getD j 0 ≠ 0 →
    ∃ k c, runFuel (encodeInput a r j v) k (.ready (.dot (r.1.map encode) (v.map encode) (0, 0))) =
      (.ready (.done ((PivotSolveMachine.result r j v).map encode)), c) ∧
      k + c.total ≤ 512 * (r.1.length + 3 * j + 9) := by
  let := fieldOfNonsquare a ha
  intro hlen hj hp
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha r j v (r.1.length + 3 * j + 9) (.dot r.1 v 0)
  rw [PivotSolveMachine.evaluation_runFuel r j v hlen hj hp] at hr
  exact ⟨k, c, hr, hb⟩

end Matrix.QuadraticPivotSolveMachine
