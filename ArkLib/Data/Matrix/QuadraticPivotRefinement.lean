/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticPivotMachine
public import ArkLib.Data.Matrix.QuadraticRowRefinement

/-!
# Same-execution coordinate pivot refinement

All source lookup, branch and scalar phases are represented explicitly. Source row states map
to the actual coordinate row child. Nonsquareness certifies source field inversion; executable
dispatch itself takes only the parameter and materialized coordinate registers.
-/

@[expose] public section

namespace Matrix.QuadraticPivotMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only pointwise representation of source pivot and delegated row states. -/
def mapState {K J : Type*} (f : K → J) :
    PivotEliminationMachine.Configuration K → PivotEliminationMachine.Configuration J
  | .lookup p t ps ts i => .lookup (p.map f) (t.map f) (ps.map f) (ts.map f) i
  | .check p t x e => .check (p.map f) (t.map f) (f x) (f e)
  | .inverse p t x e => .inverse (p.map f) (t.map f) (f x) (f e)
  | .negate p t e inv => .negate (p.map f) (t.map f) (f e) (f inv)
  | .factor p t neg inv => .factor (p.map f) (t.map f) (f neg) (f inv)
  | .row factor s => .row (f factor) (QuadraticRowMachine.mapState f s)
  | .done out => .done (out.map f)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding recovers every represented source state, including its suspended row. -/
theorem decode_encode_state (a : F)
    (s : PivotEliminationMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode,
    QuadraticRowMachine.decode_encode_state]

omit [DecidableEq F] in
/-- Every raw coordinate state has a canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : PivotEliminationMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode,
    QuadraticRowMachine.encode_decode_state]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Every actual base instruction retains its own ledger and the parent-state wrapper. -/
theorem arithmetic_trace {a : F} (cont : Continuation F)
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a n (.arithmetic cont payload s) d (.arithmetic cont payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a (.arithmetic cont payload s) =
          some (.arithmetic cont payload u, delegated c) := by simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- An actual arithmetic program and its result branch execute with the full child ledger. -/
theorem arithmetic_returns (a : F) (cont : Continuation F) (payload : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (t : Configuration F) (r : Cost)
    (hr : resume cont (ArithmeticMachine.specification payload op) = some (t, r))
    (hb : r.total ≤ 8) :
    ∃ n c, Trace a n (.arithmetic cont payload (.start op)) c t ∧ n + c.total ≤ 193 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace payload op
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) cont ht
  have hs : step a (.arithmetic cont payload (.done (ArithmeticMachine.specification payload op))) =
      some (t, r) := by simpa only [step, ArithmeticMachine.step] using hr
  refine ⟨n + 1, c + r, hc.trans (single hs), ?_⟩
  have hm := ArithmeticMachine.cost_total_le op
  rw [total_add, he]
  omega

/-- Launch, every actual arithmetic instruction and the result branch have bounded total work. -/
theorem scalar_lowering (a : F) (s t : Configuration F) (cont : Continuation F)
    (payload : ArithmeticMachine.Input F) (op : ArithmeticMachine.Operation) (c r : Cost)
    (hs : step a s = some (.arithmetic cont payload (.start op), c))
    (hr : resume cont (ArithmeticMachine.specification payload op) = some (t, r))
    (hc : c.total ≤ 32) (hb : r.total ≤ 8) :
    ∃ n d, Trace a n s d t ∧ n + d.total ≤ 256 := by
  obtain ⟨n, d, hd, he⟩ := arithmetic_returns a cont payload op t r hr hb
  refine ⟨n + 1, c + d, .cons hs hd, ?_⟩
  rw [total_add]
  omega

/-- Every coordinate row instruction is executed and charged with its parent wrapper. -/
theorem row_trace {a : F} {factor : Pair F} {n : ℕ}
    {s t : QuadraticRowMachine.Configuration F} {c : Cost}
    (h : QuadraticRowMachine.Trace a factor n s c t) :
    ∃ d, Trace a n (.row factor s) d (.row factor t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + rowWrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change _ + 3 + (_ + 3 * _) = _
        omega

/-- Each source pivot step lowers to the same represented endpoint and an actual work bound. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : PivotEliminationMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : PivotEliminationMachine.Cost}, PivotEliminationMachine.Step s c t →
      ∃ n d, Trace a n (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        n + d.total ≤ 1024 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  have small {s t : Configuration F}
      (h : ∃ n d, Trace a n s d t ∧ n + d.total ≤ 256) :
      ∃ n d, Trace a n s d t ∧ n + d.total ≤ 1024 := by
    obtain ⟨n, d, hd, hb⟩ := h
    exact ⟨n, d, hd, by omega⟩
  cases h with
  | missingPivot =>
      exact ⟨1, administrative PivotEliminationMachine.missingCost, single rfl, by decide⟩
  | missingTarget =>
      exact ⟨1, administrative PivotEliminationMachine.missingCost, single rfl, by decide⟩
  | hit => exact ⟨1, administrative PivotEliminationMachine.hitCost, single rfl, by decide⟩
  | seek => exact ⟨1, administrative PivotEliminationMachine.seekCost, single rfl, by decide⟩
  | zero =>
      apply small
      exact scalar_lowering a _ _ _ _ .equal _
        (administrative PivotEliminationMachine.zeroCost + returned) rfl
        (by simp [resume, ArithmeticMachine.specification, encode, mapState, enter])
        (by decide) (by decide)
  | @nonzero p t x e hx =>
      have hx' : ¬(x.re = 0 ∧ x.im = 0) := by
        intro hz
        apply hx
        ext <;> simp [hz.1, hz.2]
      apply small
      exact scalar_lowering a _ _ _ _ .equal _
        (administrative PivotEliminationMachine.checkCost + returned) rfl
        (by
          by_cases hr : x.re = 0
          · have hi : x.im ≠ 0 := fun hi => hx' ⟨hr, hi⟩
            simp [resume, ArithmeticMachine.specification, encode, mapState, enter, hr, hi]
          · simp [resume, ArithmeticMachine.specification, encode, mapState, enter, hr])
        (by decide) (by decide)
  | @inverse p t x e =>
      have hm : ArithmeticMachine.specification ⟨a, encode x, encode x⟩ .inv =
          .pair (encode x⁻¹) := by
        rw [← invCoordinates_eq a ha x]
        simp only [ArithmeticMachine.specification, invCoordinates, encode, sub_eq_add_neg]
      apply small
      exact scalar_lowering a _ _ _ _ .inv _ returned rfl
        (by rw [hm]; rfl) (by decide) (by decide)
  | negate =>
      apply small
      exact scalar_lowering a _ _ _ _ .neg _ returned rfl rfl (by decide) (by decide)
  | @factor p t neg inv =>
      have hm : ArithmeticMachine.specification ⟨a, encode neg, encode inv⟩ .mul =
          .pair (encode (neg * inv)) := by rw [← mulCoordinates_eq a neg inv]; rfl
      apply small
      exact scalar_lowering a _ _ _ _ .mul _ returned rfl
        (by rw [hm]; rfl) (by decide) (by decide)
  | row h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticRowMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := row_trace hc
      exact ⟨n, d, hd, by omega⟩
  | returned =>
      exact ⟨1, administrative PivotEliminationMachine.returnCost, single rfl, by decide⟩
  | rejected =>
      exact ⟨1, administrative PivotEliminationMachine.returnCost, single rfl, by decide⟩

/-- Same-endpoint traces compose without omitting row or arithmetic child work. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : PivotEliminationMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : PivotEliminationMachine.Cost}, PivotEliminationMachine.Trace n s c t →
      ∃ k d, Trace a k (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        k + d.total ≤ 1024 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Any finite source execution lowers to the exact represented endpoint. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a) (fuel : ℕ)
    (s : PivotEliminationMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel a k (enter (mapState encode s)) =
      (enter (mapState encode (PivotEliminationMachine.runFuel fuel s).1), d) ∧
      k + d.total ≤ 1024 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := PivotEliminationMachine.runFuel_refines fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Arbitrary materialized coordinate states reach the exact decoded source endpoint. -/
theorem decoded_run_lowering (a : F) (ha : ¬IsSquare a) (fuel : ℕ)
    (s : PivotEliminationMachine.Configuration (Pair F)) :
    letI := fieldOfNonsquare a ha
    ∃ k d t, runFuel a k (enter s) = (enter t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (PivotEliminationMachine.runFuel fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 1024 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨k, d, he, hb⟩ := run_lowering a ha fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- A valid pivot computes the entire ordered row formula, including any packed RHS entry. -/
theorem elimination_correct (a : F) (ha : ¬IsSquare a)
    (pivot target : List (QuadraticAlgebra F a 0)) (j : ℕ) (p e : QuadraticAlgebra F a 0) :
    letI := fieldOfNonsquare a ha
    pivot[j]? = some p → target[j]? = some e → p ≠ 0 → target.length = pivot.length →
    ∃ k c, runFuel a k (.ready (.lookup (pivot.map encode) (target.map encode)
      (pivot.map encode) (target.map encode) j)) =
      (.ready (.done ((List.zipWith
        (fun t s => t + PivotEliminationMachine.eliminationFactor e p * s) target pivot).map
          encode)), c) ∧ k + c.total ≤ 1024 * (4 * target.length + j + 8) := by
  let := fieldOfNonsquare a ha
  intro hp he hp0 hlen
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha (4 * target.length + j + 8)
    (.lookup pivot target pivot target j)
  rw [PivotEliminationMachine.elimination_runFuel pivot target j p e hp he hp0 hlen] at hr
  exact ⟨k, c, hr, hb⟩

/-- A selected zero pivot rejects through actual base equality instructions before inversion. -/
theorem zeroPivot_correct (a : F) (ha : ¬IsSquare a)
    (pivot target : List (QuadraticAlgebra F a 0)) (j : ℕ) (e : QuadraticAlgebra F a 0)
    (hp : pivot[j]? = some 0) (he : target[j]? = some e) :
    ∃ k c, runFuel a k (.ready (.lookup (pivot.map encode) (target.map encode)
      (pivot.map encode) (target.map encode) j)) = (.ready .rejected, c) ∧
      k + c.total ≤ 1024 * (j + 2) := by
  let := fieldOfNonsquare a ha
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha (j + 2) (.lookup pivot target pivot target j)
  rw [PivotEliminationMachine.zeroPivot_runFuel pivot target j e hp he] at hr
  exact ⟨k, c, hr, hb⟩

/-- Missing indices reject at the original first exhausted cursor. -/
theorem missing_correct (a : F) (ha : ¬IsSquare a)
    (pivot target : List (QuadraticAlgebra F a 0)) (j : ℕ)
    (hm : pivot[j]? = none ∨ target[j]? = none) :
    ∃ k c, runFuel a k (.ready (.lookup (pivot.map encode) (target.map encode)
      (pivot.map encode) (target.map encode) j)) = (.ready .rejected, c) ∧
      k + c.total ≤ 1024 * (min j (min pivot.length target.length) + 1) := by
  let := fieldOfNonsquare a ha
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha (min j (min pivot.length target.length) + 1)
    (.lookup pivot target pivot target j)
  rw [PivotEliminationMachine.missing_runFuel pivot target j hm] at hr
  exact ⟨k, c, hr, hb⟩

end Matrix.QuadraticPivotMachine
