/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticColumnMachine
public import ArkLib.Data.Matrix.QuadraticPivotRefinement

/-!
# Same-execution coordinate column refinement

Proof-only maps preserve all row order and suspended pivot states. Concrete traces retain
validation and child work. Full-column execution has a bound depending only on input dimensions.
-/

@[expose] public section

namespace Matrix.QuadraticColumnMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only representation of the ordered materialized row list. -/
def mapRows {K J : Type*} (f : K → J) (rs : List (List K)) : List (List J) :=
  rs.map (List.map f)

/-- Pointwise representation preserves source phases, counters and inner pivot states. -/
def mapState {K J : Type*} (f : K → J) :
    ColumnEliminationMachine.Configuration K → ColumnEliminationMachine.Configuration J
  | .begin rs => .begin (mapRows f rs)
  | .validate p rs xs i => .validate (p.map f) (mapRows f rs) (xs.map f) i
  | .check p rs x => .check (p.map f) (mapRows f rs) (f x)
  | .scan p rs rev => .scan (p.map f) (mapRows f rs) (mapRows f rev)
  | .row p rs rev s =>
      .row (p.map f) (mapRows f rs) (mapRows f rev) (QuadraticPivotMachine.mapState f s)
  | .reverse rs out => .reverse (mapRows f rs) (mapRows f out)
  | .done rs => .done (mapRows f rs)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding recovers each represented source state. -/
theorem decode_encode_state (a : F)
    (s : ColumnEliminationMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapRows, List.map_map, Function.comp_def, encode,
    ArithmeticMachine.decode, QuadraticPivotMachine.decode_encode_state]

omit [DecidableEq F] in
/-- Every raw state has a canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : ColumnEliminationMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapRows, List.map_map, Function.comp_def, encode,
    ArithmeticMachine.decode, QuadraticPivotMachine.encode_decode_state]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Every actual base instruction retains its own ledger and the parent-state wrapper. -/
theorem arithmetic_trace {a : F} {j : ℕ}
    (p : List (Pair F)) (rows : List (List (Pair F)))
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a j n (.checking p rows payload s) d (.checking p rows payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a j (.checking p rows payload s) =
          some (.checking p rows payload u, delegated c) := by simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- Actual equality instructions select the same branch, with zero and singleton charges. -/
theorem check_lowering (a : F) (j : ℕ) (p : List (Pair F)) (rows : List (List (Pair F)))
    (x : Pair F) (b : Bool)
    (hb : ArithmeticMachine.specification ⟨a, x, (0, 0)⟩ .equal = .boolean b) :
    ∃ n c, Trace a j n (.ready (.check p rows x)) c (checked p rows b).1 ∧
      n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace ⟨a, x, (0, 0)⟩ .equal
  rw [hb] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (j := j) p rows ht
  have hr : (checked p rows b).2.total ≤ 9 := by cases b <;> dsimp [checked] <;> decide
  refine ⟨n + 1 + 1, (launch + zeroSeed) + (c + (checked p rows b).2),
    .cons rfl (hc.trans (single rfl)), ?_⟩
  have hm := ArithmeticMachine.cost_total_le .equal
  simp only [total_add]
  rw [he]
  change n + 1 + 1 + (11 + ((ArithmeticMachine.cost .equal).total + 3 * n + _)) ≤ 256
  omega

/-- Every pivot-child instruction is preserved and pays the outer state wrapper. -/
theorem pivot_trace {a : F} {j n : ℕ} (p : List (Pair F))
    (rows rev : List (List (Pair F))) {s t : QuadraticPivotMachine.Configuration F} {c : Cost}
    (h : QuadraticPivotMachine.Trace a n s c t) :
    ∃ d, Trace a j n (.pivot p rows rev s) d (.pivot p rows rev t) ∧
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

/-- Each source step lowers to the same represented endpoint with actual bounded work. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a) (j : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : ColumnEliminationMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ColumnEliminationMachine.Cost}, ColumnEliminationMachine.Step j s c t →
      ∃ n d, Trace a j n (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        n + d.total ≤ 4096 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | empty => exact ⟨1, administrative ColumnEliminationMachine.rejectCost, single rfl, by decide⟩
  | begin => exact ⟨1, administrative ColumnEliminationMachine.beginCost, single rfl, by decide⟩
  | missing => exact ⟨1, administrative ColumnEliminationMachine.rejectCost, single rfl, by decide⟩
  | seek => exact ⟨1, administrative ColumnEliminationMachine.seekCost, single rfl, by decide⟩
  | hit => exact ⟨1, administrative ColumnEliminationMachine.hitCost, single rfl, by decide⟩
  | zero =>
      obtain ⟨n, c, hc, hb⟩ := check_lowering a j _ _ (encode 0) true
        (by simp [ArithmeticMachine.specification, encode])
      exact ⟨n, c, hc, by omega⟩
  | @valid p rows x hx =>
      have hz : ¬(x.re = 0 ∧ x.im = 0) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      have he : ArithmeticMachine.specification ⟨a, encode x, (0, 0)⟩ .equal = .boolean false := by
        by_cases hr : x.re = 0
        · have hi : x.im ≠ 0 := fun hi => hz ⟨hr, hi⟩
          simp [ArithmeticMachine.specification, encode, hr, hi]
        · simp [ArithmeticMachine.specification, encode, hr]
      obtain ⟨n, c, hc, hb⟩ := check_lowering a j _ _ (encode x) false he
      exact ⟨n, c, hc, by omega⟩
  | call => exact ⟨1, administrative ColumnEliminationMachine.callCost, single rfl, by decide⟩
  | delegate h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticPivotMachine.step_lowering a ha h
      obtain ⟨d, hd, he⟩ := pivot_trace (j := j) _ _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | store =>
      exact ⟨1, administrative ColumnEliminationMachine.storeCost + allocation,
        single rfl, by decide⟩
  | failed => exact ⟨1, administrative ColumnEliminationMachine.rejectCost, single rfl, by decide⟩
  | beginReverse =>
      exact ⟨1, administrative ColumnEliminationMachine.beginReverseCost, single rfl, by decide⟩
  | reverse =>
      exact ⟨1, administrative ColumnEliminationMachine.reverseCost + allocation,
        single rfl, by decide⟩
  | emit => exact ⟨1, administrative ColumnEliminationMachine.emitCost, single rfl, by decide⟩

/-- Same-endpoint traces compose without omitting row or arithmetic child work. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a) (j : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : ColumnEliminationMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ColumnEliminationMachine.Cost}, ColumnEliminationMachine.Trace j n s c t →
      ∃ k d, Trace a j k (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        k + d.total ≤ 4096 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha j head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Any finite source execution lowers to the exact represented endpoint. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a) (j : ℕ) (fuel : ℕ)
    (s : ColumnEliminationMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel a j k (enter (mapState encode s)) =
      (enter (mapState encode (ColumnEliminationMachine.runFuel j fuel s).1), d) ∧
      k + d.total ≤ 4096 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := ColumnEliminationMachine.runFuel_refines j fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha j ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Arbitrary materialized coordinate states reach the exact decoded source endpoint. -/
theorem decoded_run_lowering (a : F) (ha : ¬IsSquare a) (j : ℕ) (fuel : ℕ)
    (s : ColumnEliminationMachine.Configuration (Pair F)) :
    letI := fieldOfNonsquare a ha
    ∃ k d t, runFuel a j k (enter s) = (enter t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (ColumnEliminationMachine.runFuel j fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 4096 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨k, d, he, hb⟩ := run_lowering a ha j fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- Valid input preserves the pivot and every ordered target with an input-only work bound. -/
theorem column_correct (a : F) (ha : ¬IsSquare a) (j : ℕ)
    (pivot : List (QuadraticAlgebra F a 0)) (rows : List (List (QuadraticAlgebra F a 0)))
    (hj : j < pivot.length) :
    letI := fieldOfNonsquare a ha
    pivot[j] ≠ 0 → (∀ row ∈ rows, row.length = pivot.length) →
    ∃ k c output, runFuel a j k (.ready (.begin (mapRows encode (pivot :: rows)))) =
      (.ready (.done output), c) ∧
      output = mapRows encode (pivot :: rows.map (ColumnEliminationMachine.targetRow pivot j)) ∧
      output.length = rows.length + 1 ∧
      k + c.total ≤ 4096 * (rows.length * (4 * pivot.length + j + 11) + j + 6) := by
  let := fieldOfNonsquare a ha
  intro hp hlen
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha j
    (rows.length * (4 * pivot.length + j + 11) + j + 6) (.begin (pivot :: rows))
  rw [ColumnEliminationMachine.column_runFuel j pivot rows hj hp hlen] at hr
  exact ⟨k, c, _, hr, rfl, by simp [mapRows], hb⟩

end Matrix.QuadraticColumnMachine
