/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticForwardEchelonMachine
public import ArkLib.Data.Matrix.QuadraticSelectionRefinement
public import ArkLib.Data.Matrix.QuadraticAugmentRefinement

/-!
# Same-execution coordinate forward-echelon refinement

Actual source steps and both child executions lower to identical represented endpoints with
all base work charged. Rectangular input yields the same ordered pivots, residual RHS rows and
solution set, with an input-only polynomial bound. Nonsquareness is used for the source field
and the inverse refinement inside augmented elimination; runtime dispatch takes no proof oracle.
-/

@[expose] public section

namespace Matrix.QuadraticForwardEchelonMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

abbrev mapRows {K J : Type*} (f : K → J) (rows : List (ForwardEchelonMachine.Row K)) :=
  QuadraticSelectionMachine.mapRows f rows

/-- Proof-only mapping retains logical pivot indices and full augmented rows. -/
def mapPivots {K J : Type*} (f : K → J) (ps : List (ForwardEchelonMachine.Pivot K)) :
    List (ForwardEchelonMachine.Pivot J) :=
  ps.map (fun p => (p.1, QuadraticSelectionMachine.mapRow f p.2))

/-- Pointwise representation preserves every driver counter and actual source child state. -/
def mapState {K J : Type*} (f : K → J) :
    ForwardEchelonMachine.Configuration K → ForwardEchelonMachine.Configuration J
  | .loop j left rows rev => .loop j left (mapRows f rows) (mapPivots f rev)
  | .select j left rev s =>
      .select j left (mapPivots f rev) (QuadraticSelectionMachine.mapState f s)
  | .eliminate j left rev s =>
      .eliminate j left (mapPivots f rev) (QuadraticAugmentMachine.mapState f s)
  | .reverse ps out rest => .reverse (mapPivots f ps) (mapPivots f out) (mapRows f rest)
  | .done ps rest => .done (mapPivots f ps) (mapRows f rest)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding recovers every represented driver and child state. -/
theorem decode_encode_state (a : F)
    (s : ForwardEchelonMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapPivots, mapRows, QuadraticSelectionMachine.mapRows,
    QuadraticSelectionMachine.mapRow, List.map_map, Function.comp_def, encode,
    ArithmeticMachine.decode, QuadraticSelectionMachine.decode_encode_state,
    QuadraticAugmentMachine.decode_encode_state]

omit [DecidableEq F] in
/-- Any materialized coordinate state has a canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : ForwardEchelonMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapPivots, mapRows, QuadraticSelectionMachine.mapRows,
    QuadraticSelectionMachine.mapRow, List.map_map, Function.comp_def, encode,
    ArithmeticMachine.decode, QuadraticSelectionMachine.encode_decode_state,
    QuadraticAugmentMachine.encode_decode_state]

/-- Each selection instruction retains its ledger and pays the driver wrapper. -/
theorem select_trace {a : F} {j left n : ℕ} (rev : List (Pivot F))
    {s t : QuadraticSelectionMachine.Configuration F} {c : Cost}
    (h : QuadraticSelectionMachine.Trace a j n s c t) :
    ∃ d, Trace a n (.select j left rev s) d (.select j left rev t) ∧
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

/-- Each augmented-column instruction retains its ledger and pays the driver wrapper. -/
theorem eliminate_trace {a : F} {j left n : ℕ} (rev : List (Pivot F))
    {s t : QuadraticAugmentMachine.Configuration F} {c : Cost}
    (h : QuadraticAugmentMachine.Trace a j n s c t) :
    ∃ d, Trace a n (.eliminate j left rev s) d (.eliminate j left rev t) ∧
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

/-- Each source driver step executes to the same represented result with actual child work. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : ForwardEchelonMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ForwardEchelonMachine.Cost}, ForwardEchelonMachine.Step s c t →
      ∃ n d, Trace a n (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        n + d.total ≤ 65536 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | select => exact ⟨1, administrative ForwardEchelonMachine.selectCost, single rfl, by decide⟩
  | finish => exact ⟨1, administrative ForwardEchelonMachine.finishCost, single rfl, by decide⟩
  | selection h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticSelectionMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := select_trace _ hc
      exact ⟨n, d, hd, by omega⟩
  | nohit => exact ⟨1, administrative ForwardEchelonMachine.nextCost, single rfl, by decide⟩
  | found => exact ⟨1, administrative ForwardEchelonMachine.eliminateCost, single rfl, by decide⟩
  | selectionEmpty =>
      exact ⟨1, administrative ForwardEchelonMachine.rejectCost, single rfl, by decide⟩
  | selectionFailed =>
      exact ⟨1, administrative ForwardEchelonMachine.rejectCost, single rfl, by decide⟩
  | elimination h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticAugmentMachine.step_lowering a ha _ h
      obtain ⟨d, hd, he⟩ := eliminate_trace _ hc
      exact ⟨n, d, hd, by omega⟩
  | store =>
      exact ⟨1, administrative ForwardEchelonMachine.storeCost + allocation 2,
        single rfl, by decide⟩
  | eliminationEmpty =>
      exact ⟨1, administrative ForwardEchelonMachine.rejectCost, single rfl, by decide⟩
  | eliminationFailed =>
      exact ⟨1, administrative ForwardEchelonMachine.rejectCost, single rfl, by decide⟩
  | reverse =>
      exact ⟨1, administrative ForwardEchelonMachine.reverseCost + allocation 1,
        single rfl, by decide⟩
  | emit => exact ⟨1, administrative ForwardEchelonMachine.emitCost, single rfl, by decide⟩

/-- Same-endpoint traces compose without omitting row or arithmetic child work. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : ForwardEchelonMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ForwardEchelonMachine.Cost}, ForwardEchelonMachine.Trace n s c t →
      ∃ k d, Trace a k (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        k + d.total ≤ 65536 * n := by
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
    (s : ForwardEchelonMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel a k (enter (mapState encode s)) =
      (enter (mapState encode (ForwardEchelonMachine.runFuel fuel s).1), d) ∧
      k + d.total ≤ 65536 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := ForwardEchelonMachine.runFuel_refines fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Arbitrary materialized coordinate states reach the exact decoded source endpoint. -/
theorem decoded_run_lowering (a : F) (ha : ¬IsSquare a) (fuel : ℕ)
    (s : ForwardEchelonMachine.Configuration (Pair F)) :
    letI := fieldOfNonsquare a ha
    ∃ k d t, runFuel a k (enter s) = (enter t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (ForwardEchelonMachine.runFuel fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 65536 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨k, d, he, hb⟩ := run_lowering a ha fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- Rectangular coordinate input executes to echelon data with identical RHS solutions and
row count; the polynomial bound depends only on input dimensions. -/
theorem evaluation_correct (a : F) (ha : ¬IsSquare a) (n : ℕ) (rows : List (Row F)) :
    letI := fieldOfNonsquare a ha
    ForwardEchelonMachine.Rectangular n (mapRows (ArithmeticMachine.decode a) rows) →
    ∃ k c ps rest, runFuel a k (.ready (.loop 0 n rows [])) = (.ready (.done ps rest), c) ∧
      ForwardEchelonMachine.Echelon n 0
        (mapPivots (ArithmeticMachine.decode a) ps) (mapRows (ArithmeticMachine.decode a) rest) ∧
      ps.length + rest.length = rows.length ∧
      (∀ x, ForwardEchelonMachine.Solutions (mapPivots (ArithmeticMachine.decode a) ps)
        (mapRows (ArithmeticMachine.decode a) rest) x ↔
          PivotSelectionMachine.Satisfies (mapRows (ArithmeticMachine.decode a) rows) x) ∧
      k + c.total ≤ 65536 * (n * (1000 * (rows.length + 1) * (n + 1)) + 7 * rows.length + 13) := by
  let := fieldOfNonsquare a ha
  intro hrect
  obtain ⟨ps, rest, sourceCost, hs, he, hcount, hsol, _⟩ :=
    ForwardEchelonMachine.evaluation_runFuel n (mapRows (ArithmeticMachine.decode a) rows) hrect
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha
    (ForwardEchelonMachine.budget (mapRows (ArithmeticMachine.decode a) rows).length n)
    (.loop 0 n (mapRows (ArithmeticMachine.decode a) rows) [])
  rw [hs] at hr
  have hrows : mapRows encode (mapRows (ArithmeticMachine.decode a) rows) = rows := by
    simp [mapRows, QuadraticSelectionMachine.mapRows, QuadraticSelectionMachine.mapRow,
      List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  have hps : mapPivots (ArithmeticMachine.decode a) (mapPivots encode ps) = ps := by
    simp [mapPivots, QuadraticSelectionMachine.mapRow, List.map_map,
      Function.comp_def, encode, ArithmeticMachine.decode]
  have hrest : mapRows (ArithmeticMachine.decode a) (mapRows encode rest) = rest := by
    simp [mapRows, QuadraticSelectionMachine.mapRows, QuadraticSelectionMachine.mapRow,
      List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [mapState, mapPivots, List.map_nil, hrows, enter] at hr
  refine ⟨k, c, mapPivots encode ps, mapRows encode rest, hr, ?_, ?_, ?_, ?_⟩
  · simpa only [hps, hrest] using he
  · simpa [mapPivots, mapRows, QuadraticSelectionMachine.mapRows] using hcount
  · simpa only [hps, hrest] using hsol
  · simpa [ForwardEchelonMachine.budget, ForwardEchelonMachine.stageBudget,
      mapRows, QuadraticSelectionMachine.mapRows] using hb

end Matrix.QuadraticForwardEchelonMachine
