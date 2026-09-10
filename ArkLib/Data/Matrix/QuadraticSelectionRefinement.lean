/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticSelectionMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Same-execution coordinate pivot-selection refinement

Proof-only maps preserve complete augmented rows, saved prefixes and optional pivots. Actual
source steps lower to retained equality instructions and list transitions. Successful and
all-zero outcomes preserve the original first-pivot and row-order semantics. Equality requires
no nonsquare parameter; input-only bounds count all lowered primitive work.
-/

@[expose] public section

namespace Matrix.QuadraticSelectionMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only representation of one augmented row. -/
def mapRow {K J : Type*} (f : K → J) (r : PivotSelectionMachine.Row K) :
    PivotSelectionMachine.Row J := (r.1.map f, f r.2)

/-- Proof-only representation preserves row order and multiplicity. -/
def mapRows {K J : Type*} (f : K → J) (rows : List (PivotSelectionMachine.Row K)) :
    List (PivotSelectionMachine.Row J) := rows.map (mapRow f)

/-- Every source selection phase has the pointwise coordinate representation. -/
def mapState {K J : Type*} (f : K → J) :
    PivotSelectionMachine.Configuration K → PivotSelectionMachine.Configuration J
  | .scan rows saved => .scan (mapRows f rows) (mapRows f saved)
  | .lookup r rows saved xs i =>
      .lookup (mapRow f r) (mapRows f rows) (mapRows f saved) (xs.map f) i
  | .check r rows saved x => .check (mapRow f r) (mapRows f rows) (mapRows f saved) (f x)
  | .restore p saved out => .restore (p.map (mapRow f)) (mapRows f saved) (mapRows f out)
  | .emit b rows => .emit b (mapRows f rows)
  | .done b rows => .done b (mapRows f rows)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding recovers the represented source state. -/
theorem decode_encode_state (a : F)
    (s : PivotSelectionMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapRows, mapRow, List.map_map, Option.map_map,
    Function.comp_def, encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Every raw coordinate state has the canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : PivotSelectionMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapRows, mapRow, List.map_map, Option.map_map,
    Function.comp_def, encode, ArithmeticMachine.decode]

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
    (r : Row F) (rows saved : List (Row F))
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a j n (.checking r rows saved payload s) d (.checking r rows saved payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a j (.checking r rows saved payload s) =
          some (.checking r rows saved payload u, delegated c) := by simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- Actual equality selects the same branch and charges zero literals and allocations. -/
theorem check_lowering (a : F) (j : ℕ) (r : Row F) (rows saved : List (Row F))
    (x : Pair F) (b : Bool)
    (hb : ArithmeticMachine.specification ⟨a, x, (0, 0)⟩ .equal = .boolean b) :
    ∃ n c, Trace a j n (.ready (.check r rows saved x)) c (checked r rows saved b).1 ∧
      n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace ⟨a, x, (0, 0)⟩ .equal
  rw [hb] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (j := j) r rows saved ht
  have hr : (checked r rows saved b).2.total ≤ 11 := by cases b <;> dsimp [checked] <;> decide
  refine ⟨n + 1 + 1, (launch + zeroSeed) + (c + (checked r rows saved b).2),
    .cons rfl (hc.trans (single rfl)), ?_⟩
  have hm := ArithmeticMachine.cost_total_le .equal
  simp only [total_add]
  rw [he]
  change n + 1 + 1 + (11 + ((ArithmeticMachine.cost .equal).total + 3 * n + _)) ≤ 256
  omega

/-- Each actual source step has the identical represented successor and bounded base work. -/
theorem step_lowering {a : F} {j : ℕ}
    {s t : PivotSelectionMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : PivotSelectionMachine.Cost} (h : PivotSelectionMachine.Step j s c t) :
    ∃ n d, Trace a j n (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
      n + d.total ≤ 256 := by
  cases h with
  | take => exact ⟨1, administrative PivotSelectionMachine.takeCost, single rfl, by decide⟩
  | exhausted =>
      exact ⟨1, administrative PivotSelectionMachine.exhaustedCost, single rfl, by decide⟩
  | seek => exact ⟨1, administrative PivotSelectionMachine.seekCost, single rfl, by decide⟩
  | hit => exact ⟨1, administrative PivotSelectionMachine.hitCost, single rfl, by decide⟩
  | missing => exact ⟨1, administrative PivotSelectionMachine.rejectCost, single rfl, by decide⟩
  | zero =>
      exact check_lowering a j _ _ _ (encode 0) true
        (by simp [ArithmeticMachine.specification, encode])
  | @found r rows saved x hx =>
      have hz : ¬(x.re = 0 ∧ x.im = 0) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      apply check_lowering a j _ _ _ (encode x) false
      by_cases hr : x.re = 0
      · have hi : x.im ≠ 0 := fun hi => hz ⟨hr, hi⟩
        simp [ArithmeticMachine.specification, encode, hr, hi]
      · simp [ArithmeticMachine.specification, encode, hr]
  | reverse =>
      exact ⟨1, administrative PivotSelectionMachine.reverseCost + allocation,
        single rfl, by decide⟩
  | finish => exact ⟨1, administrative PivotSelectionMachine.finishCost, single rfl, by decide⟩
  | assemble =>
      exact ⟨1, administrative PivotSelectionMachine.assembleCost + allocation,
        single rfl, by decide⟩
  | emit => exact ⟨1, administrative PivotSelectionMachine.emitCost, single rfl, by decide⟩

/-- Composition retains all actual equality and list work. -/
theorem trace_lowering {a : F} {j n : ℕ}
    {s t : PivotSelectionMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : PivotSelectionMachine.Cost} (h : PivotSelectionMachine.Trace j n s c t) :
    ∃ k d, Trace a j k (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
      k + d.total ≤ 256 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Any finite source run lowers to its exact represented endpoint. -/
theorem run_lowering (a : F) (j fuel : ℕ)
    (s : PivotSelectionMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a j k (.ready (mapState encode s)) =
      (.ready (mapState encode (PivotSelectionMachine.runFuel j fuel s).1), d) ∧
      k + d.total ≤ 256 * fuel := by
  obtain ⟨n, hn, ht⟩ := PivotSelectionMachine.runFuel_refines j fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Raw coordinate states execute to the same decoded source endpoint, including partial states. -/
theorem decoded_run_lowering (a : F) (j fuel : ℕ)
    (s : PivotSelectionMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a j k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (PivotSelectionMachine.runFuel j fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 256 * fuel := by
  obtain ⟨k, d, he, hb⟩ := run_lowering a j fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- The first nonzero row moves to the head; skipped rows and the untouched tail keep order. -/
theorem found_correct (a : F) (j : ℕ)
    (zs : List (PivotSelectionMachine.Row (QuadraticAlgebra F a 0)))
    (p : PivotSelectionMachine.Row (QuadraticAlgebra F a 0))
    (tail : List (PivotSelectionMachine.Row (QuadraticAlgebra F a 0))) (x : QuadraticAlgebra F a 0)
    (hz : ∀ r ∈ zs, r.1[j]? = some 0) (hp : p.1[j]? = some x) (hx : x ≠ 0) :
    ∃ k c, runFuel a j k (.ready (.scan (mapRows encode (zs ++ p :: tail)) [])) =
      (.ready (.done true (mapRows encode (p :: (zs ++ tail)))), c) ∧
      k + c.total ≤ 256 * (zs.length * (j + 4) + j + 5) := by
  obtain ⟨k, c, hr, hb⟩ := run_lowering a j (zs.length * (j + 4) + j + 5)
    (.scan (zs ++ p :: tail) [])
  rw [PivotSelectionMachine.found_runFuel j zs p tail x hz hp hx] at hr
  exact ⟨k, c, hr, hb⟩

/-- Valid all-zero columns restore the complete original materialized row sequence. -/
theorem allZero_correct (a : F) (j : ℕ)
    (rows : List (PivotSelectionMachine.Row (QuadraticAlgebra F a 0)))
    (hz : ∀ r ∈ rows, r.1[j]? = some 0) :
    ∃ k c, runFuel a j k (.ready (.scan (mapRows encode rows) [])) =
      (.ready (.done false (mapRows encode rows)), c) ∧
      k + c.total ≤ 256 * (rows.length * (j + 4) + 3) := by
  obtain ⟨k, c, hr, hb⟩ := run_lowering a j (rows.length * (j + 4) + 3) (.scan rows [])
  rw [PivotSelectionMachine.allZero_runFuel j rows hz] at hr
  exact ⟨k, c, hr, hb⟩

/-- A valid column returns the source certificate, preserves row count and has an input bound. -/
theorem selection_correct (a : F) (j : ℕ)
    (rows : List (PivotSelectionMachine.Row (QuadraticAlgebra F a 0)))
    (hv : ∀ r ∈ rows, ∃ x, r.1[j]? = some x) :
    ∃ k c b output, runFuel a j k (.ready (.scan (mapRows encode rows) [])) =
      (.ready (.done b output), c) ∧
      PivotSelectionMachine.ResultCorrect j rows b (mapRows (ArithmeticMachine.decode a) output) ∧
      output.length = rows.length ∧ k + c.total ≤ 256 * (rows.length * (j + 4) + 3) := by
  obtain ⟨b, out, sourceCost, hs, hc, _⟩ := PivotSelectionMachine.selection_runFuel j rows hv
  obtain ⟨k, c, hr, hb⟩ := run_lowering a j (PivotSelectionMachine.selectionFuel j rows.length)
    (.scan rows [])
  rw [hs] at hr
  have hround : mapRows (ArithmeticMachine.decode a) (mapRows encode out) = out := by
    simp [mapRows, mapRow, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨k, c, b, mapRows encode out, hr, ?_, ?_, hb⟩
  · simpa only [hround] using hc
  · simpa [mapRows] using hc.1.length_eq.symm

end Matrix.QuadraticSelectionMachine
