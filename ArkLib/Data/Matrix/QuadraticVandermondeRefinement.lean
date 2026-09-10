/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticVandermondeMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Same-execution coordinate Vandermonde refinement

The maps are proof-only relations on materialized points, rows and states. Every original step
has a concrete lowered trace, including its final unused multiplication. The construction theorem
preserves row/column order, duplicates, physical row count and width, with a base-operation bound.
-/

@[expose] public section

namespace Matrix.QuadraticVandermondeMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only representation of point/value samples. -/
def mapSamples {K J : Type*} (f : K → J) (ss : List (K × K)) : List (J × J) :=
  ss.map (fun s => (f s.1, f s.2))

/-- Proof-only representation of materialized augmented rows. -/
def mapRows {K J : Type*} (f : K → J) (rs : List (VandermondeMachine.Row K)) :
    List (VandermondeMachine.Row J) := rs.map (fun r => (r.1.map f, f r.2))

/-- Pointwise representation preserves all source counters and control phases. -/
def mapState {K J : Type*} (f : K → J) :
    VandermondeMachine.Configuration K → VandermondeMachine.Configuration J
  | .start ss => .start (mapSamples f ss)
  | .scan ss rows => .scan (mapSamples f ss) (mapRows f rows)
  | .power x y ss rows n p cs =>
      .power (f x) (f y) (mapSamples f ss) (mapRows f rows) n (f p) (cs.map f)
  | .multiply x y ss rows n p cs =>
      .multiply (f x) (f y) (mapSamples f ss) (mapRows f rows) n (f p) (cs.map f)
  | .reverseRow y ss rows cs out =>
      .reverseRow (f y) (mapSamples f ss) (mapRows f rows) (cs.map f) (out.map f)
  | .pack y ss rows cs => .pack (f y) (mapSamples f ss) (mapRows f rows) (cs.map f)
  | .save row ss rows => .save (row.1.map f, f row.2) (mapSamples f ss) (mapRows f rows)
  | .reverseRows rs out => .reverseRows (mapRows f rs) (mapRows f out)
  | .emit rows => .emit (mapRows f rows)
  | .done rows => .done (mapRows f rows)

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding an encoded source state recovers that exact source state. -/
theorem decode_encode_state (a : F) (s : VandermondeMachine.Configuration
    (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapRows, mapSamples, List.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Every materialized coordinate state has the canonical pointwise representation. -/
theorem encode_decode_state (a : F) (s : VandermondeMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapRows, mapSamples, List.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Every actual base instruction retains its own ledger and the parent-state wrapper. -/
theorem arithmetic_trace {a : F} {L : ℕ} (frame : Frame F)
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a L n (.call frame payload s) d (.call frame payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a L (.call frame payload s) =
          some (.call frame payload u, delegated c) := by simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- The selected literal program returns its actual materialized pair to the saved power loop. -/
theorem call_returns (a : F) (L : ℕ) (frame : Frame F) (payload : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (p : Pair F)
    (hp : ArithmeticMachine.specification payload op = .pair p) :
    ∃ n c, Trace a L n (.call frame payload (.start op)) c (resume frame p) ∧
      n + c.total ≤ 189 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace payload op
  rw [hp] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (L := L) frame ht
  refine ⟨n + 1, c + returned, hc.trans (single rfl), ?_⟩
  have hb := ArithmeticMachine.cost_total_le op
  rw [total_add, he]
  change n + 1 + ((ArithmeticMachine.cost op).total + 3 * n + 4) ≤ 189
  omega

/-- Every source multiplication executes the base program, even for the unused final power. -/
theorem multiply_lowering (a : F) (L : ℕ) (x y p : QuadraticAlgebra F a 0)
    (ss : List (Sample F)) (rows : List (Row F)) (n : ℕ) (cs : List (Pair F)) :
    ∃ k c, Trace a L k (.ready (.multiply (encode x) (encode y) ss rows n (encode p) cs)) c
      (.ready (.power (encode x) (encode y) ss rows n (encode (p * x)) cs)) ∧
      k + c.total ≤ 256 := by
  have hm : ArithmeticMachine.specification ⟨a, encode p, encode x⟩ .mul =
      .pair (encode (p * x)) := by rw [← mulCoordinates_eq a p x]; rfl
  obtain ⟨k, c, hc, hb⟩ := call_returns a L ⟨encode x, encode y, ss, rows, n, cs⟩
    ⟨a, encode p, encode x⟩ .mul (encode (p * x)) hm
  refine ⟨k + 1, (administrative VandermondeMachine.multiplyCost + launch) + c, .cons rfl hc, ?_⟩
  rw [total_add]
  change k + 1 + (11 + c.total) ≤ 256
  omega

/-- Source-step simulation preserves all materialized registers and pays all actual work. -/
theorem step_lowering {a : F} {L : ℕ}
    {s t : VandermondeMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : VandermondeMachine.Cost} (h : VandermondeMachine.Step L s c t) :
    ∃ n d, Trace a L n (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
      n + d.total ≤ 256 := by
  cases h with
  | start => exact ⟨1, administrative VandermondeMachine.startCost, single rfl, by decide⟩
  | take => exact ⟨1, administrative VandermondeMachine.takeCost + seedCost, single rfl, by decide⟩
  | coefficient =>
      exact ⟨1, administrative VandermondeMachine.coefficientCost, single rfl, by decide⟩
  | multiply => exact multiply_lowering _ _ _ _ _ _ _ _ _
  | powerFinish =>
      exact ⟨1, administrative VandermondeMachine.powerFinishCost, single rfl, by decide⟩
  | reverseRow => exact ⟨1, administrative VandermondeMachine.reverseCost, single rfl, by decide⟩
  | rowFinish => exact ⟨1, administrative VandermondeMachine.rowFinishCost, single rfl, by decide⟩
  | pack => exact ⟨1, administrative VandermondeMachine.packCost, single rfl, by decide⟩
  | save => exact ⟨1, administrative VandermondeMachine.saveCost + saveRoot, single rfl, by decide⟩
  | outerFinish =>
      exact ⟨1, administrative VandermondeMachine.outerFinishCost, single rfl, by decide⟩
  | reverseRows => exact ⟨1, administrative VandermondeMachine.reverseCost, single rfl, by decide⟩
  | finish => exact ⟨1, administrative VandermondeMachine.finishCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative VandermondeMachine.emitCost, single rfl, by decide⟩

/-- Actual source traces compose into actual base-instruction traces. -/
theorem trace_lowering {a : F} {L n : ℕ}
    {s t : VandermondeMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : VandermondeMachine.Cost} (h : VandermondeMachine.Trace L n s c t) :
    ∃ k d, Trace a L k (.ready (mapState encode s)) d (.ready (mapState encode t)) ∧
      k + d.total ≤ 256 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Arbitrary source execution lowers to the same represented endpoint. -/
theorem run_lowering (a : F) (L fuel : ℕ)
    (s : VandermondeMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a L k (.ready (mapState encode s)) =
      (.ready (mapState encode (VandermondeMachine.runFuel L fuel s).1), d) ∧
      k + d.total ≤ 256 * fuel := by
  obtain ⟨n, hn, ht⟩ := VandermondeMachine.runFuel_refines L fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Arbitrary coordinate states execute to the exact decoded source endpoint. -/
theorem decoded_run_lowering (a : F) (L fuel : ℕ)
    (s : VandermondeMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a L k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (VandermondeMachine.runFuel L fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 256 * fuel := by
  obtain ⟨k, d, he, hb⟩ := run_lowering a L fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- Concrete coordinate construction preserves ordered augmented rows and bounds all base work. -/
theorem construction_correct (a : F) (L : ℕ) (samples : List (Sample F)) :
    ∃ k c rows, runFuel a L k (.ready (.start samples)) = (.ready (.done rows), c) ∧
      mapRows (ArithmeticMachine.decode a) rows =
        VandermondeMachine.rowsSpec L (mapSamples (ArithmeticMachine.decode a) samples) ∧
      rows.length = samples.length ∧ (∀ row ∈ rows, row.1.length = L) ∧
      k + c.total ≤ 1536 * (samples.length + 1) * (L + 1) := by
  let ss := mapSamples (ArithmeticMachine.decode a) samples
  obtain ⟨sourceCost, hs, _⟩ := VandermondeMachine.construction_runFuel L ss
  obtain ⟨k, c, he, hb⟩ :=
    run_lowering a L (VandermondeMachine.constructionFuel L ss.length) (.start ss)
  rw [hs] at he
  have hss : mapSamples encode ss = samples := by
    simp [ss, mapSamples, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [mapState, hss] at he
  refine ⟨k, c, mapRows encode (VandermondeMachine.rowsSpec L ss), he, ?_, ?_, ?_, ?_⟩
  · simp [mapRows, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode, ss]
  · simp [mapRows, VandermondeMachine.rowsSpec_length, ss, mapSamples]
  · intro row hr
    change row ∈ (VandermondeMachine.rowsSpec L ss).map _ at hr
    obtain ⟨r, hmem, hrow⟩ := List.mem_map.mp hr
    rw [← hrow]
    simpa using VandermondeMachine.rowsSpec_rectangular L ss r hmem
  · have hf : VandermondeMachine.constructionFuel L ss.length ≤
        6 * (samples.length + 1) * (L + 1) := by
      simp only [VandermondeMachine.constructionFuel, ss, mapSamples, List.length_map]
      nlinarith
    calc
      k + c.total ≤ 256 * VandermondeMachine.constructionFuel L ss.length := hb
      _ ≤ 256 * (6 * (samples.length + 1) * (L + 1)) := Nat.mul_le_mul_left _ hf
      _ = 1536 * (samples.length + 1) * (L + 1) := by ring

end Matrix.QuadraticVandermondeMachine
