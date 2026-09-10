/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateOutputMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputMachine
/-!
# Same-execution coordinate output collection

Every source collection edge lowers to actual coordinate acceptance or a bounded list-cell
operation. The represented endpoint preserves accepted order, multiplicity and all early exits.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticCanonicalOutputMachine

open QuadraticAlgebra
open HiddenDerivative

local notation "enc" => CoordinateCandidateMachine.encode

/-- Proof-only stage representation preserves its chosen derivative indices. -/
def mapStage {K J : Type*} (f : K → J) (s : StageRootsMachine.Stage K) :
    StageRootsMachine.Stage J :=
  ⟨QuadraticCanonicalGuardMachine.mapEquation f s.equation, s.selected⟩

/-- Proof-only representation retains the entire immutable context. -/
def mapContext {K J : Type*} (f : K → J) (c : StageRootsMachine.Context K) :
    StageRootsMachine.Context J :=
  ⟨mapStage f c.stage, QuadraticCanonicalGuardMachine.mapPrevious f c.previous,
    QuadraticCanonicalGuardMachine.mapEquation f c.separant⟩

/-- Proof-only record mapping; the interpreter never calls this function. -/
def mapRecord {K J : Type*} (f : K → J) (r : Record K) : Record J :=
  ⟨mapContext f r.context, f r.center, r.coefficients.map f⟩

/-- Preserve enumeration order and repeated records. -/
def mapRecords {K J : Type*} (f : K → J) (rs : List (Record K)) : List (Record J) :=
  rs.map (mapRecord f)

/-- Represent the actual retained payload built at the original record launch. -/
def represent {F : Type*} [CommSemiring F] (a : F) (order : ℕ)
    (samples : List (QuadraticAlgebra F a 0)) (_w _k _A : ℕ) (_rows : List (F × F)) :
    CanonicalOutputMachine.Configuration F a 0 → Configuration F
  | .start rs => .start (mapRecords enc rs)
  | .scan rs out => .scan (mapRecords enc rs) out
  | .accept r rs out s => .accept (mapRecord enc r) (mapRecords enc rs) out
      (QuadraticCanonicalGuardMachine.mapInput enc
        (CanonicalOutputMachine.guardInput order samples r))
      (QuadraticCanonicalAcceptanceMachine.represent a
        (CanonicalOutputMachine.guardInput order samples r) s)
  | .save cs rs out => .save cs (mapRecords enc rs) out
  | .reverse rs out => .reverse rs out
  | .emit out => .emit out
  | .done out => .done out

variable {F : Type*} [Field F] [DecidableEq F]

/-- Each acceptance instruction retains its payload and pays the collector dispatch. -/
theorem accept_trace {a : F} {order w k A n : ℕ} {samples : List (F × F)}
    {rows : List (F × F)} (r : Record (F × F)) (rs : List (Record (F × F)))
    (out : List (List F)) {payload : QuadraticCanonicalGuardMachine.Input F}
    {s t : Accept.Configuration F} {c : ℕ}
    (h : QuadraticCanonicalAcceptanceMachine.Trace a payload w k A rows n s c t) :
    Trace a order samples w k A rows n (.accept r rs out payload s) (c + 3 * n)
      (.accept r rs out payload t) := by
  induction h with
  | nil => exact .nil _
  | @cons n s u t c d head tail ih =>
      convert Trace.cons (s := .accept r rs out payload s) (c := c + 3)
        (by simp only [step, head]) ih using 1
      omega

/-- Every source edge lowers to bounded actual work, with no callback cost hypotheses. -/
theorem step_lowering {a : F} {order w k A : ℕ}
    {samples : List (QuadraticAlgebra F a 0)} {rows : List (F × F)}
    {s t : CanonicalOutputMachine.Configuration F a 0} {c : ℕ}
    (h : CanonicalOutputMachine.Step order samples w k A rows s c t) :
    ∃ n d, Trace a order (samples.map enc) w k A rows n
      (represent a order samples w k A rows s) d (represent a order samples w k A rows t) ∧
      n + d ≤ 2097152 * (1 + c) := by
  cases h with
  | @accept r rs out s t c h =>
      obtain ⟨n, d, hd, hb⟩ := QuadraticCanonicalAcceptanceMachine.step_lowering h
      exact ⟨n, d + 3 * n, accept_trace _ _ _ hd, by omega⟩
  | start => exact ⟨1, 4, .cons rfl (.nil _), by decide⟩
  | next => exact ⟨1, 17, .cons rfl (.nil _), by decide⟩
  | rejected => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩
  | accepted => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩
  | save => exact ⟨1, 4, .cons rfl (.nil _), by decide⟩
  | scanned => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩
  | reverse => exact ⟨1, 6, .cons rfl (.nil _), by decide⟩
  | reversed => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩
  | emit => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩

/-- A single factor bounds the complete source trace's instruction count and scalar work. -/
theorem trace_lowering {a : F} {order w k A n : ℕ}
    {samples : List (QuadraticAlgebra F a 0)} {rows : List (F × F)}
    {s t : CanonicalOutputMachine.Configuration F a 0} {c : ℕ}
    (h : CanonicalOutputMachine.Trace order samples w k A rows n s c t) :
    ∃ m d, Trace a order (samples.map enc) w k A rows m
      (represent a order samples w k A rows s) d (represent a order samples w k A rows t) ∧
      m + d ≤ 2097152 * (n + c) := by
  induction h with
  | nil => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      exact ⟨n + m, c + d, hc.trans hd, by omega⟩

/-- Every source fuel prefix has an actual target run with the same represented endpoint. -/
theorem run_lowering (a : F) (order : ℕ) (samples : List (QuadraticAlgebra F a 0))
    (w k A fuel : ℕ) (rows : List (F × F)) (s : CanonicalOutputMachine.Configuration F a 0) :
    ∃ n d, runFuel a order (samples.map enc) w k A rows n
      (represent a order samples w k A rows s) =
      (represent a order samples w k A rows
        (CanonicalOutputMachine.runFuel order samples w k A rows fuel s).1, d) ∧
      n + d ≤ 2097152 *
        (fuel + (CanonicalOutputMachine.runFuel order samples w k A rows fuel s).2) := by
  obtain ⟨m, hm, ht⟩ := CanonicalOutputMachine.runFuel_refines order w k A fuel samples rows s
  obtain ⟨n, d, hd, hb⟩ := trace_lowering ht
  exact ⟨n, d, hd.runFuel_eq, by omega⟩

omit [DecidableEq F] in
/-- Raw records survive proof-side decoding and encoding with all contexts intact. -/
theorem encode_decode_record (a : F) (r : Record (F × F)) :
    mapRecord enc (mapRecord (ArithmeticMachine.decode a) r) = r := by
  rcases r with ⟨⟨⟨equation, selected⟩, previous, separant⟩, center, coefficients⟩
  simp [mapRecord, mapContext, mapStage, QuadraticCanonicalGuardMachine.mapEquation,
    QuadraticCanonicalGuardMachine.mapPrevious, List.map_map, Function.comp_def,
    CoordinateCandidateMachine.encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- The full ordered record stream also survives the proof-only round trip. -/
theorem encode_decode_records (a : F) (rs : List (Record (F × F))) :
    mapRecords enc (mapRecords (ArithmeticMachine.decode a) rs) = rs := by
  simp [mapRecords, List.map_map, Function.comp_def, encode_decode_record]

/-- The actual collector returns the exact ordered source answer under the same-run bound. -/
theorem computation_correct (a : F) (order : ℕ) (samples : List (F × F)) (w k A : ℕ)
    (rows : List (F × F)) (rs : List (Record (F × F)))
    (hwidth : ∀ r ∈ rs, r.coefficients.length = w) :
    let sourceSamples := samples.map (ArithmeticMachine.decode a)
    let sourceRecords := mapRecords (ArithmeticMachine.decode a) rs
    ∃ n c, runFuel a order samples w k A rows n (.start rs) =
      (.done (CanonicalOutputMachine.result order sourceSamples w k A rows sourceRecords), c) ∧
      n + c ≤ 2097152 *
        (CanonicalOutputMachine.fuel order sourceSamples w k rows.length sourceRecords +
          CanonicalOutputMachine.workBound order sourceSamples w k rows.length sourceRecords) := by
  dsimp only
  let ss := samples.map (ArithmeticMachine.decode a)
  let sr := mapRecords (ArithmeticMachine.decode a) rs
  have hw : ∀ r ∈ sr, r.coefficients.length = w := by
    intro r hr
    change r ∈ rs.map (mapRecord (ArithmeticMachine.decode a)) at hr
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp hr
    rw [← heq]
    simpa [mapRecord] using hwidth original horiginal
  obtain ⟨c, hc, hb⟩ := CanonicalOutputMachine.evaluation_runFuel order w k A ss rows sr hw
  obtain ⟨n, d, hd, he⟩ := run_lowering a order ss w k A
    (CanonicalOutputMachine.fuel order ss w k rows.length sr) rows (.start sr)
  rw [hc] at hd he
  have hs : ss.map enc = samples := by
    simp [ss, List.map_map, Function.comp_def,
      CoordinateCandidateMachine.encode, ArithmeticMachine.decode]
  have hr : mapRecords enc sr = rs := encode_decode_records a rs
  rw [hs] at hd
  refine ⟨n, d, by simpa only [represent, hr] using hd, ?_⟩
  change n + d ≤ 2097152 * (CanonicalOutputMachine.fuel order ss w k rows.length sr +
    CanonicalOutputMachine.workBound order ss w k rows.length sr)
  dsimp only at he
  omega

end ReedSolomon.ListDecoding.QuadraticCanonicalOutputMachine
