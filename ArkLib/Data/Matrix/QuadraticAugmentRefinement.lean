/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticAugmentMachine
public import ArkLib.Data.Matrix.QuadraticColumnRefinement

/-!
# Same-execution augmented coordinate refinement

Representation maps are proof-only. Every physical RHS/column alignment, serialization and
child step is preserved by an actual trace. Full execution retains ordered rows and physical
row count with a polynomial bound depending only on input dimensions and column index.
-/

@[expose] public section

namespace Matrix.QuadraticAugmentMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

/-- Proof-only mapping of augmented coefficient/RHS pairs. -/
def mapRows {K J : Type*} (f : K → J) (rs : List (AugmentedColumnMachine.Row K)) :
    List (AugmentedColumnMachine.Row J) := rs.map (fun r => (r.1.map f, f r.2))

/-- Representation preserves physical child index and every partial serialization phase. -/
def mapState {K J : Type*} (f : K → J) :
    AugmentedColumnMachine.Configuration K → AugmentedColumnMachine.Configuration J
  | .pack rs rev => .pack (mapRows f rs) (QuadraticColumnMachine.mapRows f rev)
  | .reversePacked rs out =>
      .reversePacked (QuadraticColumnMachine.mapRows f rs) (QuadraticColumnMachine.mapRows f out)
  | .column i s => .column i (QuadraticColumnMachine.mapState f s)
  | .unpack rs rev => .unpack (QuadraticColumnMachine.mapRows f rs) (mapRows f rev)
  | .reverseRows rs out => .reverseRows (mapRows f rs) (mapRows f out)
  | .done rs => .done (mapRows f rs)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding recovers each represented augmented source state. -/
theorem decode_encode_state (a : F)
    (s : AugmentedColumnMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapRows, QuadraticColumnMachine.mapRows, List.map_map,
    Function.comp_def, encode, ArithmeticMachine.decode, QuadraticColumnMachine.decode_encode_state]

omit [DecidableEq F] in
/-- Every raw augmented state has a canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : AugmentedColumnMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapRows, QuadraticColumnMachine.mapRows, List.map_map,
    Function.comp_def, encode, ArithmeticMachine.decode, QuadraticColumnMachine.encode_decode_state]

/-- Each actual column-child transition retains all callee work and adds its wrapper. -/
theorem column_trace {a : F} {j i n : ℕ}
    {s t : QuadraticColumnMachine.Configuration F} {c : Cost}
    (h : QuadraticColumnMachine.Trace a i n s c t) :
    ∃ d, Trace a j n (.column i s) d (.column i t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Each source step lowers to actual serialization or column-child work with the same result. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a) (j : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : AugmentedColumnMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : AugmentedColumnMachine.Cost}, AugmentedColumnMachine.Step j s c t →
      ∃ n d, Trace a j n (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        n + d.total ≤ 16384 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | pack =>
      exact ⟨1, administrative AugmentedColumnMachine.packCost + allocation 2,
        single rfl, by decide⟩
  | packEnd => exact ⟨1, administrative AugmentedColumnMachine.endCost, single rfl, by decide⟩
  | reversePacked =>
      exact ⟨1, administrative AugmentedColumnMachine.reverseCost + allocation 1,
        single rfl, by decide⟩
  | enter => exact ⟨1, administrative AugmentedColumnMachine.enterCost, single rfl, by decide⟩
  | column h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticColumnMachine.step_lowering a ha _ h
      obtain ⟨d, hd, he⟩ := column_trace (j := j) hc
      exact ⟨n, d, hd, by omega⟩
  | returned => exact ⟨1, administrative AugmentedColumnMachine.returnCost, single rfl, by decide⟩
  | failed => exact ⟨1, administrative AugmentedColumnMachine.rejectCost, single rfl, by decide⟩
  | unpack =>
      exact ⟨1, administrative AugmentedColumnMachine.unpackCost + allocation 3,
        single rfl, by decide⟩
  | malformed => exact ⟨1, administrative AugmentedColumnMachine.rejectCost, single rfl, by decide⟩
  | unpackEnd => exact ⟨1, administrative AugmentedColumnMachine.endCost, single rfl, by decide⟩
  | reverseRows =>
      exact ⟨1, administrative AugmentedColumnMachine.reverseCost + allocation 1,
        single rfl, by decide⟩
  | emit => exact ⟨1, administrative AugmentedColumnMachine.emitCost, single rfl, by decide⟩

/-- Same-endpoint traces compose without omitting row or arithmetic child work. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a) (j : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : AugmentedColumnMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : AugmentedColumnMachine.Cost}, AugmentedColumnMachine.Trace j n s c t →
      ∃ k d, Trace a j k (enter (mapState encode s)) d (enter (mapState encode t)) ∧
        k + d.total ≤ 16384 * n := by
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
    (s : AugmentedColumnMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel a j k (enter (mapState encode s)) =
      (enter (mapState encode (AugmentedColumnMachine.runFuel j fuel s).1), d) ∧
      k + d.total ≤ 16384 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := AugmentedColumnMachine.runFuel_refines j fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha j ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Arbitrary materialized coordinate states reach the exact decoded source endpoint. -/
theorem decoded_run_lowering (a : F) (ha : ¬IsSquare a) (j : ℕ) (fuel : ℕ)
    (s : AugmentedColumnMachine.Configuration (Pair F)) :
    letI := fieldOfNonsquare a ha
    ∃ k d t, runFuel a j k (enter s) = (enter t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (AugmentedColumnMachine.runFuel j fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 16384 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨k, d, he, hb⟩ := run_lowering a ha j fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- Ordered augmented output and its row count have an input-only polynomial work bound. -/
theorem evaluation_correct (a : F) (ha : ¬IsSquare a) (j : ℕ)
    (p : AugmentedColumnMachine.Row (QuadraticAlgebra F a 0))
    (rows : List (AugmentedColumnMachine.Row (QuadraticAlgebra F a 0))) (hj : j < p.1.length) :
    letI := fieldOfNonsquare a ha
    p.1[j] ≠ 0 → (∀ r ∈ rows, r.1.length = p.1.length) →
    ∃ k c output, runFuel a j k (.ready (.pack (mapRows encode (p :: rows)) [])) =
      (.ready (.done output), c) ∧
      output = mapRows encode (p :: rows.map (AugmentedColumnMachine.transformRow p j)) ∧
      output.length = rows.length + 1 ∧
      k + c.total ≤ 16384 * (4 * (rows.length + 1) + 5 +
        (rows.length * (4 * (p.1.length + 1) + (j + 1) + 11) + (j + 1) + 6)) := by
  let := fieldOfNonsquare a ha
  intro hp hlen
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha j
    (AugmentedColumnMachine.fuel p.1.length rows.length j) (.pack (p :: rows) [])
  rw [AugmentedColumnMachine.evaluation_runFuel j p rows hj hp hlen] at hr
  exact ⟨k, c, _, hr, rfl, by simp [mapRows], hb⟩

end Matrix.QuadraticAugmentMachine
