/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.PreparationMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement
/-!
# Coordinate preparation refinement

Every source transition lowers to the same cursor, failure tag and output list. The constant
factor applies once to the complete source trace and includes coordinate zero construction.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticJetPreparationMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

/-- Pointwise representation preserves all capacities, cursors and tags. -/
def mapState {K J : Type*} (f : K → J) :
    JetPreparationMachine.Configuration K → JetPreparationMachine.Configuration J
  | .start D bs => .start D (bs.map f)
  | .scan n bs rev => .scan n (bs.map f) (rev.map f)
  | .pad n out => .pad n (out.map f)
  | .emit out => .emit (out.map (List.map f))
  | .done out => .done (out.map (List.map f))

variable {F : Type*} [Field F]

/-- Coordinate round trip for arbitrary materialized states. -/
theorem encode_decode_state (a : F) (s : Configuration F) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, List.map_map, Option.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

/-- Source round trip preserves the exact state. -/
theorem decode_encode_state (a : F)
    (s : JetPreparationMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, List.map_map, Option.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

/-- Each source edge is reproduced with both base zeros and every output allocation charged. -/
theorem step_lowering {a : F}
    {s t : JetPreparationMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : JetPreparationMachine.Cost} (h : JetPreparationMachine.Step s c t) :
    ∃ n d, Trace n (mapState encode s) d (mapState encode t) ∧ n + d.total ≤ 32 := by
  cases h with
  | start => exact ⟨1, administrative JetPreparationMachine.startCost, single rfl, by decide⟩
  | take => exact ⟨1, administrative JetPreparationMachine.takeCost, single rfl, by decide⟩
  | padStart => exact ⟨1, administrative JetPreparationMachine.padStartCost, single rfl, by decide⟩
  | reject => exact ⟨1, administrative JetPreparationMachine.rejectCost, single rfl, by decide⟩
  | pad => exact ⟨1, administrative JetPreparationMachine.padCost, single rfl, by decide⟩
  | padDone => exact ⟨1, administrative JetPreparationMachine.padDoneCost + allocation,
      single rfl, by decide⟩
  | emit => exact ⟨1, administrative JetPreparationMachine.emitCost, single rfl, by decide⟩

/-- The fixed factor applies to the entire source trace, independently of jet length. -/
theorem trace_lowering {a : F} {n : ℕ}
    {s t : JetPreparationMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : JetPreparationMachine.Cost} (h : JetPreparationMachine.Trace n s c t) :
    ∃ k d, Trace k (mapState encode s) d (mapState encode t) ∧ k + d.total ≤ 32 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- All finite source runs, including failure and partial cursors, lower exactly. -/
theorem run_lowering (a : F) (fuel : ℕ)
    (s : JetPreparationMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel k (mapState encode s) =
      (mapState encode (JetPreparationMachine.runFuel fuel s).1, d) ∧
      k + d.total ≤ 32 * fuel := by
  obtain ⟨n, hn, ht⟩ := JetPreparationMachine.runFuel_refines fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Raw coordinate runs have the exact decoded source endpoint, including rejection. -/
theorem decoded_run_lowering (a : F) (fuel : ℕ) (s : Configuration F) :
    ∃ k d t, runFuel k s = (t, d) ∧ mapState (ArithmeticMachine.decode a) t =
      (JetPreparationMachine.runFuel fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 32 * fuel := by
  obtain ⟨k, d, hr, hb⟩ := run_lowering a fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at hr
  exact ⟨k, d, _, hr, decode_encode_state a _, hb⟩

/-- Successful execution has the exact ascending-jet polynomial and requested physical width. -/
theorem preparation_correct (a : F) (D : ℕ) (bs : List (Pair F)) (h : bs.length ≤ D + 1) :
    ∃ k c out, runFuel k (.start D bs) = (.done (some out), c) ∧ out.length = D + 1 ∧
      Polynomial.JetHornerMachine.coefficientPolynomial (out.map (ArithmeticMachine.decode a)) =
        Polynomial.CoefficientList.ascendingPolynomial (bs.map (ArithmeticMachine.decode a)) ∧
      k + c.total ≤ 32 * (D + 5) := by
  obtain ⟨out, hs, hlen, hpoly, _⟩ := JetPreparationMachine.preparation_correct D
    (bs.map (ArithmeticMachine.decode a)) (by simpa using h)
  obtain ⟨k, c, hr, hb⟩ := run_lowering a (D + 5)
    (.start D (bs.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hbs : (bs.map (ArithmeticMachine.decode a)).map encode = bs := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  have hout : (out.map encode).map (ArithmeticMachine.decode a) = out := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [mapState, hbs, Option.map_some] at hr
  exact ⟨k, c, out.map encode, hr, by simpa using hlen, by simpa only [hout] using hpoly, hb⟩

/-- Overlong jets reject with the same tagged failure, never a truncated candidate. -/
theorem rejection_correct (a : F) (D : ℕ) (bs : List (Pair F)) (h : D + 1 < bs.length) :
    ∃ k c, runFuel k (.start D bs) = (.done none, c) ∧ k + c.total ≤ 32 * (D + 5) := by
  have hs := JetPreparationMachine.rejection_runFuel D
    (bs.map (ArithmeticMachine.decode a)) (by simpa using h)
  obtain ⟨k, c, hr, hb⟩ := run_lowering a (D + 5)
    (.start D (bs.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hbs : (bs.map (ArithmeticMachine.decode a)).map encode = bs := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  exact ⟨k, c, by simpa only [mapState, hbs, Option.map_none] using hr, hb⟩

end ReedSolomon.HiddenDerivative.QuadraticJetPreparationMachine
