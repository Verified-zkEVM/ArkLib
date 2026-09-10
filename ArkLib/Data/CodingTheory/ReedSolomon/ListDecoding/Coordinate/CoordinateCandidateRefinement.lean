/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateCandidateMachine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticCandidateMachine
/-!
# Exact-cost raw-coordinate candidate refinement

Representation changes only the coefficient cells. Every source instruction is one actual
raw-coordinate instruction with the identical charge, including early rejection.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CoordinateCandidateMachine

open QuadraticAlgebra

/-- Proof-only coordinate encoding. -/
def encode {F : Type*} {a b : F} (x : QuadraticAlgebra F a b) : F × F := (x.re, x.im)

/-- Proof-only representation of the descent cursor. -/
def representDescent {F : Type*} {a b : F} :
    CoefficientDescentMachine.Configuration F a b → Descent.Configuration F
  | .start cs => .start (cs.map encode)
  | .scan cs out => .scan (cs.map encode) out
  | .reverse cs out => .reverse cs out
  | .emit out => .emit out
  | .done out => .done out

/-- The base-field filter state is already in the target representation. -/
def represent {F : Type*} {a b : F} :
    QuadraticCandidateMachine.Configuration F a b → Configuration F
  | .start cs => .start (cs.map encode)
  | .descent s => .descent (representDescent s)
  | .filter s => .filter s
  | .emit out => .emit out
  | .done out => .done out

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- Checked projection is exactly one base equality and the same cell operations. -/
theorem descent_step_lowering {s t : CoefficientDescentMachine.Configuration F a b}
    {c : ArithmeticMachine.Cost} (h : CoefficientDescentMachine.Step s c t) :
    Descent.step (representDescent s) = some (representDescent t, c) := by
  cases h with
  | accepted h => simp [representDescent, Descent.step, encode, h, Descent.charge]
  | rejected h => simp [representDescent, Descent.step, encode, h, Descent.charge]
  | _ => rfl

/-- Each source driver edge has exactly the same target cost. -/
theorem step_lowering {w k A : ℕ} {rows : List (F × F)}
    {s t : QuadraticCandidateMachine.Configuration F a b} {c : ℕ}
    (h : QuadraticCandidateMachine.Step w k A rows s c t) :
    step w k A rows (represent s) = some (represent t, c) := by
  cases h with
  | descent h => simp only [represent, step, descent_step_lowering h]
  | filter h => simp only [represent, step, h.step_eq]
  | _ => rfl

/-- Complete and partial traces preserve the exact instruction count and ledger. -/
theorem trace_lowering {w k A n : ℕ} {rows : List (F × F)}
    {s t : QuadraticCandidateMachine.Configuration F a b} {c : ℕ}
    (h : QuadraticCandidateMachine.Trace w k A rows n s c t) :
    Trace w k A rows n (represent s) c (represent t) := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (step_lowering head) ih

/-- Every source fuel prefix lowers to an actual prefix with the same result and cost. -/
theorem run_lowering (w k A fuel : ℕ) (rows : List (F × F))
    (s : QuadraticCandidateMachine.Configuration F a b) :
    ∃ n ≤ fuel, runFuel w k A rows n (represent s) =
      (represent (QuadraticCandidateMachine.runFuel w k A rows fuel s).1,
        (QuadraticCandidateMachine.runFuel w k A rows fuel s).2) := by
  obtain ⟨n, hn, ht⟩ := QuadraticCandidateMachine.runFuel_refines w k A fuel rows s
  exact ⟨n, hn, (trace_lowering ht).runFuel_eq⟩

/-- The final checked descent/filter answer comes from the same bounded actual run. -/
theorem computation_correct (a b : F) (w k A : ℕ) (xs : List (F × F))
    (rows : List (F × F)) (hwidth : xs.length = w) :
    ∃ n c, runFuel w k A rows n (.start xs) =
      (.done (QuadraticCandidateMachine.result w k A
        (xs.map (fun x ↦ (⟨x.1, x.2⟩ : QuadraticAlgebra F a b))) rows), c) ∧
      n ≤ QuadraticCandidateMachine.fuel w k rows.length ∧
      c ≤ QuadraticCandidateMachine.workBound w rows.length := by
  let ys := xs.map (fun x ↦ (⟨x.1, x.2⟩ : QuadraticAlgebra F a b))
  have hw : ys.length = w := by simpa [ys] using hwidth
  obtain ⟨c, hc, hb⟩ := QuadraticCandidateMachine.evaluation_runFuel w k A ys rows hw
  obtain ⟨n, hn, ht⟩ := run_lowering w k A
    (QuadraticCandidateMachine.fuel w k rows.length) rows (.start ys)
  rw [hc] at ht
  refine ⟨n, c, ?_, hn, hb⟩
  simpa [represent, ys, List.map_map, encode, Function.comp_def] using ht

end ReedSolomon.ListDecoding.CoordinateCandidateMachine
