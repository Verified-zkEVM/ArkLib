/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateHighestMachine
public import ArkLib.Data.MvPolynomial.CoordinateNormalizeRefinement

/-! # Same-execution highest-jet selection after coordinate normalization -/

@[expose] public section

namespace MvPolynomial.QuadraticHighestMachine

open QuadraticAlgebra
open QuadraticEvaluationMachine (Cost total_add encode)
open QuadraticNormalizeMachine (mapTerms)

/-- Preserve normalization and natural-index scan states. -/
def represent {K F : Type*} (f : K → Pair F) : HighestJetMachine.Configuration K → Configuration F
  | .normalizing s => .normalizing (.ready (QuadraticNormalizeMachine.mapState f s))
  | .terms ts b => .terms (mapTerms f ts) b
  | .factors fs ts b => .factors fs (mapTerms f ts) b
  | .done b => .done b

/-- Recover the independent source rule from a literal dispatch edge. -/
theorem source_step_sound {K : Type*} [CommSemiring K] [DecidableEq K]
    {s t : HighestJetMachine.Configuration K} {c : HighestJetMachine.Cost}
    (h : HighestJetMachine.step s = some (t, c)) : HighestJetMachine.Step s c t := by
  cases s with
  | normalizing s =>
      cases s with
      | done out => cases h; exact .normalized
      | _ =>
          simp only [HighestJetMachine.step, Option.map_eq_some_iff] at h
          obtain ⟨⟨u, d⟩, hu, he⟩ := h
          cases he
          exact .normalize (DenseNormalizeMachine.step_sound hu)
  | terms ts b => cases ts <;> cases h <;> constructor
  | factors fs ts b =>
      cases fs with
      | nil => cases h; exact .next
      | cons p fs => cases h; exact .factor (HighestJetMachine.update_sound p b)
  | done b => simp [HighestJetMachine.step] at h

variable {F : Type*} [Field F] [DecidableEq F]

/-- Every normalization instruction retains its full ledger plus the outer dispatch. -/
theorem normalize_trace {a : F} {n : ℕ}
    {s t : QuadraticNormalizeMachine.Configuration F} {c : Cost}
    (h : QuadraticNormalizeMachine.Trace a n s c t) :
    ∃ d, Trace a n (.normalizing s) d (.normalizing t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Each source rule lowers with a constant independent of terms and jet indices. -/
theorem step_lowering {a : F} {s t : HighestJetMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : HighestJetMachine.Cost} (h : HighestJetMachine.Step s c t) :
    ∃ n d, Trace a n (represent encode s) d (represent encode t) ∧ n + d.total ≤ 2048 := by
  cases h with
  | normalize h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticNormalizeMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := normalize_trace hc
      exact ⟨n, d, hd, by omega⟩
  | normalized => exact ⟨1, administrative (HighestJetMachine.charge 0 2 0 0 0),
      single rfl, by decide⟩
  | term => exact ⟨1, administrative (HighestJetMachine.charge 0 3 0 0 0), single rfl, by decide⟩
  | factor h => exact ⟨1, administrative (HighestJetMachine.charge 0 6 5 0 0),
      single (by simp [step, represent, h.eq]), by decide⟩
  | next => exact ⟨1, administrative (HighestJetMachine.charge 0 2 0 0 0), single rfl, by decide⟩
  | emit => exact ⟨1, administrative (HighestJetMachine.charge 0 2 0 0 1), single rfl, by decide⟩

/-- Literal dispatch edges use the same coordinate simulation. -/
theorem dispatch_lowering {a : F}
    {s t : HighestJetMachine.Configuration (QuadraticAlgebra F a 0)} {c : HighestJetMachine.Cost}
    (h : HighestJetMachine.step s = some (t, c)) :
    ∃ n d, Trace a n (represent encode s) d (represent encode t) ∧ n + d.total ≤ 2048 :=
  step_lowering (source_step_sound h)

/-- The factor applies once to the total source trace. -/
theorem trace_lowering {a : F} {n : ℕ}
    {s t : HighestJetMachine.Configuration (QuadraticAlgebra F a 0)} {c : HighestJetMachine.Cost}
    (h : HighestJetMachine.Trace n s c t) :
    ∃ k d, Trace a k (represent encode s) d (represent encode t) ∧ k + d.total ≤ 2048 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

end MvPolynomial.QuadraticHighestMachine
