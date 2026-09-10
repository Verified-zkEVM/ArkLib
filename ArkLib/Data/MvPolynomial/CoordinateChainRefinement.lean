/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateChainMachine
public import ArkLib.Data.MvPolynomial.CoordinateHighestRefinement
public import ArkLib.Data.MvPolynomial.CoordinateDerivativeRefinement

/-! # Same-execution coordinate separant chain with retained stage order -/

@[expose] public section

namespace MvPolynomial.QuadraticChainMachine

open QuadraticAlgebra
open QuadraticEvaluationMachine (Cost total_add encode)
open QuadraticNormalizeMachine (mapTerms)

/-- Preserve the original equation and selected variable/exponent pair. -/
def mapStage {K J : Type*} (f : K → J) (s : SeparantChainMachine.Stage K) :
    SeparantChainMachine.Stage J := ⟨mapTerms f s.equation, s.selected⟩
/-- Preserve stage order and multiplicity. -/
def mapStages {K J : Type*} (f : K → J) (ss : List (SeparantChainMachine.Stage K)) :=
  ss.map (mapStage f)

/-- Every child phase and retained equation has the same represented registers. -/
def represent {K F : Type*} (f : K → Pair F) :
    SeparantChainMachine.Configuration K → Configuration F
  | .selecting eqs pre s =>
      .selecting (mapTerms f eqs) (mapStages f pre) (QuadraticHighestMachine.represent f s)
  | .record eqs b pre => .record (mapTerms f eqs) b (mapStages f pre)
  | .derivingAt i pre s =>
      .derivingAt i (mapStages f pre) (.ready (QuadraticDerivativeMachine.mapState f s))
  | .reverse pre out => .reverse (mapStages f pre) (mapStages f out)
  | .done out => .done (mapStages f out)

/-- The literal source dispatch is covered by its independent operational rules. -/
theorem source_step_sound {K : Type*} [CommSemiring K] [DecidableEq K]
    {s t : SeparantChainMachine.Configuration K} {c : SeparantChainMachine.Cost}
    (h : SeparantChainMachine.step s = some (t, c)) : SeparantChainMachine.Step s c t := by
  cases s with
  | selecting eqs pre s =>
      cases s with
      | done b => cases h; exact .selected
      | _ =>
          simp only [SeparantChainMachine.step, Option.map_eq_some_iff] at h
          obtain ⟨⟨u, d⟩, hu, he⟩ := h
          cases he
          exact .selector hu
  | derivingAt i pre s =>
      cases s with
      | done ts => cases h; exact .derived
      | _ =>
          simp only [SeparantChainMachine.step, Option.map_eq_some_iff] at h
          obtain ⟨⟨u, d⟩, hu, he⟩ := h
          cases he
          exact .derivative hu
  | record eqs b pre => cases b with
      | none => cases h; exact .terminal
      | some p => cases p; cases h; exact .active
  | reverse pre out => cases pre <;> cases h <;> constructor
  | done out => simp [SeparantChainMachine.step] at h

variable {F : Type*} [Field F] [DecidableEq F]

/-- Every selector instruction preserves its full charge plus the outer wrapper. -/
theorem selector_trace {a : F} {n : ℕ} (eqs : List (Term F)) (pre : List (Stage F))
    {s t : QuadraticHighestMachine.Configuration F} {c : Cost}
    (h : QuadraticHighestMachine.Trace a n s c t) :
    ∃ d, Trace a n (.selecting eqs pre s) d (.selecting eqs pre t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Every derivative instruction preserves its full charge plus the outer wrapper. -/
theorem derivative_trace {a : F} {n : ℕ} (i : ℕ) (pre : List (Stage F))
    {s t : QuadraticDerivativeMachine.Configuration F} {c : Cost}
    (h : QuadraticDerivativeMachine.Trace a i n s c t) :
    ∃ d, Trace a n (.derivingAt i pre s) d (.derivingAt i pre t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Every original chain edge lowers with a fixed bound independent of stage count. -/
theorem step_lowering {a : F} {s t : SeparantChainMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : SeparantChainMachine.Cost} (h : SeparantChainMachine.Step s c t) :
    ∃ n d, Trace a n (represent encode s) d (represent encode t) ∧ n + d.total ≤ 8192 := by
  cases h with
  | selector h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticHighestMachine.dispatch_lowering h
      obtain ⟨d, hd, he⟩ := selector_trace _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | derivative h =>
      obtain ⟨n, c, hc, hb⟩ :=
        QuadraticDerivativeMachine.step_lowering (PartialDerivativeMachine.step_sound h)
      obtain ⟨d, hd, he⟩ := derivative_trace _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | selected => exact ⟨1, administrative (SeparantChainMachine.charge 0 2 0 0 0),
      single rfl, by decide⟩
  | terminal => exact ⟨1, administrative (SeparantChainMachine.charge 0 6 0 0 1),
      single rfl, by decide⟩
  | active => exact ⟨1, administrative (SeparantChainMachine.charge 0 8 0 0 1),
      single rfl, by decide⟩
  | derived => exact ⟨1, administrative (SeparantChainMachine.charge 0 5 0 0 0),
      single rfl, by decide⟩
  | reverse => exact ⟨1, administrative (SeparantChainMachine.charge 0 5 0 0 1),
      single rfl, by decide⟩
  | emit => exact ⟨1, administrative (SeparantChainMachine.charge 0 2 0 0 1),
      single rfl, by decide⟩

/-- Literal source edges lower to exactly the same represented stages. -/
theorem dispatch_lowering {a : F}
    {s t : SeparantChainMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : SeparantChainMachine.Cost}
    (h : SeparantChainMachine.step s = some (t, c)) :
    ∃ n d, Trace a n (represent encode s) d (represent encode t) ∧ n + d.total ≤ 8192 :=
  step_lowering (source_step_sound h)

/-- The factor applies once to the complete source execution. -/
theorem trace_lowering {a : F} {n : ℕ}
    {s t : SeparantChainMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : SeparantChainMachine.Cost}
    (h : SeparantChainMachine.Trace n s c t) :
    ∃ k d, Trace a k (represent encode s) d (represent encode t) ∧ k + d.total ≤ 8192 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

end MvPolynomial.QuadraticChainMachine
