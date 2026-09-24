/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.Simulation.Basic

/-! Regression tests for deterministic guarded simulation and `vcv_guard`. -/

open OracleComp OracleSpec
open scoped ProbabilityTheory

namespace GuardedSimulationTest

variable {ι σ α : Type} {spec : OracleSpec ι}
  (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))

/-- A toy verifier whose guard and output remain explicit. -/
def check (p : Prop) [Decidable p] (x : α) : OptionT (OracleComp spec) α :=
  if p then pure x else failure

example (p : Prop) [Decidable p] (x : α) (R : α → Prop)
    (h : Pr{let y ← OptionT.mk (do
      let s ← init
      (simulateQ impl (check p x)).run' s)}[R y] > 0) : p ∧ R x := by
  vcv_guard [check] at h
  exact h

example (x : α) :
    some x ∉ support (do
      let s ← init
      (simulateQ impl (if False then pure (some x) else pure none)).run' s) := by
  rw [OptionT.mem_support_simulateQ_run'_guarded_iff]
  simp

example (x y : α) :
    some y ∈ support (do
      let s ← init
      (simulateQ impl (if True then pure (some x) else pure none)).run' s) ↔ y = x := by
  rw [OptionT.mem_support_simulateQ_run'_guarded_iff]
  simp

end GuardedSimulationTest
