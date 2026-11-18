/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Basic
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the Reed–Muller affine combiner definitions -/

open ReedSolomon ReedMuller MvPolynomial Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The multiplier of `(1, 2, 3)` evaluates to `1 + 2 · 1 + 3 · 4 = 0` at `(1, 4)` in `F₅`.
example : eval ![1, 4] (reedMullerMultiplier (![1, 2, 3] : Fin 3 → ZMod 5)) = 0 := by
  rw [eval_reedMullerMultiplier]
  decide

-- The multiplier has total degree at most one, so `F₀ + L_α G₀` keeps total degree `≤ d`.
example (α : Fin 3 → ZMod 5) : (reedMullerMultiplier α).totalDegree ≤ 1 :=
  totalDegree_reedMullerMultiplier_le α

-- A second word of total degree below `d` admits witnesses for every candidate.
example (f : (Fin 2 → ZMod 5) → ZMod 5) (G₀ : MvPolynomial (Fin 2) (ZMod 5))
    (hG : G₀.totalDegree < 2) (α : Fin 3 → ZMod 5) (P : MvPolynomial (Fin 2) (ZMod 5)) :
    ¬ IsReedMullerExceptional f (fun z ↦ eval (gridPoint (ZMod 5) z) G₀) 2 4 0 α P :=
  not_isReedMullerExceptional_of_eval f G₀ hG α P

-- Exceptionality persists when the loss and the threshold decrease.
example {f g : (Fin 2 → ZMod 5) → ZMod 5} {α : Fin 3 → ZMod 5}
    {P : MvPolynomial (Fin 2) (ZMod 5)} (h : IsReedMullerExceptional f g 1 10 5 α P) :
    IsReedMullerExceptional f g 1 8 3 α P :=
  (h.anti_loss (by norm_num)).anti_threshold (by norm_num)

-- The error is a probability.
example : reedMullerMcaError (ZMod 5) (ZMod 5) 2 1 10 5 ≤ 1 :=
  reedMullerMcaError_le_one 2 1 10 5

-- A uniform count of zero exceptional vectors gives error zero.
example (h : ∀ f g : (Fin 2 → ZMod 5) → ZMod 5, ∀ α P,
    ¬ IsReedMullerExceptional f g 1 10 5 α P) :
    reedMullerMcaError (ZMod 5) (ZMod 5) 2 1 10 5 ≤ ENNReal.ofReal (0 / 5 ^ 3) :=
  reedMullerMcaError_le_of_forall_exists fun f g ↦ ⟨∅, by simp, fun α _ P ↦ h f g α P⟩

-- The definitions accept the caller's field and equality instances.
open Classical in
example {K₀ F : Type*} [Field K₀] [Fintype K₀] [Field F] [Fintype F] [DecidableEq F]
    [Algebra K₀ F] (f g : (Fin 2 → K₀) → F) :
    ENNReal.ofReal
      ((#{α : Fin 3 → F | ∃ P, IsReedMullerExceptional f g 1 4 2 α P} : ℝ) /
        (Fintype.card F : ℝ) ^ 3) ≤ reedMullerMcaError K₀ F 2 1 4 2 :=
  le_reedMullerMcaError 1 4 2 f g

/-- info: 'ReedSolomon.reedMullerMcaError_le_of_forall_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.reedMullerMcaError_le_of_forall_exists

/-- info: 'ReedSolomon.not_isReedMullerExceptional_of_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.not_isReedMullerExceptional_of_eval
