/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Basic
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the Reed–Muller affine combiner definitions -/

open ReedMuller MvPolynomial Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The multiplier of `(1, 2, 3)` evaluates to `1 + 2 · 1 + 3 · 4 = 0` at `(1, 4)` in `F₅`.
example : eval ![1, 4] (affineMultiplier (![1, 2, 3] : Fin 3 → ZMod 5)) = 0 := by
  rw [eval_affineMultiplier]
  decide

-- Here the multiplier is `1 + 2 · 1 + 3 · 2 = 4` in `F₅`, so the output is `2 + 4 · 3 = 4`.
/-- info: true -/
#guard_msgs in
#eval affineCombinedWord (K₀ := ZMod 5) (F := ZMod 5)
  (fun _ ↦ 2) (fun _ ↦ 3) ![1, 2, 3] ![1, 2] == 4

-- The multiplier has total degree at most one, so `F₀ + L_α G₀` keeps total degree `≤ d`.
example (α : Fin 3 → ZMod 5) : (affineMultiplier α).totalDegree ≤ 1 :=
  totalDegree_affineMultiplier_le α

-- A second word of total degree below `d` admits witnesses for every candidate.
example (f : (Fin 2 → ZMod 5) → ZMod 5) (G₀ : MvPolynomial (Fin 2) (ZMod 5))
    (hG : G₀.totalDegree < 2) (α : Fin 3 → ZMod 5) (P : MvPolynomial (Fin 2) (ZMod 5)) :
    ¬ IsAffineExceptional f (fun z ↦ eval (gridPoint (ZMod 5) z) G₀) 2 4 0 α P :=
  not_isAffineExceptional_of_eval f G₀ (Or.inr hG) α P

-- At `d = 0` the zero second witness is still admissible, so `g = 0` gives no exceptions.
example (f : (Fin 2 → ZMod 5) → ZMod 5) (α : Fin 3 → ZMod 5)
    (P : MvPolynomial (Fin 2) (ZMod 5)) :
    ¬ IsAffineExceptional f (fun z ↦ eval (gridPoint (ZMod 5) z) 0) 0 1 0 α P :=
  not_isAffineExceptional_of_eval f 0 (Or.inl rfl) α P

-- Exceptionality persists when the loss and the threshold decrease.
example {f g : (Fin 2 → ZMod 5) → ZMod 5} {α : Fin 3 → ZMod 5}
    {P : MvPolynomial (Fin 2) (ZMod 5)} (h : IsAffineExceptional f g 1 10 5 α P) :
    IsAffineExceptional f g 1 8 3 α P :=
  (h.anti_loss (by norm_num)).anti_threshold (by norm_num)

-- The error is a probability.
example : affineMcaError (ZMod 5) (ZMod 5) 2 1 10 5 ≤ 1 :=
  affineMcaError_le_one 2 1 10 5

-- A threshold `A = 26` above the grid size `n = 25` of `F₅²` makes the error zero.
example : affineMcaError (ZMod 5) (ZMod 5) 2 1 26 5 = 0 :=
  affineMcaError_eq_zero_of_card_lt (by simp [ZMod.card])

-- The definitions accept the caller's field and equality instances.
open Classical in
example {K₀ F : Type*} [Field K₀] [Fintype K₀] [Field F] [Fintype F] [DecidableEq F]
    [Algebra K₀ F] (f g : (Fin 2 → K₀) → F) :
    ENNReal.ofReal
      ((#{α : Fin 3 → F | ∃ P, IsAffineExceptional f g 1 4 2 α P} : ℝ) /
        (Fintype.card F : ℝ) ^ 3) ≤ affineMcaError K₀ F 2 1 4 2 :=
  le_affineMcaError 1 4 2 f g

/-- info: 'ReedMuller.eval_affineMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.eval_affineMultiplier

/-- info: 'ReedMuller.coeff_zero_affineMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.coeff_zero_affineMultiplier

/-- info: 'ReedMuller.coeff_single_affineMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.coeff_single_affineMultiplier

/-- info: 'ReedMuller.affineMultiplier_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMultiplier_injective

/-- info: 'ReedMuller.totalDegree_affineMultiplier_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.totalDegree_affineMultiplier_le

/-- info: 'ReedMuller.affineMultiplier_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMultiplier_sub

/-- info: 'ReedMuller.affineMultiplier_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMultiplier_zero

/-- info: 'ReedMuller.affineMultiplier_smul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMultiplier_smul

/-- info: 'ReedMuller.succ_eq_zero_of_totalDegree_affineMultiplier_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.succ_eq_zero_of_totalDegree_affineMultiplier_eq_zero

/-- info: 'ReedMuller.combinedWord_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.combinedWord_apply

/-- info: 'ReedMuller.mem_agreementSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.mem_agreementSet

/-- info: 'ReedMuller.mem_agreementLoss' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.mem_agreementLoss

/-- info: 'ReedMuller.le_affineMcaError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.le_affineMcaError

/-- info: 'ReedMuller.affineMcaError_le_of_forall_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMcaError_le_of_forall_exists

/-- info: 'ReedMuller.affineMcaError_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMcaError_le_one

/-- info: 'ReedMuller.not_isAffineExceptional_of_card_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.not_isAffineExceptional_of_card_lt

/-- info: 'ReedMuller.affineMcaError_eq_zero_of_card_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMcaError_eq_zero_of_card_lt

/-- info: 'ReedMuller.IsAffineExceptional.anti_loss' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.IsAffineExceptional.anti_loss

/-- info: 'ReedMuller.IsAffineExceptional.anti_threshold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.IsAffineExceptional.anti_threshold

/-- info: 'ReedMuller.not_isAffineExceptional_of_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.not_isAffineExceptional_of_eval
