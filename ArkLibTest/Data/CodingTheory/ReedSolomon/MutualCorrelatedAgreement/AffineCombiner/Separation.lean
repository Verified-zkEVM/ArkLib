/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Separation
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the combiner lower bounds -/

open ReedSolomon

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

/-- Six of the seven points of `F₇` as the evaluation domain. -/
private def sixDomain : Fin 6 ↪ ZMod 7 :=
  ⟨fun i ↦ (i : ℕ), fun i j h ↦ Fin.ext (by
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this)⟩

-- The word `x + α` has one zero for each challenge over the full field.
/-- info: true -/
#guard_msgs in
#eval (exactZeroChallenges (fun x : ZMod 5 ↦ x) (fun _ ↦ 1) 1).card == 5

/-- Without loss, the affine error at `d = 1`, `A = 3` on `F₅` is at least `12 / 25`. -/
example : (12 : ENNReal) / 25 ≤ affineMcaError fullDomain 1 3 0 := by
  have h := le_affineMcaError_zero_loss fullDomain (d := 1) (A := 3) (by norm_num)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

/-- With loss `1`, the scalar error at `d = 0`, `A = 3` on `F₅` is at least `2 / 5`. -/
example : (2 : ENNReal) / 5 ≤ scalarMcaError fullDomain 0 3 1 := by
  have h := le_scalarMcaError_of_degree_add_loss_add_one_lt fullDomain
    (d := 0) (A := 3) (s := 1) (by norm_num)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

-- On all of `F₇` with `d = 1`, `A = 4`, `s = 1`, the floor matters: `1 + ⌊3 / 2⌋ = 2`.
open Polynomial Finset in
example : ∃ f g : ZMod 7 → ZMod 7,
    (∀ G : (ZMod 7)[X], G.degree ≤ 1 → #(polynomialAgreementSet (.refl _) g G) < 3) ∧
    (∀ α ∈ exactZeroChallenges f g 4, IsScalarExceptional (.refl _) f g 1 4 1 α 0) ∧
    2 ≤ #(exactZeroChallenges f g 4) :=
  exists_words_forall_isScalarExceptional_zero (.refl _) (d := 1) (A := 4) (s := 1)
    (by norm_num) (by simp [ZMod.card])

-- On six points of `F₇`, two challenges have exactly four agreements.
-- Their probability gives the lower bound `2 / 7` on the scalar error.
example : (2 : ENNReal) / 7 ≤ scalarMcaError sixDomain 0 4 1 := by
  obtain ⟨f, g, hfar, -, hcount⟩ :=
    exists_words_forall_isScalarExceptional_zero sixDomain (d := 0) (A := 4) (s := 1)
      (by norm_num) (by simp)
  have h2 : (2 : ℝ) ≤ (exactZeroChallenges f g 4).card := by exact_mod_cast hcount
  calc (2 : ENNReal) / 7 = ENNReal.ofReal ((2 : ℝ) / 7) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (((exactZeroChallenges f g 4).card : ℝ) /
        (Fintype.card (ZMod 7) : ℝ)) := by
        rw [ZMod.card, Nat.cast_ofNat]
        gcongr
    _ ≤ _ := le_scalarMcaError_of_forall_card_lt sixDomain hfar

/-- info: 'ReedSolomon.exists_words_forall_isScalarExceptional_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_words_forall_isScalarExceptional_zero

/-- info: 'ReedSolomon.le_scalarMcaError_of_forall_card_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_scalarMcaError_of_forall_card_lt

/-- info: 'ReedSolomon.isScalarExceptional_of_forall_card_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.isScalarExceptional_of_forall_card_lt
