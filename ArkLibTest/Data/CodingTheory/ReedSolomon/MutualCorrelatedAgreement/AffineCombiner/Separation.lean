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

open Polynomial Finset in
/-- Proposition 6.1 at `d = 0`, `A = 4`, `s = 1` on six points of `F₇`.

The exact count is `1 + ⌊(6 - 4) / 2⌋ = 2` challenges with exactly four agreements. -/
example : ∃ f g : Fin 6 → ZMod 7,
    (∀ G : (ZMod 7)[X], G.degree ≤ 0 → #(polynomialAgreementSet sixDomain g G) < 3) ∧
    (∀ α : ZMod 7, #(polynomialAgreementSet sixDomain (combinedWord sixDomain f g (C α)) 0) = 4 →
      IsScalarExceptional sixDomain f g 0 4 1 α 0) ∧
    2 ≤ #{α : ZMod 7 |
      #(polynomialAgreementSet sixDomain (combinedWord sixDomain f g (C α)) 0) = 4} :=
  exists_words_forall_isScalarExceptional_zero sixDomain (d := 0) (A := 4) (s := 1)
    (by norm_num) (by simp)

open Polynomial Finset in
/-- On all of `F₇` with `d = 1`, `A = 4`, `s = 1`, the floor matters: `1 + ⌊3 / 2⌋ = 2`. -/
example : ∃ f g : ZMod 7 → ZMod 7,
    (∀ G : (ZMod 7)[X], G.degree ≤ 1 → #(polynomialAgreementSet (.refl _) g G) < 3) ∧
    (∀ α : ZMod 7, #(polynomialAgreementSet (.refl _) (combinedWord (.refl _) f g (C α)) 0) = 4 →
      IsScalarExceptional (.refl _) f g 1 4 1 α 0) ∧
    2 ≤ #{α : ZMod 7 |
      #(polynomialAgreementSet (.refl _) (combinedWord (.refl _) f g (C α)) 0) = 4} :=
  exists_words_forall_isScalarExceptional_zero (.refl _) (d := 1) (A := 4) (s := 1)
    (by norm_num) (by simp [ZMod.card])

/-- info: 'ReedSolomon.exists_words_forall_isScalarExceptional_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_words_forall_isScalarExceptional_zero
