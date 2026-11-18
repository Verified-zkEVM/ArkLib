/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.RationalPair
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the Reed–Muller rational-pair bounds (Lemma A.1) -/

open ReedSolomon MvPolynomial Finset

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Polynomials over `F₃` in two variables. -/
private abbrev R := MvPolynomial (Fin 2) (ZMod 3)

-- With witnesses `F₀ = X₁` and `G₀ = X₂` at `d = 2` on the grid `F₃²` (`n = 9`),
-- at most `9 choose 3 = 84` coefficient vectors are exceptional at loss `3`.
open Classical in
example (f g : (Fin 2 → ZMod 3) → ZMod 3) :
    #{α : Fin 3 → ZMod 3 | IsReedMullerExceptional f g 2 5 3 α
      (X 0 + reedMullerMultiplier α * X 1)} ≤ 84 := by
  have h := card_isReedMullerExceptional_add_mul_le f g (d := 2) (A := 5) (X 0 : R) (X 1)
    (by simp) (by simp)
  exact h.trans (by rw [ZMod.card]; decide)

-- The first rational function `X₁²` exceeds the degree bound `d = 1`, so at most `q = 3`
-- coefficient vectors make `X₁² + L_α · 0` a polynomial of total degree at most one.
open Classical in
example :
    #{α : Fin 3 → ZMod 3 | ∃ P : R, P.totalDegree ≤ 1 ∧
      algebraMap R (FractionRing R) P =
        algebraMap R (FractionRing R) (X 0 ^ 2) +
          algebraMap R (FractionRing R) (reedMullerMultiplier α) * 0} ≤ 3 := by
  have h := card_reedMuller_fractionRing_combination_le (k := 2) (d := 1) le_rfl
    (algebraMap R (FractionRing R) (X 0 ^ 2)) 0 ?_
  · simpa [ZMod.card] using h
  rintro ⟨F₁, G₁, hF, -, hdeg, -⟩
  rw [(IsFractionRing.injective R (FractionRing R)) hF, totalDegree_X_pow] at hdeg
  omega

-- The combined bound `max q (n choose (k + 1)) = max 3 84` holds for every rational pair.
open Classical in
example (f g : (Fin 2 → ZMod 3) → ZMod 3) (F₀ G₀ : FractionRing R) :
    #{α : Fin 3 → ZMod 3 | ∃ P : R,
        algebraMap R (FractionRing R) P =
          F₀ + algebraMap R (FractionRing R) (reedMullerMultiplier α) * G₀ ∧
        IsReedMullerExceptional f g 2 5 3 α P} ≤ 84 := by
  have h := card_isReedMullerExceptional_fractionRing_le f g (A := 5) (d := 2) (by norm_num)
    F₀ G₀
  exact h.trans (by rw [ZMod.card]; decide)

/-- info: 'ReedSolomon.card_isReedMullerExceptional_add_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_isReedMullerExceptional_add_mul_le

/-- info: 'ReedSolomon.card_reedMuller_fractionRing_combination_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_reedMuller_fractionRing_combination_le

/-- info: 'ReedSolomon.card_isReedMullerExceptional_fractionRing_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_isReedMullerExceptional_fractionRing_le
