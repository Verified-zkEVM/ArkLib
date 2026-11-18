/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.RationalPair
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for the Reed–Muller rational-pair bounds (Lemma A.1) -/

open ReedMuller MvPolynomial Finset

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _

private noncomputable instance : Fintype (GaloisField 2 8) := Fintype.ofFinite _

private theorem card_galoisField_3_2 : Fintype.card (GaloisField 3 2) = 9 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
  norm_num

private theorem card_galoisField_2_8 : Fintype.card (GaloisField 2 8) = 256 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 8 (by norm_num)]
  norm_num

/-- Polynomials over `F₃` in two variables. -/
private abbrev R := MvPolynomial (Fin 2) (ZMod 3)

/-- Polynomials over `F₉` in two variables. -/
private abbrev R₉ := MvPolynomial (Fin 2) (GaloisField 3 2)

-- On the proper subfield grid `F₃² ⊆ F₉²` (`n = 9`), witnesses `X₁, X₂` at `d = 2` leave at most
-- `9 choose 3 = 84` exceptional coefficient vectors at loss `3`.
open Classical in
example (f g : (Fin 2 → ZMod 3) → GaloisField 3 2) :
    #{α : Fin 3 → GaloisField 3 2 | IsAffineExceptional f g 2 5 3 α
      (X 0 + affineMultiplier α * X 1)} ≤ 84 := by
  have h := card_isAffineExceptional_add_mul_le f g (d := 2) (A := 5) (X 0 : R₉) (X 1)
    (by simp) (Or.inr (by simp))
  exact h.trans (by rw [ZMod.card]; decide)

-- The zero second witness is admissible even at `d = 0`.
open Classical in
example (f g : (Fin 2 → ZMod 3) → ZMod 3) :
    #{α : Fin 3 → ZMod 3 | IsAffineExceptional f g 0 5 3 α
      ((1 : R) + affineMultiplier α * 0)} ≤ 84 := by
  have h := card_isAffineExceptional_add_mul_le f g (d := 0) (A := 5) (1 : R) 0
    (by simp) (Or.inl rfl)
  exact h.trans (by rw [ZMod.card]; decide)

-- The first rational function `X₁²` exceeds the degree bound `d = 1`, so at most `q = 3`
-- coefficient vectors make `X₁² + L_α · 0` a polynomial of total degree at most one.
open Classical in
example :
    #{α : Fin 3 → ZMod 3 | ∃ P : R, P.totalDegree ≤ 1 ∧
      algebraMap R (FractionRing R) P =
        algebraMap R (FractionRing R) (X 0 ^ 2) +
          algebraMap R (FractionRing R) (affineMultiplier α) * 0} ≤ 3 := by
  have h := card_fractionRing_combination_le (k := 2) (d := 1)
    (algebraMap R (FractionRing R) (X 0 ^ 2)) 0 ?_
  · simpa [ZMod.card] using h
  rintro ⟨F₁, G₁, hF, -, hdeg, -⟩
  rw [(IsFractionRing.injective R (FractionRing R)) hF, totalDegree_X_pow] at hdeg
  omega

-- The combined bound on the proper subfield grid `F₃² ⊆ F₉²` is `max 9 84 = 84`.
open Classical in
example (f g : (Fin 2 → ZMod 3) → GaloisField 3 2) (F₀ G₀ : FractionRing R₉) :
    #{α : Fin 3 → GaloisField 3 2 | ∃ P : R₉,
        algebraMap R₉ (FractionRing R₉) P =
          F₀ + algebraMap R₉ (FractionRing R₉) (affineMultiplier α) * G₀ ∧
        IsAffineExceptional f g 2 5 3 α P} ≤ 84 := by
  have h := card_isAffineExceptional_fractionRing_le f g (A := 5) (d := 2) F₀ G₀
  exact h.trans (by rw [ZMod.card, card_galoisField_3_2]; decide)

-- On the grid `F₂ ⊆ F₂₅₆` (`k = 1`, `n = 2`), the field side wins: `max 256 (2 choose 2) = 256`.
open Classical in
example (f g : (Fin 1 → ZMod 2) → GaloisField 2 8)
    (F₀ G₀ : FractionRing (MvPolynomial (Fin 1) (GaloisField 2 8))) :
    #{α : Fin 2 → GaloisField 2 8 | ∃ P : MvPolynomial (Fin 1) (GaloisField 2 8),
        algebraMap _ (FractionRing (MvPolynomial (Fin 1) (GaloisField 2 8))) P =
          F₀ + algebraMap _ _ (affineMultiplier α) * G₀ ∧
        IsAffineExceptional f g 1 2 1 α P} ≤ 256 := by
  have h := card_isAffineExceptional_fractionRing_le f g (A := 2) (d := 1) F₀ G₀
  exact h.trans (by rw [ZMod.card, card_galoisField_2_8]; decide)

/-- info: 'ReedMuller.eval_affineMultiplier_eq_of_mem_agreementLoss' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.eval_affineMultiplier_eq_of_mem_agreementLoss

/-- info: 'ReedMuller.card_isAffineExceptional_add_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_isAffineExceptional_add_mul_le

/-- info: 'ReedMuller.exists_forall_eq_smul_of_affineMultiplier_mul_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_forall_eq_smul_of_affineMultiplier_mul_eq

/-- info: 'ReedMuller.card_fractionRing_combination_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_fractionRing_combination_le

/-- info: 'ReedMuller.card_isAffineExceptional_fractionRing_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_isAffineExceptional_fractionRing_le
