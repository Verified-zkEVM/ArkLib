/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Persistent
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for Reed–Muller persistence and its Johnson count -/

open ReedMuller MvPolynomial Finset

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _

private noncomputable instance : Fintype (GaloisField 2 8) := Fintype.ofFinite _

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

/-- The subfield embedding `GF(2⁸) ⊆ GF(2⁶⁴)`, which exists since `8 ∣ 64`. -/
private noncomputable instance : Algebra (GaloisField 2 8) (GaloisField 2 64) :=
  (Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 8) (L := GaloisField 2 64)
    (by rw [GaloisField.finrank 2 (by norm_num), GaloisField.finrank 2 (by norm_num)]
        norm_num))).toRingHom.toAlgebra

private theorem card_galoisField_3_2 : Fintype.card (GaloisField 3 2) = 9 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
  norm_num

private theorem card_galoisField_2_8 : Fintype.card (GaloisField 2 8) = 2 ^ 8 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 8 (by norm_num)]

private theorem card_galoisField_2_64 : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

/-- The multiplier `L = X₁` in two variables over `F₃`. -/
private def σX : Fin 3 → ZMod 3 := ![0, 1, 0]

-- On the grid `F₃²`, `H = 0` and `L = X₁` explain the zero words at the six points with `z₁ ≠ 0`.
-- The three zeros of `X₁` do not count, and the zero candidate is persistent at threshold `6`.
example : IsAffinePersistent (K₀ := ZMod 3) (F := ZMod 3) (k := 2) (fun _ ↦ 0) (fun _ ↦ 0)
    0 6 0 0 := by
  refine ⟨0, σX, by decide, by simp, ?_⟩
  have hset : affinePersistenceSet (k := 2) (fun _ ↦ (0 : ZMod 3)) (fun _ ↦ 0) 0 0 0 σX =
      ({z : Fin 2 → ZMod 3 | z 0 ≠ 0} : Finset _) := by
    ext z
    simp [σX, Fin.sum_univ_two]
  rw [hset]
  decide

-- At `k = 2`, `q₀ = 3`, `q = 9`, `d = 0` and `B = 6`, the paper's `a = 2/3` and `b = 1/3` give
-- `ℓ = (a - b) / (a² - b) = 3`; with `max 9 (9 choose 3) = 84`, the count is at most `252`.
open Classical in
example (f g : (Fin 2 → ZMod 3) → GaloisField 3 2) (A : ℕ) :
    (#{α : Fin 3 → GaloisField 3 2 | ∃ P, IsAffineExceptional f g 0 A 3 α P ∧
        IsAffinePersistent f g 0 6 α P} : ℝ) ≤ 252 := by
  have h := card_isAffineExceptional_persistent_le f g (k := 2) (d := 0) (A := A) (B := 6)
    (by simp [ZMod.card]) (by simp [ZMod.card])
  simp only [ZMod.card, card_galoisField_3_2] at h
  norm_num [Nat.choose] at h
  exact_mod_cast h

-- The worked case `q₀ = 2⁸`, `k = 2`, `d = 64`, `B = 40704` over `F = GF(2⁶⁴)`.
-- Here `ℓ = 65536 · 24064 / 566296576 < 3`, and `(2¹⁶ choose 3) < 2⁶⁴ = q`.
open Classical in
example (f g : (Fin 2 → GaloisField 2 8) → GaloisField 2 64) (A : ℕ) :
    (#{α : Fin 3 → GaloisField 2 64 | ∃ P, IsAffineExceptional f g 64 A (2 ^ 8) α P ∧
        IsAffinePersistent f g 64 40704 α P} : ℝ) ≤ 3 * 2 ^ 64 := by
  have h := card_isAffineExceptional_persistent_le f g (k := 2) (d := 64) (A := A) (B := 40704)
    (by rw [card_galoisField_2_8]; norm_num) (by rw [card_galoisField_2_8]; norm_num)
  have hchoose : ((2 ^ 8) ^ 2).choose (2 + 1) ≤ 2 ^ 64 :=
    (Nat.choose_le_pow _ _).trans (by norm_num)
  rw [card_galoisField_2_8, card_galoisField_2_64] at h
  refine h.trans ?_
  rw [max_eq_left (by exact_mod_cast hchoose)]
  norm_num

-- The hypothesis `(d + 1) q₀ᵏ⁻¹ < B` is needed: on the grid `F₂` (`n = 2`) with `d = 5` and
-- `B = 4`, the Johnson condition `n (d + 1) < B²` holds, nothing is persistent, and `ℓ = -1`.
open Classical in
example (f g : (Fin 1 → ZMod 2) → ZMod 2) (A : ℕ) :
    ¬ (#{α : Fin 2 → ZMod 2 | ∃ P, IsAffineExceptional f g 5 A 1 α P ∧
        IsAffinePersistent f g 5 4 α P} : ℝ) ≤
      (2 : ℝ) ^ 1 * ((4 : ℝ) - (5 + 1) * 2 ^ (1 - 1)) /
          ((4 : ℝ) ^ 2 - 2 ^ 1 * ((5 + 1) * 2 ^ (1 - 1))) *
        max (2 : ℝ) ((2 ^ 1).choose (1 + 1)) := by
  have hempty : #{α : Fin 2 → ZMod 2 | ∃ P, IsAffineExceptional f g 5 A 1 α P ∧
      IsAffinePersistent f g 5 4 α P} = 0 := by
    refine card_eq_zero.mpr (filter_false_of_mem fun α _ ↦ ?_)
    rintro ⟨P, -, H, σ, -, -, hB⟩
    have := card_le_univ (affinePersistenceSet f g α P H σ)
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at this
    omega
  rw [hempty]
  norm_num

-- The Lean factor `n (B - (d + 1) q₀ᵏ⁻¹) / (B² - n (d + 1) q₀ᵏ⁻¹)` with `n = q₀ᵏ` is the
-- paper's `(a - b) / (a² - b)` with `a = B / n` and `b = (d + 1) / q₀`, for `k ≥ 1`.
example (q₀ B d : ℝ) (k : ℕ) (hq : q₀ ≠ 0) (hk : 1 ≤ k) :
    q₀ ^ k * (B - (d + 1) * q₀ ^ (k - 1)) / (B ^ 2 - q₀ ^ k * ((d + 1) * q₀ ^ (k - 1))) =
      (B / q₀ ^ k - (d + 1) / q₀) / ((B / q₀ ^ k) ^ 2 - (d + 1) / q₀) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [Nat.add_sub_cancel_left, pow_add, pow_one]
  have hqj : q₀ ^ j ≠ 0 := pow_ne_zero _ hq
  field_simp

/-- info: 'ReedMuller.mem_affinePersistenceSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.mem_affinePersistenceSet

/-- info: 'ReedMuller.card_isAffineExceptional_persistent_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_isAffineExceptional_persistent_le

/-- info: 'Finset.card_le_of_fiber_card_le_of_inter_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.card_le_of_fiber_card_le_of_inter_card_le
