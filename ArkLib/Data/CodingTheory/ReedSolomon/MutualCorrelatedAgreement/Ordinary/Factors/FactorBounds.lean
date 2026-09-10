/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
/-!
# Degree arithmetic for an ordinary Frobenius factor

These arithmetic bounds account for the pulled reconstruction degree and the smaller
separable fiber degree together. They do not assert existence of the rational chart or its
image-degree bound; those geometric inputs must be proved separately.
-/

@[expose] public section

namespace ReedSolomon

/-- The mixed chart degree with inseparability power `s`, separable degree `b`, challenge
height `h`, and original polynomial degree bound `D`. -/
def ordinaryFrobeniusMixedDegree (D h s b : ℕ) : ℕ :=
  h * (1 + (2 * D * s - 1) * (b - 1)) + b * (s + (2 * D * s - 1) * h)

/-- The exact cancellation between reconstruction and separable fiber degrees. -/
theorem ordinaryFrobeniusMixedDegree_eq (D h s b : ℕ) (hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b =
      h + s * b + (2 * D * s - 1) * h * (2 * b - 1) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
  simp only [ordinaryFrobeniusMixedDegree, Nat.add_sub_cancel_left,
    Nat.mul_add, Nat.mul_one]
  have ht : 2 + 2 * b - 1 = 1 + 2 * b := by omega
  rw [ht]
  ring

/-- The inseparability power incurs no additional multiplicative loss after the original
root degree is written as `s*b`. -/
theorem ordinaryFrobeniusMixedDegree_le (D h s b : ℕ) (hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b ≤ h + s * b + 4 * D * h * (s * b) := by
  rw [ordinaryFrobeniusMixedDegree_eq D h s b hb]
  have hprod : (2 * D * s - 1) * h * (2 * b - 1) ≤ (2 * D * s) * h * (2 * b) := by
    gcongr <;> omega
  calc
    h + s * b + (2 * D * s - 1) * h * (2 * b - 1) ≤
        h + s * b + (2 * D * s) * h * (2 * b) := Nat.add_le_add_left hprod _
    _ = h + s * b + 4 * D * h * (s * b) := by ring

/-- The exact polynomial identity behind the sharper factor comparison. -/
theorem ordinaryFrobenius_sharp_difference (D s b : ℤ) :
    (2 * D - 1) * (2 * (s * b) - 1) - (2 * D * s - 1) * (2 * b - 1) =
      2 * (s - 1) * (D - b) := by
  ring

/-- The sharper factor comparison applies when the separable degree is at most `D`. -/
theorem ordinaryFrobenius_sharp_factor {D s b : ℕ}
    (hD : b ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    (2 * D * s - 1) * (2 * b - 1) ≤ (2 * D - 1) * (2 * (s * b) - 1) := by
  have hD1 : 1 ≤ D := hb.trans hD
  have hds : 1 ≤ 2 * D * s := by nlinarith [Nat.mul_le_mul hD1 hs]
  have hsb : 1 ≤ 2 * (s * b) := by nlinarith [Nat.mul_le_mul hs hb]
  have hD2 : 1 ≤ 2 * D := by omega
  have hb2 : 1 ≤ 2 * b := by omega
  zify [hds, hsb, hD2, hb2]
  have hsn : (0 : ℤ) ≤ (s : ℤ) - 1 := by omega
  have hDn : (0 : ℤ) ≤ (D : ℤ) - b := by omega
  nlinarith [mul_nonneg hsn hDn]

/-- The sharper ordinary image charge also absorbs the pulled reconstruction degree. -/
theorem ordinaryFrobeniusMixedDegree_le_sharp {D s b : ℕ} (h : ℕ)
    (hD : b ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b ≤
      h + s * b + (2 * D - 1) * h * (2 * (s * b) - 1) := by
  rw [ordinaryFrobeniusMixedDegree_eq D h s b hb]
  apply Nat.add_le_add_left
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul_right h (ordinaryFrobenius_sharp_factor hD hs hb)

end ReedSolomon
