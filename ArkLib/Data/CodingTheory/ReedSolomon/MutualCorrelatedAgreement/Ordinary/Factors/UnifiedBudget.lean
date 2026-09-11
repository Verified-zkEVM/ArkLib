/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.FactorBounds

/-!
# One characteristic-free ordinary transfer budget

The positive-part correction extends the sharp ordinary factor comparison beyond the range where
the separable factor degree is at most the message degree. It agrees with the sharp coefficient
through root degree `2 * D + 1` and remains valid for every Frobenius factor.
-/

@[expose] public section

namespace ReedSolomon

/-- The unified coefficient of challenge height in the ordinary joint-image degree. -/
def ordinaryPsi (D B : ℕ) : ℕ :=
  1 + (2 * D - 1) * (2 * B - 1) + 2 * (B - 2 * D - 1)

/-- Up to root degree `2D+1`, the unified coefficient is exactly the sharp coefficient. -/
theorem ordinaryPsi_eq_sharp {D B : ℕ} (hB : B ≤ 2 * D + 1) :
    ordinaryPsi D B = 1 + (2 * D - 1) * (2 * B - 1) := by
  unfold ordinaryPsi
  omega

/-- The positive-part correction absorbs the degree loss of every inseparable pullback, including
the case where the separable factor degree exceeds `D`. -/
theorem ordinaryFrobenius_unified_factor {D s b : ℕ}
    (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    1 + (2 * D * s - 1) * (2 * b - 1) ≤ ordinaryPsi D (s * b) := by
  unfold ordinaryPsi
  by_cases hbD : b ≤ D
  · exact (Nat.add_le_add_left (ordinaryFrobenius_sharp_factor hbD hs hb) 1).trans
      (Nat.le_add_right _ _)
  have hDb : D < b := Nat.lt_of_not_ge hbD
  rcases eq_or_lt_of_le hs with rfl | hsTwo
  · simp
  have htailPos : 2 * D + 1 ≤ s * b := by nlinarith
  have hDs : 1 ≤ 2 * D * s := by nlinarith
  have hbTwo : 1 ≤ 2 * b := by omega
  have hDTwo : 1 ≤ 2 * D := by omega
  have hsbTwo : 1 ≤ 2 * (s * b) := by nlinarith
  have hsZ : (0 : ℤ) ≤ (s : ℤ) - 2 := by omega
  have hDZ : (0 : ℤ) ≤ D := by positivity
  have hbZ : (0 : ℤ) ≤ (b : ℤ) - D - 1 := by omega
  have htailZ :
      (2 : ℤ) * ((s : ℤ) - 1) * ((b : ℤ) - D) ≤
        2 * ((s : ℤ) * b - 2 * D - 1) := by
    nlinarith [mul_nonneg hDZ hsZ]
  have htailCast : ((s * b - 2 * D - 1 : ℕ) : ℤ) =
      (s : ℤ) * b - 2 * D - 1 := by omega
  zify [hDs, hbTwo, hDTwo, hsbTwo, htailPos]
  rw [htailCast] at *
  nlinarith [ordinaryFrobenius_sharp_difference (D : ℤ) (s : ℤ) (b : ℤ), htailZ]

/-- The ordinary Frobenius image degree satisfies the unified bound without assuming `b ≤ D`. -/
theorem ordinaryFrobeniusMixedDegree_le_unified {D s b : ℕ} (h : ℕ)
    (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b ≤ s * b + h * ordinaryPsi D (s * b) := by
  rw [ordinaryFrobeniusMixedDegree_eq D h s b hb]
  have hcoefficient := ordinaryFrobenius_unified_factor hD hs hb
  nlinarith

/-- The unified all-characteristic ordinary MCA budget for a received curve of degree `ell`.
This is the integral form of the manuscript's `E_ord^(ell)`. -/
def ordinaryUnifiedPowerFactorRaw (theta : ℚ) (n D ell B H : ℕ) : ℚ :=
  ((2 * B - 1) * H : ℕ) + theta * (ell * B + H * ordinaryPsi D B : ℕ) +
    (ell * ((n - D - 1) * B) : ℕ)

end ReedSolomon
