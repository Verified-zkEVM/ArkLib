/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.ParameterBounds
public import Mathlib.Algebra.BigOperators.Intervals
/-!
# Finite strict order-zero interpolation counts

The column count is the finite staircase sum over b<2m, with exactly mA-Db choices of X exponent.
These numerical counts do not yet identify a local constraint range or produce an interpolant.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

/-- Strict weighted support with a finite Y-degree cap, including D=0. -/
def zeroStaircaseCount (D L H : ℕ) : ℕ := ∑ b ∈ Finset.range H, (L - D * b)

/-- Adding one Y exponent adds precisely its nonnegative number of X exponents. -/
theorem zeroStaircaseCount_succ (D L H : ℕ) :
    zeroStaircaseCount D L (H + 1) = zeroStaircaseCount D L H + (L - D * H) := by
  exact Finset.sum_range_succ _ _

/-- A staircase whose last slice is nonnegative has an exact doubled arithmetic-sum count. -/
theorem zeroStaircaseCount_balance (D L H : ℕ) (h : D * (H - 1) ≤ L) :
    2 * zeroStaircaseCount D L H + D * H * (H - 1) = 2 * H * L := by
  have hs : ∑ b ∈ Finset.range H, (L - D * b + D * b) = H * L := by
    calc
      _ = ∑ _b ∈ Finset.range H, L := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Nat.sub_add_cancel ((Nat.mul_le_mul_left D (by
          have := Finset.mem_range.mp hb
          omega)).trans h)
      _ = _ := by simp
  simp only [Finset.sum_add_distrib] at hs
  rw [← Finset.mul_sum] at hs
  have hi := Finset.sum_range_id_mul_two H
  unfold zeroStaircaseCount
  calc
    _ = 2 * ((∑ b ∈ Finset.range H, (L - D * b)) + D * ∑ b ∈ Finset.range H, b) := by
      rw [Nat.mul_assoc, ← hi]
      ring
    _ = _ := by rw [hs]; ring

/-- The finite staircase covers the whole triangle whenever L≤D*H. -/
theorem zeroStaircaseCount_area (D L H : ℕ) (h : L ≤ D * H) :
    L * L ≤ 2 * D * zeroStaircaseCount D L H := by
  induction H with
  | zero => simp only [Nat.mul_zero, Nat.le_zero] at h; subst L; omega
  | succ H ih =>
    by_cases hh : L ≤ D * H
    · have hi := ih hh
      rw [zeroStaircaseCount_succ]
      nlinarith
    · have hb := zeroStaircaseCount_balance D L (H + 1) (by
        simpa using (Nat.le_of_lt (Nat.lt_of_not_ge hh)))
      simp only [Nat.add_sub_cancel] at hb
      have hmul : D * (H + 1) = D * H + D := by ring
      have hr : D * (H + 1) - L ≤ D := by omega
      have he : D * (H + 1) - L + L = D * (H + 1) := Nat.sub_add_cancel h
      have hsq := Nat.mul_le_mul hr hr
      have hH := Nat.zero_le H
      have hb' := congrArg (D * ·) hb
      have he₂ := congrArg (fun z : ℕ ↦ z * z) he
      have heL := congrArg (· * L) he
      nlinarith only [he₂, heL, hsq, hH, hb', Nat.zero_le (D * D * H)]

/-- Canonical finite columns for strict X/Y support at order zero. -/
abbrev ZeroInterpolationIndex (D m A : ℕ) := Σ b : Fin (2 * m), Fin (m * A - D * b.val)

/-- The finite dependent columns have exactly the staircase-sum cardinality. -/
theorem card_zeroInterpolationIndex (D m A : ℕ) :
    Fintype.card (ZeroInterpolationIndex D m A) = zeroStaircaseCount D (m * A) (2 * m) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, zeroStaircaseCount]
  exact Fin.sum_univ_eq_sum_range (fun b ↦ m * A - D * b) (2 * m)

/-- For every n≥3, half-length multiplicity yields strictly more columns than triangular rows.
The doubled form avoids natural division in the local triangular count. -/
theorem zero_count_surplus (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : (k : ℝ) + (n : ℝ) / 4 ≤ A) :
    n * (n / 2) * (n / 2 + 1) <
      2 * zeroStaircaseCount (k - 1) ((n / 2) * A) (2 * (n / 2)) := by
  have hm : 0 < n / 2 := by omega
  by_cases ht : A ≤ 2 * (k - 1)
  · have ha := zeroStaircaseCount_area (k - 1) ((n / 2) * A) (2 * (n / 2)) (by
      have h := Nat.mul_le_mul_left (n / 2) ht
      nlinarith only [h])
    have hmargin := zero_triangle_surplus n k A hn hk hA
    have hmargin' : (n : ℝ) * (k - 1 : ℕ) * ((n / 2 : ℕ) + 1) <
        (n / 2 : ℕ) * ((A : ℝ) * A) := by nlinarith only [hmargin]
    have hnat : n * (k - 1) * (n / 2 + 1) < (n / 2) * (A * A) := by
      exact_mod_cast hmargin'
    have hmul := Nat.mul_lt_mul_of_pos_left hnat hm
    apply Nat.lt_of_mul_lt_mul_left (a := k - 1)
    nlinarith only [hmul, ha]
  · have hkA : k - 1 ≤ A := by omega
    have hbal := zeroStaircaseCount_balance (k - 1) ((n / 2) * A) (2 * (n / 2)) (by
      have h := Nat.mul_le_mul_left (n / 2) (Nat.le_of_lt (Nat.lt_of_not_ge ht))
      have hs := Nat.mul_le_mul_left (k - 1) (Nat.sub_le (2 * (n / 2)) 1)
      nlinarith only [h, hs])
    have hsub := Nat.sub_add_cancel hkA
    have hm' : 2 * (n / 2) - 1 + 1 = 2 * (n / 2) := by omega
    have hbalance : 2 * zeroStaircaseCount (k - 1) ((n / 2) * A) (2 * (n / 2)) =
        4 * (n / 2) * (n / 2) * (A - (k - 1)) + 2 * (k - 1) * (n / 2) := by
      have h₁ := congrArg (fun z ↦ 4 * (n / 2) * (n / 2) * z) hsub
      have h₂ := congrArg (fun z ↦ (k - 1) * (2 * (n / 2)) * z) hm'
      nlinarith only [hbal, h₁, h₂]
    rw [hbalance]
    exact zero_truncated_surplus n k A hn hk hA

/-- The dependent columns are exactly the strict finite pair support, including D=0. -/
def zeroInterpolationIndexEquiv (D m A : ℕ) :
    ZeroInterpolationIndex D m A ≃
      {p : ℕ × ℕ // p.2 < 2 * m ∧ p.1 + D * p.2 < m * A} where
  toFun p := ⟨(p.2.val, p.1.val), p.1.isLt, Nat.lt_sub_iff_add_lt.mp p.2.isLt⟩
  invFun p := ⟨⟨p.1.2, p.2.1⟩, ⟨p.1.1, Nat.lt_sub_iff_add_lt.mpr p.2.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Integer triangular constraint count is strictly smaller than the finite column dimension. -/
theorem zero_count_surplus_nat (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : (k : ℝ) + (n : ℝ) / 4 ≤ A) :
    n * ((n / 2) * (n / 2 + 1) / 2) <
      Fintype.card (ZeroInterpolationIndex (k - 1) (n / 2) A) := by
  rw [card_zeroInterpolationIndex]
  have hs := zero_count_surplus n k A hn hk hA
  have hd : 2 * ((n / 2) * (n / 2 + 1) / 2) ≤ (n / 2) * (n / 2 + 1) := by omega
  have h := Nat.mul_le_mul_left n hd
  nlinarith only [h, hs]

/-- Quarter-gap parameters give the finite column surplus and characteristic-compatible cap.
A local image/rank bound is still required to turn this count into an actual witness. -/
theorem zero_quarter_columns (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) :
    0 < n / 2 ∧ 2 * (n / 2) ≤ n ∧
      n * ((n / 2) * (n / 2 + 1) / 2) <
        Fintype.card (ZeroInterpolationIndex (k - 1) (n / 2) A) := by
  obtain ⟨hm, hcap, _⟩ := zero_multiplicity_bounds n hn
  exact ⟨hm, hcap, zero_count_surplus_nat n k A hn hk
    (zero_threshold_quarter delta hdelta n k A hA)⟩

end ReedSolomon.HiddenDerivative
